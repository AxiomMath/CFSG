module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.E8Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport
public import Certificates.Data.AltInsp443

public section

namespace CFSG.SectionRank.QTK.Insp443.Alt

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31

theorem mem_of_comm_of_orbit {α : Type*} {U : Subgroup (Perm α)}
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {a w : α}
    (hcover : ∀ b, b ≠ w → ∃ u ∈ U, u a = b) (hmove : ∃ u ∈ U, u a ≠ a)
    {c : Perm α} (hc : ∀ u ∈ U, c * u = u * c) : c ∈ U := by
  have hia : ∀ (f : Perm α) (x : α), f⁻¹ (f x) = x := fun f x => f.symm_apply_apply x
  have hai : ∀ (f : Perm α) (x : α), f (f⁻¹ x) = x := fun f x => f.apply_symm_apply x
  have hcu : ∀ u ∈ U, ∀ x, c (u x) = u (c x) := fun u hu x => by
    rw [← Perm.mul_apply c u, hc u hu, Perm.mul_apply]
  obtain ⟨u₀, hu₀, hu₀a⟩ : ∃ u₀ ∈ U, u₀ a = c a := by
    by_cases hca : c a = w
    · by_cases hw : ∃ u ∈ U, u a = w
      · obtain ⟨u, hu, hua⟩ := hw
        exact ⟨u, hu, hua.trans hca.symm⟩
      · exfalso
        push Not at hw
        obtain ⟨u₁, hu₁, hu₁a⟩ := hmove
        have hu₁w : u₁ w = w := by
          by_contra hne
          obtain ⟨u', hu', hu'a⟩ := hcover _ hne
          apply hw (u₁⁻¹ * u') (U.mul_mem (U.inv_mem hu₁) hu')
          rw [Perm.mul_apply, hu'a, hia]
        apply hu₁a
        apply c.injective
        rw [hcu u₁ hu₁, hca, hu₁w]
    · exact hcover _ hca
  have hne : ∀ b, b ≠ w → c b = u₀ b := fun b hb => by
    obtain ⟨u, hu, rfl⟩ := hcover b hb
    rw [hcu u hu, ← hu₀a, ← Perm.mul_apply u u₀, hU u hu u₀ hu₀, Perm.mul_apply]
  have hcu₀ : c = u₀ := by
    ext b
    by_cases hb : b = w
    · rw [hb]
      by_contra hcb
      have hb' : u₀⁻¹ (c w) ≠ w := by
        intro h
        apply hcb
        calc c w = u₀ (u₀⁻¹ (c w)) := (hai u₀ (c w)).symm
          _ = u₀ w := by rw [h]
      apply hb'
      apply c.injective
      rw [hne _ hb', hai]
    · exact hne b hb
  rw [hcu₀]
  exact hu₀

theorem exists_conj_pow {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {x : G}
    (hx : orderOf x = p) (hpi : ¬ p ∣ Nat.card G / p) {y : G} (hy : ∃ k : ℕ, y ^ p ^ k = 1) :
    ∃ g : G, ∃ m < p, g⁻¹ * y * g = x ^ m := by
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hP : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [hcardx, pow_one])
  have hPi : ¬ p ∣ (Subgroup.zpowers x).index := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [hcardx] at h
    rw [← h, Nat.mul_div_cancel_left _ hp.out.pos] at hpi
    exact hpi
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi hy
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
  refine ⟨g, m % p, Nat.mod_lt _ hp.out.pos, ?_⟩
  rw [← hx, pow_mod_orderOf, hm]

theorem exists_conj_of_sylow {G : Type*} [Group G] [Finite G] {L V : Subgroup G} {p : ℕ}
    [Fact p.Prime] {x : G} (hx : orderOf x = p) (hpi : ¬ p ∣ Nat.card G / p) {y t : G}
    (hy : y ∈ L) (hyk : ∃ k : ℕ, y ^ p ^ k = 1) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) :
    ∃ σ : G ≃* G, ∃ m < p, ∃ t₁ ∈ V.map σ.toMonoidHom,
      x ^ m ∈ L.map σ.toMonoidHom ∧ x ^ m * t₁ * (x ^ m)⁻¹ ≠ t₁ := by
  obtain ⟨g, m, hm, hgm⟩ := exists_conj_pow hx hpi hyk
  refine ⟨MulAut.conj g⁻¹, m, hm, g⁻¹ * t * g, ⟨t, ht, by simp [MulAut.conj_apply]⟩,
    ⟨y, hy, by simp [MulAut.conj_apply, hgm]⟩, ?_⟩
  rw [← hgm]
  intro he
  apply hyt
  have e1 : g⁻¹ * y * g * (g⁻¹ * t * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * t * y⁻¹) * g := by group
  rw [e1] at he
  exact mul_left_cancel (mul_right_cancel he)

variable {n : ℕ}

theorem bad_of_kConfig {L V MK : Subgroup (alternatingGroup (Fin n))}
    (h : KConfig (alternatingGroup (Fin n)) L V MK) {y t : alternatingGroup (Fin n)}
    (hy : y ∈ L) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) (p : ℕ) :
    (t : Perm (Fin n)) * t = 1 ∧ Perm.sign (t : Perm (Fin n)) = 1 ∧
      Bad p (y : Perm (Fin n)) (t : Perm (Fin n)) := by
  have ht2 : t * t = 1 := by rw [← sq]; exact h.elemAbelian.2 t ht
  refine ⟨by rw [← Subgroup.coe_mul, ht2, Subgroup.coe_one],
    Perm.mem_alternatingGroup.mp t.2, fun he => hyt (Subtype.ext ?_), fun j _ => ?_⟩
  · simpa using he
  · have hm : y ^ j * t * (y ^ j)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) j) t).mp ht
    have h1 := h.elemAbelian.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    have h2 := congrArg (fun z : V => ((z : alternatingGroup (Fin n)) : Perm (Fin n))) h1
    simpa using h2

theorem conclK_of_regular [NeZero n] (hn : n ≤ 9) {L V MK : Subgroup (alternatingGroup (Fin n))}
    (h : KConfig (alternatingGroup (Fin n)) L V MK) {y t : alternatingGroup (Fin n)}
    (hy : y ∈ L) (ht : t ∈ V) (hreg : Regular (y : Perm (Fin n)) (t : Perm (Fin n))) :
    ConclK (alternatingGroup (Fin n)) L V MK := by
  let v : Fin 3 → alternatingGroup (Fin n) := ![t, y * t * y⁻¹, y ^ 2 * t * (y ^ 2)⁻¹]
  have hvV : ∀ i, v i ∈ V := by
    intro i
    fin_cases i
    · exact ht
    · exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer hy) t).mp ht
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) 2) t).mp ht
  have hcoe : (fun i => ((v i : alternatingGroup (Fin n)) : Perm (Fin n))) =
      tri (y : Perm (Fin n)) (t : Perm (Fin n)) := by
    funext i
    fin_cases i <;> simp [v, tri]
  have hcoeE : ∀ c, ((eElt v c : alternatingGroup (Fin n)) : Perm (Fin n)) =
      eElt (tri (y : Perm (Fin n)) (t : Perm (Fin n))) c := by
    intro c
    rw [← hcoe]
    exact map_eElt (alternatingGroup (Fin n)).subtype c
  have hinj : Function.Injective
      fun c : Fin 3 → ZMod 2 => eElt (tri (y : Perm (Fin n)) (t : Perm (Fin n))) c 0 := by
    have h8 : (Finset.univ : Finset (Fin 3 → ZMod 2)).card = 8 := by rfl
    have hI := Finset.card_image_iff.mp (hreg.trans h8.symm)
    intro c d hcd
    exact hI (Finset.mem_coe.mpr (Finset.mem_univ c)) (Finset.mem_coe.mpr (Finset.mem_univ d)) hcd
  have hv : EBasis v := by
    refine ⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩
    · rw [← sq]
      exact h.elemAbelian.2 _ (hvV i)
    · exact congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨_, hvV i⟩ ⟨_, hvV j⟩)
    · apply hinj
      have h1 : ((eElt v c : alternatingGroup (Fin n)) : Perm (Fin n)) 0 = 0 := by
        rw [hc]
        rfl
      rw [hcoeE] at h1
      beta_reduce
      rw [h1, eElt_zero, Perm.one_apply]
  have hUV : eSub hv ≤ V := by
    rw [eSub_eq_closure hv, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hvV i
  have hcompl : (Finset.univ \ Finset.univ.image
      fun c : Fin 3 → ZMod 2 => eElt (tri (y : Perm (Fin n)) (t : Perm (Fin n))) c 0).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hreg]
    omega
  obtain ⟨w, hw⟩ := Finset.card_le_one_iff_subset_singleton.mp hcompl
  have hcover : ∀ b, b ≠ w → ∃ c, eElt (tri (y : Perm (Fin n)) (t : Perm (Fin n))) c 0 = b := by
    intro b hb
    by_contra hnot
    push Not at hnot
    apply hb
    refine Finset.mem_singleton.mp (hw ?_)
    simpa [Finset.mem_sdiff, Finset.mem_image] using hnot
  have hC : Subgroup.centralizer (eSub hv : Set (alternatingGroup (Fin n))) ≤ eSub hv := by
    intro c hc
    have hmem : ((c : alternatingGroup (Fin n)) : Perm (Fin n)) ∈
        (eSub hv).map (alternatingGroup (Fin n)).subtype := by
      refine mem_of_comm_of_orbit (a := 0) (w := w) ?_ ?_ ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
        simp only [Subgroup.coe_subtype]
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, eSub_comm hv u u' hu hu']
      · intro b hb
        obtain ⟨c', hc'⟩ := hcover b hb
        exact ⟨_, ⟨eElt v c', eElt_mem hv c', rfl⟩, by rw [Subgroup.coe_subtype, hcoeE, hc']⟩
      · refine ⟨_, ⟨eElt v (fun _ => 1), eElt_mem hv _, rfl⟩, ?_⟩
        rw [Subgroup.coe_subtype, hcoeE]
        intro h0
        have h1 : (fun _ => 1 : Fin 3 → ZMod 2) = 0 :=
          hinj (by beta_reduce; rw [h0, eElt_zero, Perm.one_apply])
        exact one_ne_zero (congrFun h1 0)
      · rintro _ ⟨u, hu, rfl⟩
        have h1 := Subgroup.mem_centralizer_iff.mp hc u hu
        simp only [Subgroup.coe_subtype]
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, h1]
    obtain ⟨c', hc', hcc'⟩ := hmem
    rwa [Subtype.val_injective hcc'] at hc'
  have hVC : V ≤ Subgroup.centralizer (V : Set (alternatingGroup (Fin n))) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elemAbelian.1
  have hVU : V = eSub hv :=
    le_antisymm (hVC.trans ((Subgroup.centralizer_le hUV).trans hC)) hUV
  have hU2 : IsPGroup 2 ↥(eSub hv) := IsPGroup.of_card (n := 3) (card_eSub hv)
  rw [hVU] at h ⊢
  exact KConfig.conclK_of_e8 hv h (hU2.to_le hC)

theorem coe_mk_pow (x : Perm (Fin n)) (hx : x ∈ alternatingGroup (Fin n)) (m : ℕ) :
    (((⟨x, hx⟩ : alternatingGroup (Fin n)) ^ m : alternatingGroup (Fin n)) : Perm (Fin n)) =
      x ^ m := by
  simp

theorem orderOf_mk {p : ℕ} [Fact p.Prime] {x : Perm (Fin n)} (hx : x ∈ alternatingGroup (Fin n))
    (hp : x ^ p = 1) (h1 : x ≠ 1) : orderOf (⟨x, hx⟩ : alternatingGroup (Fin n)) = p :=
  orderOf_eq_prime (Subtype.ext (by rw [coe_mk_pow]; exact hp))
    (fun h => h1 (congrArg Subtype.val h))

theorem conclK_of_altProp [NeZero n] (hA : AltProp n) (hn : n ≤ 9)
    (h57 : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (alternatingGroup (Fin n)) → p = 5 ∨ p = 7)
    (h5 : ¬ 5 ∣ Nat.card (alternatingGroup (Fin n)) / 5)
    (h7 : ¬ 7 ∣ Nat.card (alternatingGroup (Fin n)) / 7)
    {L V MK : Subgroup (alternatingGroup (Fin n))} (h : KConfig (alternatingGroup (Fin n)) L V MK) :
    ConclK (alternatingGroup (Fin n)) L V MK := by
  obtain ⟨hs5, hp5, hn5, hs7, hp7, hn7, hS⟩ := hA
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5', y, hy, hyk, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have hpd : p ∣ Nat.card (alternatingGroup (Fin n)) := by
    by_contra hpd
    apply hyt
    rw [eq_one_of_pow_of_not_dvd hp hpd hyk, one_mul, inv_one, mul_one]
  rcases h57 p hp hp5' hpd with rfl | rfl
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hmem := Perm.mem_alternatingGroup.mpr hs5
    obtain ⟨σ, m, hm, t₁, ht₁, hxL, hxt⟩ :=
      exists_conj_of_sylow (orderOf_mk hmem hp5 hn5) h5 hy hyk ht hyt
    obtain ⟨hsq, hsg, hbad⟩ := bad_of_kConfig (h.map_mulEquiv σ) hxL ht₁ hxt 5
    rw [coe_mk_pow] at hbad
    exact ((hS _ hsq hsg).1 m hm hbad).elim
  ·
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hmem := Perm.mem_alternatingGroup.mpr hs7
    obtain ⟨σ, m, hm, t₁, ht₁, hxL, hxt⟩ :=
      exists_conj_of_sylow (orderOf_mk hmem hp7 hn7) h7 hy hyk ht hyt
    have h' := h.map_mulEquiv σ
    obtain ⟨hsq, hsg, hbad⟩ := bad_of_kConfig h' hxL ht₁ hxt 7
    rw [coe_mk_pow] at hbad
    have hreg := (hS _ hsq hsg).2 m hm hbad
    rw [← coe_mk_pow _ hmem m] at hreg
    exact ConclK.of_map_mulEquiv σ h.elemAbelian h.le_normalizer
      (conclK_of_regular hn h' hxL ht₁ hreg)

end CFSG.SectionRank.QTK.Insp443.Alt

end
