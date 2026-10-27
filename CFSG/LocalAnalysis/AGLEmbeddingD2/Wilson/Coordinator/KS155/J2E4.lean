module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Model
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.KS155Generic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofCasesB

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

set_option linter.unusedSectionVars false

theorem map_centralizer_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (S : Subgroup X) :
    (centralizer (S : Set X)).map e.toMonoidHom =
      centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  ext y
  simp only [mem_map, mem_centralizer_iff, MulEquiv.coe_toMonoidHom, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hx s hs]
  · intro hy
    refine ⟨e.symm y, fun s hs => e.injective ?_, e.apply_symm_apply y⟩
    rw [map_mul, map_mul, e.apply_symm_apply, hy (e s) ⟨s, hs, rfl⟩]

noncomputable def centralizerMapEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (S : Subgroup X) :
    centralizer (S : Set X) ≃* centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) :=
  ((centralizer (S : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_mulEquiv e S))

section Model


theorem E0_le_centralizer : E0 ≤ centralizer (E0 : Set GJ) := by
  rw [centralizer_E0_eq]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have c12 : Commute e1J e2J := e1_comm_e2
  rcases hy with rfl | hy
  · rcases hx with rfl | rfl | rfl | rfl
    · simp
    · rfl
    · exact c12.eq
    · exact ((Commute.refl e1J).mul_right c12).eq
  · rw [Set.mem_singleton_iff.1 hy]
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact c12.symm.eq
    · rfl
    · exact (c12.symm.mul_right (Commute.refl e2J)).eq

theorem nonempty_centralizer_E0_equiv :
    Nonempty (centralizer (E0 : Set GJ) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) := by
  have hEC : E0 ≤ centralizer (E0 : Set GJ) := E0_le_centralizer
  have hDC : DJ ≤ centralizer (E0 : Set GJ) := DJ_le
  have hA : E0.subgroupOf (centralizer (E0 : Set GJ)) ≤ center (centralizer (E0 : Set GJ)) := by
    intro x hx
    rw [mem_center_iff]
    intro y
    have hx' : ((x : centralizer (E0 : Set GJ)) : GJ) ∈ E0 := mem_subgroupOf.1 hx
    exact Subtype.ext (mem_centralizer_iff.1 y.2 _ hx').symm
  have hAB : Disjoint (E0.subgroupOf (centralizer (E0 : Set GJ)))
      (DJ.subgroupOf (centralizer (E0 : Set GJ))) := by
    rw [Subgroup.disjoint_def]
    intro x h1 h2
    exact Subtype.ext (Subgroup.disjoint_def.1 disjoint_E0_DJ (mem_subgroupOf.1 h1)
      (mem_subgroupOf.1 h2))
  have hcA : Nat.card (E0.subgroupOf (centralizer (E0 : Set GJ))) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv, card_E0]
  have hcB : Nat.card (DJ.subgroupOf (centralizer (E0 : Set GJ))) = 60 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv, card_DJ]
  have hcC : Nat.card (centralizer (E0 : Set GJ)) = 240 := by
    rw [centralizer_E0_eq, card_centralizer_E0]
  obtain ⟨φ⟩ := Proving.nonempty_mulEquiv_prod_of_le_center hA hAB (by rw [hcA, hcB, hcC])
  obtain ⟨ψA⟩ := Proving.nonempty_mulEquiv_klein hcA fun x => by
    have hx : ((x : centralizer (E0 : Set GJ)) : GJ) ∈ E0 := mem_subgroupOf.1 x.2
    apply Subtype.ext
    apply Subtype.ext
    simp only [OneMemClass.coe_one, pow_two]
    exact mul_self_of_mem_kleinSub hx
  have hperf : Group.IsPerfect (DJ.subgroupOf (centralizer (E0 : Set GJ))) := by
    have := DJ_perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hDC).symm.toMonoidHom)
      (subgroupOfEquivOfLe hDC).symm.surjective
  obtain ⟨ψB⟩ := CFSG.Quasithin.A312J2.nonempty_mulEquiv_alt5_of_perfect hperf hcB
  exact ⟨φ.trans (MulEquiv.prodCongr ψA ψB)⟩

theorem prime_dvd_card_GJ {r : ℕ} (hr : r.Prime) (h : r ∣ Nat.card GJ) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  rw [card_GJ, show (604800 : ℕ) = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 by norm_num] at h
  have hq : ∀ q : ℕ, q.Prime → ∀ k, r ∣ q ^ k → r = q := fun q hq k hk =>
    (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow hk)
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h7
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h5
    · rcases (Nat.Prime.dvd_mul hr).1 h with h2 | h3
      · exact Or.inl (hq 2 Nat.prime_two 7 h2)
      · exact Or.inr (Or.inl (hq 3 Nat.prime_three 3 h3))
    · exact Or.inr (Or.inr (Or.inl (hq 5 (by norm_num) 2 h5)))
  · exact Or.inr (Or.inr (Or.inr (hq 7 (by norm_num) 1 (by simpa using h7))))

theorem mem_map_conj_inv {E : Subgroup GJ} {k y : GJ} :
    y ∈ E.map (MulAut.conj k⁻¹).toMonoidHom ↔ k * y * k⁻¹ ∈ E := by
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨k * y * k⁻¹, h, by group⟩

theorem exists_conj_E0 {E : Subgroup GJ} (h4 : Nat.card E = 4) {K : Subgroup GJ} (hK : K ≠ ⊥)
    (hKp : Group.IsPerfect K) (hKE : K ≤ centralizer (E : Set GJ)) :
    ∃ m : GJ, E.map (MulAut.conj m).toMonoidHom = E0 := by
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hK
  have hns := Proving.not_isSolvable_of_isPerfect (K := K)
  obtain ⟨r, hr, hrK, hr2, hr3⟩ :=
    Proving.exists_third_prime_dvd_card_of_not_isSolvable hns Nat.prime_two Nat.prime_three
  have : Fact r.Prime := ⟨hr⟩
  have hrG : r ∣ Nat.card GJ := hrK.trans (Subgroup.card_subgroup_dvd_card K)
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' r hrK
  have hfo : orderOf (f : GJ) = r := by rw [Subgroup.orderOf_coe]; exact hf
  have hEf : E ≤ centralizer ({(f : GJ)} : Set GJ) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 (hKE f.2) x hx
  have h4C : 4 ∣ Nat.card (centralizer ({(f : GJ)} : Set GJ)) := by
    rw [← h4]
    exact Subgroup.card_dvd_of_le hEf
  rcases prime_dvd_card_GJ hr hrG with rfl | rfl | rfl | rfl
  · exact absurd rfl hr2
  · exact absurd rfl hr3
  ·
    obtain ⟨k, c, hc, e, he0, he5, hfk⟩ := exists_conj_case hfo
    set E' := E.map (MulAut.conj k⁻¹).toMonoidHom with hE'
    have hE'card : Nat.card E' = 4 := by
      rw [hE', Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, h4]
    have hE'C : E' ≤ centralizer ({caseJ c} : Set GJ) := by
      rw [← centralizer_caseJ_pow hc he0 he5]
      intro y hy
      rw [mem_map_conj_inv] at hy
      have hcomm := mem_centralizer_singleton_iff.1 (hEf hy)
      rw [mem_centralizer_singleton_iff]
      rw [hfk] at hcomm
      calc y * caseJ c ^ e = k⁻¹ * ((k * y * k⁻¹) * (k * caseJ c ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * caseJ c ^ e * k⁻¹) * (k * y * k⁻¹)) * k := by rw [hcomm]
        _ = caseJ c ^ e * y := by group
    have h4c : 4 ∣ Nat.card (centralizer ({caseJ c} : Set GJ)) := by
      rw [← hE'card]
      exact Subgroup.card_dvd_of_le hE'C
    have hc0 : c = 0 := by
      by_contra hc0
      have hc1 : c = 1 := by omega
      have hx : caseJ c = x5cJ := by simp [caseJ, hc0]
      rw [hx, card_centralizer_x5c] at h4c
      norm_num at h4c
    have hx : caseJ c = x5aJ := by simp [caseJ, hc0]
    rw [hx] at hE'C
    have hA : Nat.card (E'.subgroupOf (centralizer ({x5aJ} : Set GJ))) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hE'C).toEquiv, hE'card]
    have hB : Nat.card (E0.subgroupOf (centralizer ({x5aJ} : Set GJ))) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe E0_le_centralizer_x5a).toEquiv, card_E0]
    obtain ⟨h, hh⟩ := Proving.exists_conj_eq_of_card_eq_four
      (by rw [card_centralizer_x5a]; norm_num) hA hB
    refine ⟨(h : GJ) * k⁻¹, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyE' : k⁻¹ * y * k ∈ E' := by
        rw [mem_map_conj_inv]
        simpa [mul_assoc] using hy
      have hmem : (MulAut.conj h).toMonoidHom ⟨k⁻¹ * y * k, hE'C hyE'⟩ ∈
          E0.subgroupOf (centralizer ({x5aJ} : Set GJ)) := by
        rw [← hh]
        exact ⟨⟨k⁻¹ * y * k, hE'C hyE'⟩, mem_subgroupOf.2 hyE', rfl⟩
      rw [mem_subgroupOf] at hmem
      simpa [MulAut.conj_apply, mul_assoc] using hmem
    · intro hx0
      have hx0' : (⟨x, E0_le_centralizer_x5a hx0⟩ : centralizer ({x5aJ} : Set GJ)) ∈
          E0.subgroupOf (centralizer ({x5aJ} : Set GJ)) := mem_subgroupOf.2 hx0
      rw [← hh] at hx0'
      obtain ⟨⟨y, hyC⟩, hy, hyx⟩ := hx0'
      replace hy : y ∈ E' := mem_subgroupOf.1 (SetLike.mem_coe.1 hy)
      have hyx' : (h : GJ) * y * (h : GJ)⁻¹ = x := by
        have := congrArg Subtype.val hyx
        simpa [MulAut.conj_apply] using this
      rw [mem_map_conj_inv] at hy
      refine ⟨k * y * k⁻¹, hy, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hyx']
      group
  ·
    have hle := card_centralizer_le_of_orderOf_seven hfo
    have h7 : 7 ∣ Nat.card (centralizer ({(f : GJ)} : Set GJ)) := by
      rw [← hfo, ← Nat.card_zpowers]
      apply Subgroup.card_dvd_of_le
      rw [zpowers_le, mem_centralizer_singleton_iff]
    have hpos : 0 < Nat.card (centralizer ({(f : GJ)} : Set GJ)) := Nat.card_pos
    have h7' : Nat.card (centralizer ({(f : GJ)} : Set GJ)) = 7 := by
      obtain ⟨m, hm⟩ := h7
      rcases m with _ | _ | m
      · omega
      · omega
      · omega
    rw [h7'] at h4C
    norm_num at h4C

theorem nonempty_centralizer_equiv_GJ {E : Subgroup GJ} (h4 : Nat.card E = 4) {K : Subgroup GJ}
    (hK : K ≠ ⊥) (hKp : Group.IsPerfect K) (hKE : K ≤ centralizer (E : Set GJ)) :
    Nonempty (centralizer (E : Set GJ) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) := by
  obtain ⟨m, hm⟩ := exists_conj_E0 h4 hK hKp hKE
  obtain ⟨ψ⟩ := nonempty_centralizer_E0_equiv
  exact ⟨((centralizerMapEquiv (MulAut.conj m) E).trans (MulEquiv.subgroupCongr (by rw [hm]))).trans
    ψ⟩

end Model

theorem ks155J2CentE4 :
    CFSG.RankThree.PartTwo.Sec15.KS155J2CentE4 := by
  intro X _ ⟨e⟩ E h4 _ ⟨K, hK, hKp, hKE⟩
  let φ : X ≃* GJ := e.trans nativeEquivP
  have h4' : Nat.card (E.map φ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective φ.injective, h4]
  have hK' : K.map φ.toMonoidHom ≠ ⊥ := by
    intro h
    apply hK
    rw [eq_bot_iff]
    intro x hx
    have : φ x ∈ K.map φ.toMonoidHom := ⟨x, hx, rfl⟩
    rw [h, mem_bot] at this
    rw [mem_bot]
    exact φ.injective (this.trans (map_one φ).symm)
  have hKp' : Group.IsPerfect (K.map φ.toMonoidHom) := Group.IsPerfect.map φ.toMonoidHom
  have hKE' : K.map φ.toMonoidHom ≤ centralizer ((E.map φ.toMonoidHom : Subgroup GJ) : Set GJ) := by
    rw [← map_centralizer_mulEquiv φ E]
    exact Subgroup.map_mono hKE
  obtain ⟨ψ⟩ := nonempty_centralizer_equiv_GJ h4' hK' hKp' hKE'
  exact ⟨(centralizerMapEquiv φ E).trans ψ⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155
