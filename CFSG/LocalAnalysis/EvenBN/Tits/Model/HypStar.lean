module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Elementary
public import CFSG.LocalAnalysis.EvenBN.Tits.Setting

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin (tπ twoF4S twoF4H twoF4N twoF4P)

theorem eq_or_eq_inv_of_sq_eq {G : Type*} [Group G] {u w : G} (hu4 : u ^ 4 = 1)
    (hu2 : u ^ 2 ≠ 1) (hw : w ∈ zpowers u) (hw2 : w ^ 2 = u ^ 2) : w = u ∨ w = u⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  have hk : u ^ k = u ^ (k % 4) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 4]
    rw [zpow_add, zpow_mul, show u ^ (4 : ℤ) = 1 by exact_mod_cast hu4, one_zpow, mul_one]
  obtain ⟨r, hr, hr0, hr4⟩ : ∃ r : ℤ, k % 4 = r ∧ 0 ≤ r ∧ r < 4 :=
    ⟨_, rfl, Int.emod_nonneg k (by norm_num), Int.emod_lt_of_pos k (by norm_num)⟩
  rw [hk, hr] at hw2 ⊢
  interval_cases r
  · exfalso
    apply hu2
    simpa using hw2.symm
  · exact Or.inl (zpow_one u)
  · exfalso
    apply hu2
    rw [← hw2, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_mul]
    exact hu4
  · refine Or.inr (eq_inv_of_mul_eq_one_left ?_)
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_succ]
    exact hu4

theorem mem_normalizer_sup {G : Type*} [Group G] [Finite G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => mem_comap.2 (le_sup_left (a := A) ((mem_normalizer_iff.1 hA a).1 ha)))
      (fun b hb => mem_comap.2 (le_sup_right (a := A) ((mem_normalizer_iff.1 hB b).1 hb)))
  exact CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4 fun x hx => mem_comap.1 (hle hx)

theorem exists_conj_not_mem_zpowers_of_sq_eq_titsZ
    {u : Equiv.Perm (Fin 1755)} (huA : u ∈ titsA) (hu : u ^ 2 = titsZ) :
    ∃ c ∈ titsH, c * u * c⁻¹ ∉ zpowers u := by
  by_contra hcon
  have hall : ∀ c ∈ titsH, c * u * c⁻¹ ∈ zpowers u := fun c hc => by
    by_contra h
    exact hcon ⟨c, hc, h⟩
  have hu4 : u ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hu, sq, titsZ_mul_self]
  have hu2 : u ^ 2 ≠ 1 := hu ▸ titsZ_ne_one
  have huz : u * titsZ = titsZ * u := by
    rw [← hu]
    group
  have huH : u ∈ twoF4H := by
    rw [← centralizer_titsZ_eq]
    exact mem_inf.2 ⟨huA, mem_centralizer_singleton_iff.2 huz⟩
  have hcomm : ∀ c ∈ titsH, c * u * c⁻¹ * u⁻¹ ∈ zpowers titsZ := by
    intro c hc
    have hcz : c * titsZ * c⁻¹ = titsZ := by
      rw [mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hc), mul_inv_cancel_right]
    have hw2 : (c * u * c⁻¹) ^ 2 = u ^ 2 := by
      calc (c * u * c⁻¹) ^ 2 = c * u ^ 2 * c⁻¹ := conj_pow
        _ = u ^ 2 := by rw [hu, hcz]
    rcases eq_or_eq_inv_of_sq_eq hu4 hu2 (hall c hc) hw2 with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, ← mul_inv_rev, ← sq, hu]
      exact inv_mem (mem_zpowers _)
  have hHn : ∀ c ∈ titsH, c ∈ normalizer (zpowers u : Set (Equiv.Perm (Fin 1755))) :=
    fun c hc => CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4 fun x hx => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      rw [← conj_zpow]
      exact zpow_mem (hall c hc) k
  have hPn : twoF4H ≤ normalizer (twoF4P : Set (Equiv.Perm (Fin 1755))) := by
    have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 twoF4H
    rwa [CFSG.Quasithin.pCoreOf_twoF4H] at this
  have huP : u ∈ twoF4P := by
    have hu2g : IsPGroup 2 (zpowers u) := fun g => by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 g.2
      refine ⟨2, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, show ((2 ^ 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, hu4, one_zpow]
    have hQ2 : IsPGroup 2 (zpowers u ⊔ twoF4P : Subgroup (Equiv.Perm (Fin 1755))) :=
      IsPGroup.to_sup_of_normal_right' hu2g CFSG.Quasithin.twoF4P_isPGroup
        (zpowers_le.2 (hPn huH))
    have hQH : zpowers u ⊔ twoF4P ≤ twoF4H :=
      sup_le (zpowers_le.2 huH) CFSG.Quasithin.twoF4P_le_twoF4H
    have hπQ : tπ ∈ normalizer ((zpowers u ⊔ twoF4P : Subgroup _) :
        Set (Equiv.Perm (Fin 1755))) :=
      le_normalizer (le_sup_right (a := zpowers u) (CFSG.Quasithin.q_mem_extSub : tπ ∈ twoF4P))
    have hQn : twoF4H ≤ normalizer ((zpowers u ⊔ twoF4P : Subgroup _) :
        Set (Equiv.Perm (Fin 1755))) := by
      rintro g (hg | hg)
      · exact mem_normalizer_sup (hHn g hg) (hPn (CFSG.Quasithin.le_extSub hg))
      · have h1 := mem_normalizer_sup (hHn _ hg) (hPn (CFSG.Quasithin.le_extSub hg))
        have := mul_mem h1 hπQ
        rwa [inv_mul_cancel_right] at this
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH hQn hQ2
    rw [CFSG.Quasithin.pCoreOf_twoF4H] at this
    exact this (le_sup_left (a := zpowers u) (mem_zpowers u))
  have hJ := (pCore_twoF4H).2.2.1
  have hinv : ∀ y ∈ titsJ, u * y * u⁻¹ * y⁻¹ ∈ zpowers titsZ := fun y hy => by
    have e : u * y * u⁻¹ * y⁻¹ = (y * u * y⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hcomm y (titsJ_le_titsH hy))
  have huE : u ∈ hatE := by
    by_cases huD : u ∈ titsD
    · rw [tits_vertex_hatE.1]
      exact ⟨hJ ▸ mem_inf.2 ⟨huP, huD⟩, hinv⟩
    · rw [twoF4_vertex.1]
      refine ⟨huP, fun y hy => ?_⟩
      by_cases hyD : y ∈ titsD
      · exact hinv y (hJ ▸ mem_inf.2 ⟨hy, hyD⟩)
      · have hj : y * u⁻¹ ∈ titsJ := hJ ▸ mem_inf.2 ⟨mul_mem hy (inv_mem huP),
          mul_inv_mem_titsD (twoF4P_le_titsA hy) huA hyD huD⟩
        have e : u * y * u⁻¹ * y⁻¹ = u * (y * u⁻¹) * u⁻¹ * (y * u⁻¹)⁻¹ := by group
        rw [e]
        exact hinv _ hj
  exact hu2 (by rw [sq]; exact twoF4_vertex.2.1 u huE)

@[expose] def ShortStarEscape : Prop :=
  ∀ u ∈ titsA, u ^ 2 = titsTInv →
    ∃ c ∈ titsD, c * titsTInv = titsTInv * c ∧ c * u * c⁻¹ ∉ zpowers u

theorem exists_conj_not_mem_zpowers_of_sq
    (ht : ShortStarEscape) {x u : Equiv.Perm (Fin 1755)} (hxA : x ∈ titsA)
    (hx : orderOf x = 2) (huA : u ∈ titsA) (hu : u ^ 2 = x) :
    ∃ c ∈ titsD, c * x = x * c ∧ c * u * c⁻¹ ∉ zpowers u := by
  obtain ⟨-, d, hd, hdx⟩ := titsA_involution_conj hxA hx
  have hdA : d ∈ titsA := titsD_le_titsA hd
  have hu'A : d⁻¹ * u * d ∈ titsA := mul_mem (mul_mem (inv_mem hdA) huA) hdA
  have key : ∀ y : Equiv.Perm (Fin 1755), d * y * d⁻¹ = x →
      (∃ c ∈ titsD, c * y = y * c ∧ c * (d⁻¹ * u * d) * c⁻¹ ∉ zpowers (d⁻¹ * u * d)) →
      ∃ c ∈ titsD, c * x = x * c ∧ c * u * c⁻¹ ∉ zpowers u := by
    rintro y rfl ⟨c, hc, hcy, hcu⟩
    refine ⟨d * c * d⁻¹, mul_mem (mul_mem hd hc) (inv_mem hd), ?_, fun hmem => hcu ?_⟩
    · calc d * c * d⁻¹ * (d * y * d⁻¹) = d * (c * y) * d⁻¹ := by group
        _ = d * (y * c) * d⁻¹ := by rw [hcy]
        _ = d * y * d⁻¹ * (d * c * d⁻¹) := by group
    · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have h1 : (d⁻¹ * u * d) ^ k = d⁻¹ * u ^ k * d := by
        have := conj_zpow (i := k) (a := d⁻¹) (b := u)
        rwa [inv_inv] at this
      rw [h1, hk]
      group
  have hsq : ∀ y, d * y * d⁻¹ = x → (d⁻¹ * u * d) ^ 2 = y := fun y hy => by
    have := conj_pow (i := 2) (a := d⁻¹) (b := u)
    rw [inv_inv] at this
    rw [this, hu, ← hy]
    group
  rcases hdx with h | h
  · refine key titsZ h ?_
    obtain ⟨c, hcH, hc⟩ := exists_conj_not_mem_zpowers_of_sq_eq_titsZ hu'A (hsq _ h)
    exact ⟨c, titsH_le_titsD hcH, mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hcH),
      hc⟩
  · exact key titsTInv h (ht _ hu'A (hsq _ h))

theorem hypothesisOneStar_of_shortStarEscape
    (ht : ShortStarEscape) : CFSG.SeitzReduction.RankOne.HypothesisOneStar titsD := by
  intro x u hx hux E hEC hEodd hEu hEc
  have hconj : ∀ d : titsD, MulAut.conj d = titsConjEquiv ⟨d, titsD_le_titsA d.2⟩ := fun d =>
    MulEquiv.ext fun e => Subtype.ext rfl
  set a := titsConjEquiv.symm x with ha
  set b := titsConjEquiv.symm u with hb
  have hxa : titsConjEquiv a = x := titsConjEquiv.apply_symm_apply x
  have hub : titsConjEquiv b = u := titsConjEquiv.apply_symm_apply u
  have ha2 : orderOf (a : Equiv.Perm (Fin 1755)) = 2 := by
    rw [Subgroup.orderOf_coe, ha, MulEquiv.orderOf_eq, hx]
  have hb2 : (b : Equiv.Perm (Fin 1755)) ^ 2 = a := by
    rw [← Subgroup.coe_pow, hb, ha, ← map_pow, hux]
  have haD : (a : Equiv.Perm (Fin 1755)) ∈ titsD := titsA_involution_mem_D a.2 ha2
  have hE : ∀ e ∈ E, e = 1 := by
    intro e he
    set ê := titsConjEquiv.symm e with hê
    have hφê : titsConjEquiv ê = e := titsConjEquiv.apply_symm_apply e
    have hodd : Odd (orderOf (ê : Equiv.Perm (Fin 1755))) := by
      rw [Subgroup.orderOf_coe, hê, MulEquiv.orderOf_eq]
      exact Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E he)
    have hêD : (ê : Equiv.Perm (Fin 1755)) ∈ titsD := by
      obtain ⟨m, hm⟩ := hodd
      have h1 : (ê : Equiv.Perm (Fin 1755)) =
          (ê : Equiv.Perm (Fin 1755)) ^ (m + 1) * (ê : Equiv.Perm (Fin 1755)) ^ (m + 1) := by
        rw [← pow_add, show m + 1 + (m + 1) = orderOf (ê : Equiv.Perm (Fin 1755)) + 1 by omega,
          pow_succ, pow_orderOf_eq_one, one_mul]
      rw [h1]
      exact mul_self_mem_titsD (pow_mem ê.2 _)
    have hêa : (ê : Equiv.Perm (Fin 1755)) * a = a * ê := by
      have h1 : ê * a = a * ê := by
        apply titsConjEquiv.injective
        rw [map_mul, map_mul, hφê, hxa]
        exact mem_centralizer_singleton_iff.1 (hEC he)
      exact congrArg (fun y : titsA => (y : Equiv.Perm (Fin 1755))) h1
    set a₀ : titsD := ⟨a, haD⟩ with ha₀def
    have ha₀ : orderOf a₀ = 2 := by rw [← Subgroup.orderOf_coe]; exact ha2
    have hx0 : x = MulAut.conj a₀ := by
      rw [hconj, ← hxa]
    let ψ : centralizer ({a₀} : Set titsD) →* MulAut titsD :=
      MulAut.conj.comp (centralizer ({a₀} : Set titsD)).subtype
    have hψ : ∀ g, ψ g = MulAut.conj (g : titsD) := fun _ => rfl
    have hRn : (E.comap ψ).Normal := ⟨fun r hr g => by
      rw [mem_comap, map_mul, map_mul, map_inv]
      refine hEc (g : titsD) ?_ _ hr
      rw [hx0, ← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 g.2)]⟩
    have hψinj : Function.Injective ψ := by
      intro g₁ g₂ h
      rw [hψ, hψ, hconj, hconj] at h
      have h2 : ((g₁ : titsD) : Equiv.Perm (Fin 1755)) = (g₂ : titsD) :=
        congrArg (fun y : titsA => (y : Equiv.Perm (Fin 1755))) (titsConjEquiv.injective h)
      exact Subtype.ext (Subtype.ext h2)
    have hRodd : Odd (Nat.card (E.comap ψ)) := by
      have h1 : Nat.card ((E.comap ψ).map ψ) = Nat.card (E.comap ψ) :=
        card_map_of_injective hψinj
      exact Odd.of_dvd_nat hEodd (h1 ▸ card_dvd_of_le (map_comap_le ψ E))
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hodd⟩ :=
      CTUC_Tits_two_involution_classes_and_centralizer_two_kernels
    have hR := hodd a₀ ha₀ (E.comap ψ) hRn hRodd
    have hêR : (⟨⟨ê, hêD⟩, mem_centralizer_singleton_iff.2 (Subtype.ext hêa)⟩ :
        centralizer ({a₀} : Set titsD)) ∈ E.comap ψ := by
      rw [mem_comap, hψ, hconj]
      exact hφê ▸ he
    rw [hR, mem_bot] at hêR
    have hê1 : ê = 1 := Subtype.ext (congrArg (fun g : centralizer ({a₀} : Set titsD) =>
      ((g : titsD) : Equiv.Perm (Fin 1755))) hêR)
    rw [← hφê, hê1, map_one]
  obtain ⟨c, hcD, hca, hcb⟩ := exists_conj_not_mem_zpowers_of_sq ht a.2 ha2 b.2 hb2
  have hcc : MulAut.conj (⟨c, hcD⟩ : titsD) = titsConjEquiv ⟨c, titsD_le_titsA hcD⟩ := hconj _
  refine ⟨⟨c, hcD⟩, ?_, ?_⟩
  · rw [hcc, ← hxa, ← map_mul, ← map_mul]
    exact congrArg titsConjEquiv (Subtype.ext hca)
  · have hEb : E = ⊥ := (eq_bot_iff_forall E).2 hE
    rw [hEb, bot_sup_eq]
    intro hmem
    apply hcb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [hcc, ← hub, ← map_zpow, ← map_inv, ← map_mul, ← map_mul] at hk
    have := congrArg Subtype.val (titsConjEquiv.injective hk)
    simpa using this

theorem kernel_eq_zpowers_of_shortStarEscape
    {G : Type} [Group G] [Finite G] {d : Data G} (hd : d.Hyp) (ht : ShortStarEscape) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) = zpowers d.t :=
  hd.kernel_eq_zpowers (hypothesisOneStar_of_shortStarEscape ht)

end CFSG.LocalAnalysis.EvenBN.Tits.Model
