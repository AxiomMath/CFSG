module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapEdgeChains
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)

theorem ordF4_two_eq : CFSG.Open.ordF4 2 = 2 ^ 24 * 197358525 := by
  norm_num [CFSG.Open.ordF4]

theorem not_sq_card_titsD_dvd_ordF4_two : ¬ 17971200 * 17971200 ∣ CFSG.Open.ordF4 2 := by
  rw [ordF4_two_eq]
  decide

theorem two_pow_eleven_dvd_card_titsD : 2 ^ 11 ∣ (17971200 : ℕ) := ⟨8775, by norm_num⟩

variable {K : Type} [Field K]

theorem factorization_two_mul_card_mulAut_F4_two [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) :
    (2 * Nat.card (MulAut (adjointGroup .F4 K))).factorization 2 = 26 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  rw [card_mulAut_F4 le_rfl K hK', CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK,
    ordF4_two_eq, show 2 * (2 ^ 24 * 197358525 * (2 * 1)) = 2 ^ 26 * 197358525 by norm_num,
    Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by positivity) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by decide)]

theorem twenty_le_factorization_card_fixedSubgroup_F4_two [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {w : adjointGroup .F4 K} (hθ : MulAut.conj w * MulAut.conj w = 1)
    (hθ1 : MulAut.conj w ≠ 1) :
    20 ≤ (Nat.card (fixedSubgroup (MulAut.conj w))).factorization 2 := by
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL Tag.F4 K) := finite_modGL
    infer_instance
  have hZ := center_adjointGroup_eq_bot_field .F4 K
  have hw2 : w * w = 1 := by
    have h1 : MulAut.conj (w * w) = 1 := by rw [map_mul]; exact hθ
    have hc : w * w ∈ center (adjointGroup .F4 K) := by
      rw [mem_center_iff]
      intro g
      have h2 : w * w * g * (w * w)⁻¹ = g := by
        have := congrArg (fun φ : MulAut (adjointGroup .F4 K) => φ g) h1
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * (w * w) = w * w * g * (w * w)⁻¹ * (w * w) := by rw [h2]
        _ = w * w * g := by group
    rw [hZ, mem_bot] at hc
    exact hc
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hθ1 (map_one _)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hdvd := ClassReps.pow_twenty_dvd_card_centralizer hwo
  rw [hK] at hdvd
  rw [E8Pilot.fixedSubgroup_conj_eq_centralizer]
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd

section Tits

open CFSG.Sporadic.Schreier.Tits in
theorem exists_perfect_le_reeFixed_card_eq [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) :
    ∃ Γ' : Subgroup (adjointGroup .F4 K), Γ' ≤ reeFixed ReeTag.F4 K 0 ∧ ⁅Γ', Γ'⁆ = Γ' ∧
      Nat.card Γ' = 17971200 := by
  have : Fact (Nat.card K = 2) := ⟨hK⟩
  set R := reeFixed ReeTag.F4 K 0 with hRdef
  have hS : Group.IsPerfect (commutator R) := by
    have := commutator_reeFixed_simple (K := K) hK
    refine isPerfect_of_isSimpleGroup_of_exists_ne ?_
    by_contra! hcomm
    have hZ : center (commutator R) = ⊤ :=
      eq_top_iff.2 fun z _ => mem_center_iff.2 fun g => hcomm g z
    rw [center_commutator_reeFixed hK] at hZ
    obtain ⟨u, v, huv⟩ := exists_pair_ne (commutator R)
    have hu : u ∈ (⊥ : Subgroup (commutator R)) := hZ ▸ mem_top u
    have hv : v ∈ (⊥ : Subgroup (commutator R)) := hZ ▸ mem_top v
    rw [mem_bot] at hu hv
    exact huv (hu.trans hv.symm)
  refine ⟨(commutator R).map R.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact g.2
  · have := Group.IsPerfect.map (H := commutator R) R.subtype
    exact Subgroup.commutator_eq_self (H := (commutator R).map R.subtype)
  · have h1 : Nat.card (commutator R) = 17971200 := by
      rw [Nat.card_congr (titsDerivedIso (K := K)).toEquiv, card_titsD]
    exact (Nat.card_congr ((commutator R).equivMapOfInjective R.subtype
      R.subtype_injective).toEquiv).symm.trans h1

theorem card_titsD_dvd_card_perfectCore_fixedSubgroup_F4_two [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2) {θ : MulAut (adjointGroup .F4 K)}
    (hθ : θ * θ = 1)
    (hθo : θ ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range) :
    17971200 ∣ Nat.card (perfectCore (fixedSubgroup θ)) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have hθ2 : θ ^ 2 = 1 := by rw [sq]; exact hθ
  obtain ⟨ψ, -, -, hodd, hfix, -⟩ :=
    even_F4_all_outer_involutions_canonical (f := 1) le_rfl K hK' θ hθ2 hθo
  obtain ⟨hree, -⟩ := hodd 0 rfl
  have hΓ : (ReeTag.F4.finiteExceptionalAut K ^ 1).toMonoidHom.eqLocus (MonoidHom.id _) =
      reeFixed ReeTag.F4 K 0 := by
    rw [hree, CFSG.LieType.Ree.ReeTag.finiteReeAut_eq_reeAut]
    rfl
  let ψ' : MulAut (adjointGroup .F4 K) := ψ
  have hmap : (fixedSubgroup θ).map ψ'.toMonoidHom = reeFixed ReeTag.F4 K 0 := hfix.trans hΓ
  obtain ⟨Γ', hΓ'le, hperf, hcard⟩ := exists_perfect_le_reeFixed_card_eq hK
  set Q : Subgroup (adjointGroup .F4 K) := Γ'.map ψ'.symm.toMonoidHom with hQdef
  have hQle : Q ≤ fixedSubgroup θ := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ (fixedSubgroup θ).map ψ'.toMonoidHom := hmap ▸ hΓ'le hg
    obtain ⟨h, hh, rfl⟩ := hg'
    change ψ'.symm (ψ' h) ∈ fixedSubgroup θ
    rw [MulEquiv.symm_apply_apply]
    exact hh
  have hQperf : ⁅Q, Q⁆ = Q := by rw [hQdef, ← map_commutator, hperf]
  have hQ : Q ≤ perfectCore (fixedSubgroup θ) := le_perfectCore_of_perfect hQle hQperf
  have hQcard : Nat.card Q = 17971200 := by
    rw [hQdef, card_map_of_injective ψ'.symm.injective, hcard]
  rw [← hQcard]
  exact Subgroup.card_dvd_of_le hQ

theorem eleven_le_factorization_card_fixedSubgroup_F4_two [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) {θ : MulAut (adjointGroup .F4 K)} (hθ : θ * θ = 1)
    (hθo : θ ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range) :
    11 ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := by
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL Tag.F4 K) := finite_modGL
    infer_instance
  have h1 := card_titsD_dvd_card_perfectCore_fixedSubgroup_F4_two hK hθ hθo
  have h2 : 2 ^ 11 ∣ Nat.card (fixedSubgroup θ) :=
    two_pow_eleven_dvd_card_titsD.trans (h1.trans (Subgroup.card_dvd_of_le (perfectCore_le _)))
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2

theorem swapPairExclusion_adjointGroup_F4_two [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) : SeitzQ2.SwapPairExclusion (adjointGroup .F4 K) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  intro θ θ' hθ hθ1 hθ' hθ'1 h2 hdvd
  have hA := factorization_two_mul_card_mulAut_F4_two hK
  rw [hA] at h2
  by_cases hi : θ ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range
  · obtain ⟨w, rfl⟩ := hi
    have h1 := twenty_le_factorization_card_fixedSubgroup_F4_two hK hθ hθ1
    by_cases hi' : θ' ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range
    · obtain ⟨w', rfl⟩ := hi'
      have h1' := twenty_le_factorization_card_fixedSubgroup_F4_two hK hθ' hθ'1
      omega
    · have h1' := eleven_le_factorization_card_fixedSubgroup_F4_two hK hθ' hi'
      omega
  · have h1 := eleven_le_factorization_card_fixedSubgroup_F4_two hK hθ hi
    by_cases hi' : θ' ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range
    · obtain ⟨w', rfl⟩ := hi'
      have h1' := twenty_le_factorization_card_fixedSubgroup_F4_two hK hθ' hθ'1
      omega
    · have d1 := card_titsD_dvd_card_perfectCore_fixedSubgroup_F4_two hK hθ hi
      have d2 := card_titsD_dvd_card_perfectCore_fixedSubgroup_F4_two hK hθ' hi'
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK] at hdvd
      exact not_sq_card_titsD_dvd_ordF4_two ((mul_dvd_mul d1 d2).trans hdvd)

theorem twoF4SwapPairExclusionInput_holds : TwoF4SwapPairExclusionInput :=
  fun _ _ _ _ hK => swapPairExclusion_adjointGroup_F4_two hK

theorem twoSwapPairInput_of_chainInput'
    (h : TwoSwapChainInput) : TwoSwapPairInput :=
  twoSwapPairInput_of_chainInput h twoF4SwapPairExclusionInput_holds

end Tits

end CFSG.SeitzReduction.F4Pilot
