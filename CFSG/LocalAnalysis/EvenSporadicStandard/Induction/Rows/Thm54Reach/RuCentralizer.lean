module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzPair

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.RuStd CFSG.EvenSporadicStandard.Induction.RuSz

theorem le_of_isPerfect_of_comm_quotient {G : Type*} [Group G] {K X : Subgroup G} [K.Normal]
    (hcomm : ∀ a b : G ⧸ K, a * b = b * a) (hX : Group.IsPerfect ↥X) : X ≤ K := by
  haveI : IsMulCommutative (G ⧸ K) := IsMulCommutative.of_comm hcomm
  have hle : _root_.commutator G ≤ K :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := G) (N := K)).mp inferInstance
  haveI : Group.IsPerfect ↥X := hX
  calc X = ⁅X, X⁆ := (Subgroup.commutator_eq_self (H := X)).symm
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ = _root_.commutator G := rfl
    _ ≤ K := hle

section Ru


theorem card_eq_of_perfect_centralizer_ru {R : Type} [Group R] (hR : IsSporadic R .Ru) {u : R}
    (hu : orderOf u = 2) {X : Subgroup R} (hX : Group.IsPerfect ↥X)
    (hXu : ∀ x ∈ X, x * u = u * x) (hdvd : 29120 ∣ Nat.card ↥X) : Nat.card ↥X = 29120 := by
  have hF := ruFacts_of_isSporadic hR
  have hdvdC : 29120 ∣ Nat.card (centralizer ({u} : Set R)) :=
    hdvd.trans (Subgroup.card_dvd_of_le fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.2 (hXu k hk))
  have hcu : Nat.card (centralizer ({u} : Set R)) = 116480 := by
    rcases hF.card_centralizer u hu with h | h
    · exfalso
      rw [h] at hdvdC
      omega
    · exact h
  obtain ⟨e, he⟩ := exists_std_equiv hR hu hcu
  have hXmapL : X.map (emb e) ≤ ruL := by
    rintro _ ⟨x, hx, rfl⟩
    exact emb_conj_mem he (hXu x hx)
  haveI : Group.IsPerfect ↥X := hX
  have hXmap_perf : Group.IsPerfect ↥(X.map (emb e)) :=
    Group.IsPerfect.ofSurjective
      (f := (X.equivMapOfInjective (emb e) (emb_injective e)).toMonoidHom)
      (X.equivMapOfInjective (emb e) (emb_injective e)).surjective
  haveI := hXmap_perf
  have hXruL_perf : Group.IsPerfect ↥((X.map (emb e)).subgroupOf ruL) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hXmapL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXmapL).symm.surjective
  haveI : (K0.subgroupOf ruL).Normal := K0_normal
  have hcardK0sub : Nat.card (K0.subgroupOf ruL) = 29120 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe K0_le_L).toEquiv, card_K0]
  have hcardQ : Nat.card (↥ruL ⧸ K0.subgroupOf ruL) = 2 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (K0.subgroupOf ruL)
    rw [card_ruL_eq, hcardK0sub, card_K0] at h
    have h4 : Nat.card (↥ruL ⧸ K0.subgroupOf ruL) = 4 :=
      (Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 29120) h).symm
    rw [h4]
    norm_num
  haveI : IsMulCommutative (↥ruL ⧸ K0.subgroupOf ruL) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcardQ
  have hXruL_le : (X.map (emb e)).subgroupOf ruL ≤ K0.subgroupOf ruL :=
    le_of_isPerfect_of_comm_quotient (fun a b => mul_comm' a b) hXruL_perf
  have hmapK0 : X.map (emb e) ≤ K0 := by
    intro x hx
    have hxL : x ∈ ruL := hXmapL hx
    exact hXruL_le (show (⟨x, hxL⟩ : ↥ruL) ∈ (X.map (emb e)).subgroupOf ruL from hx)
  have hdiv : Nat.card ↥X ∣ 29120 := by
    have h1 : Nat.card (X.map (emb e)) ∣ Nat.card K0 := Subgroup.card_dvd_of_le hmapK0
    rw [card_K0] at h1
    rwa [Subgroup.card_map_of_injective (emb_injective e)] at h1
  exact (Nat.dvd_antisymm hdvd hdiv).symm

end Ru

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
