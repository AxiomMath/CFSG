module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ZStar
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.Generic.S3

open CFSG Subgroup
open scoped commutatorElement

section Glauberman

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_normal_of_isolated {Y : Subgroup G} {t : G} (htY : t ∈ Y) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hiso : ∀ h ∈ Y, (h * t * h⁻¹) * t = t * (h * t * h⁻¹) → h * t * h⁻¹ = t) :
    ∃ N : Subgroup G, N ≤ Y ∧ (∀ h ∈ Y, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧ Odd (Nat.card N) ∧
      ∀ h ∈ Y, h * t * h⁻¹ * t⁻¹ ∈ N := by
  classical
  let _ : Fintype ↥Y := Fintype.ofFinite ↥Y
  let t' : ↥Y := ⟨t, htY⟩
  have ht2' : t' * t' = 1 := Subtype.ext ht2
  have ht1' : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨N', hN'n, hN'odd, hN'⟩ := CFSG.ZStar.glauberman_zStar ↥Y t' ht1' ht2' (fun g hg => by
    have := hiso g g.2 (by simpa using congrArg Subtype.val hg)
    exact Subtype.ext this)
  refine ⟨N'.map Y.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨n, -, rfl⟩
    exact n.2
  · rintro h hh _ ⟨n, hn, rfl⟩
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hN'n.conj_mem n hn ⟨h, hh⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hN'odd
  · intro h hh
    exact ⟨⟨h, hh⟩ * t' * ⟨h, hh⟩⁻¹ * t'⁻¹, hN' ⟨h, hh⟩, rfl⟩

end Glauberman

section Layer

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem eq_one_of_mem_pCore_of_odd {O' : Subgroup Y} (hO'odd : Odd (Nat.card O')) {t : Y}
    (ht : t ∈ pCore 2 Y) (htO : t ∈ O') : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := Y)) ⟨t, ht⟩
  have h1 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  have h2 : orderOf t ∣ Nat.card O' := Subgroup.orderOf_dvd_natCard O' htO
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hodd : Odd (orderOf t) := Odd.of_dvd_nat hO'odd h2
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 hne)
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.1 hi

theorem conj_centralizes_layer (hY : pPrimeCore 2 Y = ⊥) {x : Y} {L : Subgroup Y} (hL : IsComponent L)
    {O' : Subgroup Y} (hO'odd : Odd (Nat.card O'))
    (hO'norm : ∀ n ∈ normalizer (L : Set Y), ∀ o ∈ O', n * o * n⁻¹ ∈ O')
    (hZ : ∀ n ∈ normalizer (L : Set Y), x * n * x⁻¹ * n⁻¹ ∈ O') :
    ∀ h : Y, ∀ l ∈ L, (h * x * h⁻¹) * l = l * (h * x * h⁻¹) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLayer : layer Y = ComponentClassification.Layer.subgroup Y := layer_eq_componentClassification Y
  set E : Subgroup Y := ComponentClassification.Layer.subgroup Y with hE
  have hEnorm : E.Normal := ComponentClassification.Layer.normal Y
  have hLE : L ≤ E := by
    rw [← hLayer]
    exact le_sSup hL
  have hEN : E ≤ normalizer (L : Set Y) := by
    refine sSup_le fun K hK => ?_
    have hK' : IsComponent K := (isComponent_iff_open K).2 hK
    rcases CFSG.LocalCores.distinct_components_commute hK' hL with h | h
    · rw [h]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h).trans (Subgroup.centralizer_le_normalizer _)
  set T : Subgroup Y := O' ⊓ E with hT
  have hTodd : Odd (Nat.card T) :=
    Odd.of_dvd_nat hO'odd (Subgroup.card_dvd_of_le (inf_le_left : T ≤ O'))
  have hTsolv : Group.IsSolvable T := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hTodd
  have hTE : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T := by
    intro e he t ht
    exact ⟨hO'norm e (hEN he) t ht.1, hEnorm.conj_mem t ht.2 e⟩
  have hTsub : T.IsSubnormal := by
    refine Subgroup.IsSubnormal.step T E inf_le_right hEnorm.isSubnormal ?_
    exact ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hTE g g.2 n hn⟩
  have hcomm : ⁅E, T⁆ = ⊥ :=
    ComponentClassification.Layer.commutes_with_solvable_subnormal T
      (ComponentClassification.Components.chain_of_mathlib_subnormal hTsub)
  have hT1 : ∀ t ∈ T, t = 1 := by
    intro t ht
    have hcen : (⟨t, ht.2⟩ : ↥E) ∈ Subgroup.center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro e
      have h2 : ⁅(e : Y), t⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator e.2 ht
        rw [hcomm, Subgroup.mem_bot] at this
        exact this
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 h2)
    have hF := ComponentClassification.GeneralizedFitting.layer_center_le_fitting Y
    have hmem : t ∈ (Subgroup.center E).map E.subtype := ⟨⟨t, ht.2⟩, hcen, rfl⟩
    have hFit : t ∈ fittingSubgroup Y := hF hmem
    rw [Fitting_eq_pcore Y 2 hY] at hFit
    exact eq_one_of_mem_pCore_of_odd hO'odd hFit ht.1
  have hxE : ∀ e ∈ E, x * e = e * x := by
    intro e he
    have h1 : x * e * x⁻¹ * e⁻¹ ∈ T :=
      ⟨hZ e (hEN he), E.mul_mem (hEnorm.conj_mem e he x) (E.inv_mem he)⟩
    have h2 := hT1 _ h1
    calc x * e = (x * e * x⁻¹ * e⁻¹) * (e * x) := by group
      _ = e * x := by rw [h2, one_mul]
  intro h l hl
  have hl' : h⁻¹ * l * h ∈ E := by
    have := hEnorm.conj_mem l (hLE hl) h⁻¹
    simpa using this
  have := hxE _ hl'
  calc (h * x * h⁻¹) * l = h * (x * (h⁻¹ * l * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * l * h) * x) * h⁻¹ := by rw [this]
    _ = l * (h * x * h⁻¹) := by group

end Layer

end CFSG.GH74.Generic.S3
