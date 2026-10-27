module

public import CFSG.LargeExtraspecial.A2ModD4Main
public import CFSG.LargeExtraspecial.DWRtMain
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ARS
  CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {X : Type} [Group X] {D : Set X}

@[expose] def rootSet (D : Set X) : Set (Subgroup X) := {A | ∃ d ∈ D, A = Subgroup.zpowers d}

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {d x : X} (hd : d * d = 1)
    (hx : x ∈ Subgroup.zpowers d) : x = 1 ∨ x = d := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : d ^ (2 : ℤ) = 1 := by rw [zpow_two, hd]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem conjSub_zpowers_eq (d g : X) :
    conjSub (Subgroup.zpowers d) g = Subgroup.zpowers (g * d * g⁻¹) := by
  rw [conjSub, MonoidHom.map_zpowers]
  rfl

theorem commuting_zpowers_of_commute {d e : X} (h : Commute d e) :
    Commuting (Subgroup.zpowers d) (Subgroup.zpowers e) := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact h.zpow_zpow i j

theorem commutator_zpowers_eq {d e : X} (hdd : d * d = 1) (hee : e * e = 1) :
    ⁅Subgroup.zpowers d, Subgroup.zpowers e⁆ = Subgroup.zpowers ((d * e) ^ 2) := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hc : ⁅d, e⁆ = (d * e) ^ 2 := by
    rw [commutatorElement_def, hdi, hei, pow_two]
    group
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hdd ha with rfl | rfl
    · rw [commutatorElement_one_left]
      exact one_mem _
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hee hb with rfl | rfl
    · rw [commutatorElement_one_right]
      exact one_mem _
    rw [hc]
    exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, ← hc]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers d) (Subgroup.mem_zpowers e)

theorem commute_sq_of_mul_self {d e : X} (hdd : d * d = 1) (hee : e * e = 1)
    (hf : (d * e) ^ 2 * (d * e) ^ 2 = 1) :
    Commute ((d * e) ^ 2) d ∧ Commute ((d * e) ^ 2) e := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hfi : ((d * e) ^ 2)⁻¹ = (d * e) ^ 2 := inv_eq_of_mul_eq_one_right hf
  have h1 : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [hdi, mul_inv_rev, hdi, hei]
    calc d * (d * e) * d = (d * d) * (e * d) := by group
      _ = e * d := by rw [hdd, one_mul]
  have h2 : e * (d * e) * e⁻¹ = (d * e)⁻¹ := by
    rw [mul_inv_rev, hdi, hei]
    calc e * (d * e) * e = e * d * (e * e) := by group
      _ = e * d := by rw [hee, mul_one]
  have h1' : d * (d * e) ^ 2 * d⁻¹ = (d * e) ^ 2 := by rw [← conj_pow, h1, inv_pow, hfi]
  have h2' : e * (d * e) ^ 2 * e⁻¹ = (d * e) ^ 2 := by rw [← conj_pow, h2, inv_pow, hfi]
  constructor
  · show (d * e) ^ 2 * d = d * (d * e) ^ 2
    calc (d * e) ^ 2 * d = d * (d * e) ^ 2 * d⁻¹ * d := by rw [h1']
      _ = d * (d * e) ^ 2 := by group
  · show (d * e) ^ 2 * e = e * (d * e) ^ 2
    calc (d * e) ^ 2 * e = e * (d * e) ^ 2 * e⁻¹ * e := by rw [h2']
      _ = e * (d * e) ^ 2 := by group

namespace RootClass

theorem conj_mem (hD : RootClass X D) : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
  obtain ⟨d₀, -, hd₀⟩ := hD.1.2.1
  intro g d hd
  exact (hd₀ _).mpr (((hd₀ d).mp hd).trans (isConj_iff.mpr ⟨g, rfl⟩))

theorem opposite_of_orderOf_eq_three (hD : RootClass X D) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (hne : Subgroup.zpowers d ≠ Subgroup.zpowers e) (h3 : orderOf (d * e) = 3) :
    Opposite (Subgroup.zpowers d) (Subgroup.zpowers e) := by
  have hdd := hD.mul_self hd
  have hee := hD.mul_self he
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hp3 : (d * e) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have key : e * d * e⁻¹ = d * e * d⁻¹ := by
    have h1 : e * d * e = d⁻¹ * e⁻¹ * d⁻¹ := by
      calc e * d * e = d⁻¹ * ((d * e) * (d * e) * (d * e)) * e⁻¹ * d⁻¹ := by group
        _ = d⁻¹ * e⁻¹ * d⁻¹ := by rw [← pow_three', hp3]; group
    rw [hei, hdi, h1, hdi, hei]
  refine ⟨hne, fun a ha ha1 => ?_, fun b hb hb1 => ?_⟩
  · rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hdd ha with rfl | rfl
    · exact absurd rfl ha1
    refine ⟨e, Subgroup.mem_zpowers e, hD.ne_one he, ?_⟩
    rw [conjSub_zpowers_eq, conjSub_zpowers_eq, key]
  · rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hee hb with rfl | rfl
    · exact absurd rfl hb1
    refine ⟨d, Subgroup.mem_zpowers d, hD.ne_one hd, ?_⟩
    rw [conjSub_zpowers_eq, conjSub_zpowers_eq, key]

theorem special_of_orderOf_eq_four (hD : RootClass X D) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) :
    Special (rootSet D) (Subgroup.zpowers d) (Subgroup.zpowers e) := by
  have hdd := hD.mul_self hd
  have hee := hD.mul_self he
  have hfD : (d * e) ^ 2 ∈ D := hD.1.2.2.2.2 d hd e he h4
  obtain ⟨hfd, hfe⟩ := commute_sq_of_mul_self hdd hee (hD.mul_self hfD)
  rw [Special, commutator_zpowers_eq hdd hee]
  exact ⟨⟨_, hfD, rfl⟩, commuting_zpowers_of_commute hfd, commuting_zpowers_of_commute hfe⟩

theorem isRootClass [Finite X] (hD : RootClass X D) : IsRootClass (rootSet D) where
  conj_class := by
    obtain ⟨d₀, hd₀, hcls⟩ := hD.1.2.1
    refine ⟨Subgroup.zpowers d₀, Set.ext fun A => ⟨?_, ?_⟩⟩
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨g, rfl⟩ := isConj_iff.mp ((hcls d).mp hd)
      exact ⟨g, conjSub_zpowers_eq d₀ g⟩
    · rintro ⟨g, rfl⟩
      rw [conjSub_zpowers_eq]
      exact ⟨_, hD.conj_mem g d₀ hd₀, rfl⟩
  ne_bot := by
    rintro A ⟨d, hd, rfl⟩ h
    have h1 := Subgroup.mem_zpowers d
    rw [h, Subgroup.mem_bot] at h1
    exact hD.ne_one hd h1
  mul_self := by
    rintro A ⟨d, hd, rfl⟩ a ha
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self (hD.mul_self hd) ha with rfl | rfl
    · exact mul_one 1
    · exact hD.mul_self hd
  rel := by
    rintro A ⟨d, hd, rfl⟩ B ⟨e, he, rfl⟩ hAB
    have hdd := hD.mul_self hd
    have hee := hD.mul_self he
    have hle : orderOf (d * e) ≤ 4 := hD.1.2.2.2.1 d hd e he
    have hpos : 0 < orderOf (d * e) := orderOf_pos _
    interval_cases h : orderOf (d * e)
    · exfalso
      apply hAB
      have h1 : d * e = 1 := orderOf_eq_one_iff.mp h
      have h2 : e = d := by
        calc e = d⁻¹ * (d * e) := by group
          _ = d := by rw [h1, mul_one]; exact inv_eq_of_mul_eq_one_right hdd
      rw [h2]
    · left
      apply commuting_zpowers_of_commute
      have h1 : (d * e) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
      have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
      show d * e = e * d
      calc d * e = (d * e)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_two, h1])).symm
        _ = e * d := by rw [mul_inv_rev, hdi, hei]
    · exact Or.inr (Or.inl (hD.opposite_of_orderOf_eq_three hd he hAB h))
    · exact Or.inr (Or.inr (hD.special_of_orderOf_eq_four hd he h))
  gen := by
    rw [eq_top_iff, ← hD.closure_eq_top, Subgroup.closure_le]
    intro d hd
    exact (le_iSup₂ (f := fun A (_ : A ∈ rootSet D) => A) (Subgroup.zpowers d) ⟨d, hd, rfl⟩)
      (Subgroup.mem_zpowers d)

theorem arsHyp [Finite X] (hD : RootClass X D) : Hyp X (rootSet D) where
  finite := inferInstance
  root := hD.isRootClass
  nondeg := by
    obtain ⟨d, hd, e, he, h4⟩ := hD.2.1
    exact ⟨_, ⟨d, hd, rfl⟩, _, ⟨e, he, rfl⟩, hD.special_of_orderOf_eq_four hd he h4⟩
  center := hD.2.2.1
  twoCore := hD.2.2.2

theorem card_eq_two (hD : RootClass X D) : ∀ A ∈ rootSet D, Nat.card A = 2 := by
  rintro A ⟨d, hd, rfl⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hD.mul_self hd) (hD.ne_one hd)

end RootClass

section Outcomes

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem RootClass.not_lieModel_trialityD4 (hD : RootClass X D) (hA : A2Action D Q ρ) :
    ¬ LieModel X .trialityD4 0 2 1 := by
  obtain ⟨d, hd⟩ := hD.nonempty
  exact not_lieModel_trialityD4_of_finrank_commSpace_le_two ρ hA.injective (hA.ne_one hd)
    (hA.mul_self hd) (hA.isTypeA hd).2.2.2.1.le

theorem RootClass.eq_one_of_lieModel [Finite X] (hD : RootClass X D) {t : StatedLieTag}
    (ht : t ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    {f : ℕ} (hf : 1 ≤ f) (h : LieModel X t 0 2 f) : f = 1 := by
  by_contra hne
  exact DW.dw2FieldInput X t 0 f (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, ht⟩))) h D hD.1

end Outcomes

end CFSG.LargeExtraspecial.A2Mod
