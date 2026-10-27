module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix

theorem card_SL_four_two {F : Type} [Field F] [Finite F] (h : Nat.card F = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) F) = 20160 := by
  have : Fintype F := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, h]
  decide

theorem card_SL_five_two {F : Type} [Field F] [Finite F] (h : Nat.card F = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) F) = 9999360 := by
  have : Fintype F := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, h]
  decide

theorem card_SL_three_four {F : Type} [Field F] [Finite F] (h : Nat.card F = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 60480 := by
  have : Fintype F := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, h]
  decide

theorem card_statedProj_dvd (n : ℕ) {F : Type} [Field F] [Finite F] :
    Nat.card (StatedProj (StatedSL n F)) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) F) := by
  have h1 := Subgroup.card_quotient_dvd_card
    ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))
  rwa [← Nat.card_congr (specialLinearGroupEquivStatedSL n F).toEquiv] at h1

theorem card_statedProj_of_card_two (n : ℕ) {F : Type} [Field F] [Finite F]
    (h : Nat.card F = 2) :
    Nat.card (StatedProj (StatedSL n F)) = Nat.card (Matrix.SpecialLinearGroup (Fin n) F) := by
  have hu : ∀ c : Fˣ, c = 1 := by
    intro c
    have h1 : Nat.card Fˣ = 1 := by rw [Nat.card_units, h]
    exact (Nat.card_eq_one_iff_unique.1 h1).1.elim c 1
  have hbot : (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, hu c, map_one]
    rfl
  rw [Nat.card_congr (specialLinearGroupEquivStatedSL n F).toEquiv]
  show Nat.card (↥(StatedSL n F) ⧸ _) = _
  rw [hbot, ← Subgroup.index_eq_card, Subgroup.index_bot]

variable {G : Type} [Group G]

theorem card_hSub_of_natural_four {T H : Subgroup G} (hTH : T ≤ H) (hT : Nat.card T = 16)
    (hnat : NaturalSL T H 4 1) : Nat.card H = 322560 := by
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    simpa using this
  have hq : Nat.card (↥H ⧸ T.subgroupOf H) = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_SL_four_two hF2
  have hTs : Nat.card (T.subgroupOf H) = 16 := by
    rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf H), hq, hTs]

theorem not_isPGroup_of_natural_four [Finite G] {T H : Subgroup G} (hTH : T ≤ H)
    (hT : Nat.card T = 16) (hnat : NaturalSL T H 4 1) : ¬ IsPGroup 2 H := by
  intro hp
  have hc := card_hSub_of_natural_four hTH hT hnat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  rw [hc] at hk
  have h3 : 3 ∣ 2 ^ k := by
    rw [← hk]
    norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end CFSG.CGT.T75Q
