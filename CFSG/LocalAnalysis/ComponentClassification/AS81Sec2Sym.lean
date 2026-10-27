module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sec2Z_comm (A E F : Subgroup G) : sec2Z A F E = sec2Z A E F := by
  rw [sec2Z, sec2Z, sup_comm]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem card_sec2S
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : Nat.card (sec2S A R E F) = 16 * 64 := by
  have hS := (isElemQuot_sec2S h11 hE16 hF hL hodd).2
  have h1 := relIndex_mul_card E (sec2S A R E F)
  rw [inf_eq_left.mpr hS.1, hS.2.1, hF.cardE] at h1
  exact h1.symm

theorem sec2S_comm
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : sec2S A R F E = sec2S A R E F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := isSylowOf_sec2S h11 hE16 hF hL hodd
  have hsyl' := isSylowOf_sec2S h11 hE16 hF.symm hL hodd
  have hXS := le_normalizer_sec2S (A := A) (R := R) (E := E) (F := F)
  have hS'X : sec2S A R F E ≤ centralizer (sec2Z A E F : Set G) ⊓
      centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓ normalizer (E : Set G) ⊓
        normalizer (F : Set G) := fun x hx => by
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hsyl'.le hx
    rw [sec2Z_comm] at h1 h2
    exact ⟨⟨⟨h1, h2⟩, h4⟩, h3⟩
  have hY2 : IsPGroup 2 (sec2S A R E F ⊔ sec2S A R F E : Subgroup G) :=
    hsyl.isPGroup.to_sup_of_normal_left' hsyl'.isPGroup (hS'X.trans hXS)
  have hY := hsyl.eq_of_le le_sup_left (sup_le hsyl.le hS'X) hY2
  have hS'S : sec2S A R F E ≤ sec2S A R E F := hY ▸ le_sup_right
  refine eq_of_le_of_card_ge hS'S ?_
  rw [card_sec2S h11 hE16 hF hL hodd]
  have hS' := (isElemQuot_sec2S h11 hE16 hF.symm hL hodd).2
  have h1 := relIndex_mul_card F (sec2S A R F E)
  rw [inf_eq_left.mpr hS'.1, hS'.2.1, hF.cardF] at h1
  omega

theorem sec2P_F_le_normalizer_sec2S
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    sec2P F ≤ normalizer (sec2S A R E F : Set G) := by
  rw [← sec2S_comm h11 hE16 hF hL hodd]
  exact sec2P_le_normalizer_sec2S h11 hE16 hF.symm hL hodd

theorem centralizerMod_F_le_sec2S
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    centralizerMod (sec2P F) (R ⊔ sec2Z A F E) (sec2Z A F E) ≤ sec2S A R E F := by
  rw [← sec2S_comm h11 hE16 hF hL hodd]
  exact le_sup_right

theorem rightConjugate_inf_eq_and_sec2S_eq
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {x : G}
    (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) :
    rightConjugate E x ⊓ E = sec2Z A E F ∧ sec2S A R E F = E ⊔ rightConjugate E x := by
  have hxC : x ∉ centralizerMod (sec2P F) (R ⊔ sec2Z A F E) (sec2Z A F E) := fun h =>
    hxS (centralizerMod_F_le_sec2S h11 hE16 hF hL hodd h)
  obtain ⟨hinf, hsup⟩ := sec2S_eq_sup_rightConjugate h11 hE16 hF.symm hL hodd hx hxC
  refine ⟨?_, ?_⟩
  · rw [inf_comm, hinf, sec2Z_comm]
  · rw [← sec2S_comm h11 hE16 hF hL hodd, hsup]

end Frame

end CFSG.ComponentClassification.AS81
