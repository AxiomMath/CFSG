module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivCW
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivPar
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec2Quot

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem card_sup_inf_eq (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : Nat.card ((E ⊔ F) ⊓ A : Subgroup G) = 64 := by
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  obtain ⟨hRD, -, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  have hEF : Nat.card (E ⊔ F : Subgroup G) = 256 := by
    have h := card_sup_mul_card_inf (H := E) (R := F) (hF.F_le_normalizer hL hodd)
    rw [hF.card_inf, hF.cardE, hF.cardF] at h
    omega
  have h := card_eq_card_inf_mul hRA hRD hF.sylow.le hRA1
  rw [hEF, hF.cardR] at h
  omega

theorem isSylowOf_sup_inf_sec2L (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : IsSylowOf 2 ((E ⊔ F) ⊓ A) (sec2L A E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  obtain ⟨-, hT₀, -⟩ := sylow_sup_structure hRA hF.sylowR.isPGroup hF.sylow
  have hTL := sup_inf_le_sec2L hF hL hodd
  have hLA : sec2L A E ≤ A := (sec2L_le A E).trans inf_le_left
  obtain ⟨-, hT2, hidx⟩ := isSylowOf_iff.mp hT₀
  refine isSylowOf_iff.mpr ⟨hTL, hT2, fun h => hidx (h.trans ?_)⟩
  exact Dvd.intro _ (relIndex_mul_relIndex _ _ _ hTL hLA)

theorem exists_mem_inf_not_mem_E (hF : Frame G A A R g E F)
    (hodd : Odd (Nat.card (center ↥A))) : ∃ f ∈ F ⊓ A, f ∉ E := by
  by_contra h
  push Not at h
  have hle : F ⊓ A ≤ sec2Z A E F := by
    rw [hF.sec2Z_eq]
    exact fun f hf => ⟨⟨h f hf, hf.1⟩, hf.2⟩
  have h1 := card_le_of_le hle
  rw [card_inf_left hF.symm hodd, hF.card_sec2Z hodd] at h1
  omega

end Frame

section Wsec

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
  (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
  (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y))

include h11 hE16 hF hL hodd hyA hyE hyU hy3

theorem R_le_normalizer_sec2W : R ≤ normalizer (sec2W A E y : Set G) := by
  obtain ⟨-, -, -, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  exact hF.R_le_E.trans ((isElemQuot_sec2P h11 hE16 hF hL hodd).1.trans hPW)

theorem sec2L_inf_sec2W : sec2L A E ⊓ sec2W A E y = E ⊓ A := by
  obtain ⟨-, hUW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  refine le_antisymm ?_ (le_inf ((inf_le_inf_right A le_sup_left).trans
    (sup_inf_le_sec2L hF hL hodd)) hUW)
  rw [← sec2W_inf_eq h11 hE16 hF hL hodd hyA hyE hyU hy3, inf_comm]
  exact inf_le_inf_left _ ((sec2L_le A E).trans inf_le_left)

variable (hW : IsElemAbelian 2 (sec2W A E y))
include hW

theorem inf_sec2W_eq_bot : R ⊓ sec2W A E y = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [mem_bot]
  refine eq_one_of_mem_centralizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hr.1
    (mem_centralizer_iff.mpr fun w hw => ?_)
  exact congrArg Subtype.val (hW.1.is_comm.comm ⟨w, hw⟩ ⟨r, hr.2⟩)

theorem card_nbar_R : Nat.card (nbar (sec2W A E y) R) = 4 := by
  have h := card_nbar (R_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3)
  rw [inf_sec2W_eq_bot h11 hE16 hF hL hodd hyA hyE hyU hy3 hW, card_bot, mul_one,
    hF.cardR] at h
  exact h

omit h11 hE16 hL hodd hyA hyE hyU hy3
  hW in
theorem nbar_R_le_centralizer :
    nbar (sec2W A E y) R ≤ centralizer (nbar (sec2W A E y) (sec2L A E) : Set (↥(normalizer
      (sec2W A E y : Set G)) ⧸ (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))) :=
  nbar_le_centralizer (le_centralizer_iff.mp (((sec2L_le A E).trans inf_le_left).trans
    (le_centralizer_iff.mp hF.sylowR.le)))

theorem isSylowOf_nbar_inf : IsSylowOf 2 (nbar (sec2W A E y) (F ⊓ A))
      (nbar (sec2W A E y) (sec2L A E)) ∧ Nat.card (nbar (sec2W A E y) (F ⊓ A)) = 4 := by
  set W := sec2W A E y with hWdef
  have hLN := sec2L_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hTL := isSylowOf_sup_inf_sec2L hF hL hodd
  have hLW := sec2L_inf_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hWA := sec2W_inf_eq h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hUT : E ⊓ A ≤ (E ⊔ F) ⊓ A := inf_le_inf_right A le_sup_left
  have hsyl := isSylowOf_nbar hTL hLN (hLW ▸ hUT)
  have hTN : (E ⊔ F) ⊓ A ≤ normalizer (W : Set G) := hTL.le.trans hLN
  have hFT : F ⊓ A ≤ (E ⊔ F) ⊓ A := inf_le_inf_right A le_sup_right
  have hTW : (E ⊔ F) ⊓ A ⊓ W = E ⊓ A := by
    refine le_antisymm ?_ (le_inf hUT (hLW ▸ inf_le_right))
    rw [← hWA, inf_comm W A]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hT4 : Nat.card (nbar W ((E ⊔ F) ⊓ A)) = 4 := by
    have h := card_nbar hTN
    rw [hTW, card_inf_left hF hodd, card_sup_inf_eq hF hL hodd] at h
    omega
  have hFW : F ⊓ A ⊓ W = sec2Z A E F := by
    rw [hF.sec2Z_eq, inf_assoc, inf_comm A W, hWA]
    ext x
    simp only [mem_inf]
    tauto
  have hF4 : Nat.card (nbar W (F ⊓ A)) = 4 := by
    have h := card_nbar (hFT.trans hTN)
    rw [hFW, hF.card_sec2Z hodd, card_inf_left hF.symm hodd] at h
    omega
  have heq : nbar W (F ⊓ A) = nbar W ((E ⊔ F) ⊓ A) :=
    eq_of_le_of_card_ge (nbar_mono hFT) (by rw [hT4, hF4])
  exact ⟨heq ▸ hsyl, hF4⟩

end Wsec

end CFSG.ComponentClassification.AS81
