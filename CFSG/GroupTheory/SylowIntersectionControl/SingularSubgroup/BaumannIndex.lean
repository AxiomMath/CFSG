module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.ModuleSetting
import CFSG.Quasithin.Background.C126NatDSimple
import CFSG.Quasithin.Background.G64NatSec
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeOffender

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem mem_gomiOset_autOn_g45la (h : GomiThm45Counterexample c G S) {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A) (hAC : ¬ A ≤ Subgroup.centralizer (gomiV G : Set Ω)) :
    autOn A (gomiV G) ∈ gomiOset (autOn G (gomiV G)) := by
  have hV : IsElemAbelian 2 (gomiV G) := (gomiV_moduleSetting G).1
  have hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hAG : A ≤ G := hA.1.trans h.isSylowTwoOf.1
  have hFF := CFSG.AGLEmbedding.AscTenThree.isFFStarOffender_autOn_of_isMaxElemAbelian
    (H := G) (V := gomiV G) (S := S) (A := A) hV (gomiV_le_sylow h) hVG hAG hA hAC
  refine ⟨hFF.1, hFF.2.1, hFF.2.2.1, ?_⟩
  have h := hFF.2.2.2 (⊥ : Subgroup (MulAut ↥(gomiV G))) bot_le
  rwa [CFSG.Quasithin.B1.card_bot_mul_card_fixV] at h

private theorem fact35_apply_g45la (h35 : GomiFact35)
    {m : ℕ} (hm : 1 ≤ m) (hSL : IsSLn ↥(autOn G (gomiV G)) 2 m) {A : Subgroup Ω}
    (hmem : autOn A (gomiV G) ∈ gomiOset (autOn G (gomiV G))) :
    BinaryNaturalSL (autOn G (gomiV G)) ⊤ (fixV (autOn G (gomiV G))) 2 m ∧
      Nat.card (autOn A (gomiV G)) = 2 ^ m ∧
        Nat.card (gomiV G) = 2 ^ m * Nat.card (fixV (autOn A (gomiV G))) :=
  h35 ↥(gomiV G) (fun w => Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2))
    (autOn G (gomiV G)) m hm hSL (autOn A (gomiV G)) hmem

theorem relIndex_centralizer_gomiV_eq (h : GomiThm45Counterexample c G S) {m : ℕ}
    (hSL : IsSLn ↥(autOn G (gomiV G)) 2 m) :
    (Subgroup.centralizer (gomiV G : Set Ω)).relIndex S = 2 ^ m := by
  have hSV : S ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    h.isSylowTwoOf.1.trans (gomiV_moduleSetting G).2
  rw [← CFSG.Quasithin.AutOn.card_autOn_eq_relIndex_centralizer hSV]
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := hSL
  let _ : Field K := hK
  let _ : Finite K := hKfin
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hKcard
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  refine CFSG.Quasithin.C126.Nat.card_sylow_of_equiv_sl2 (Nat.one_le_iff_ne_zero.mpr hm0)
    hKcard (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm) ?_
  exact isSylowIn_autOn h

theorem relIndex_eq_of_isMaxElemAbelian (h : GomiThm45Counterexample c G S) (h35 : GomiFact35)
    {m : ℕ} (hm : 1 ≤ m) (hSL : IsSLn ↥(autOn G (gomiV G)) 2 m) {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A) (hAC : ¬ A ≤ Subgroup.centralizer (gomiV G : Set Ω)) :
    (Subgroup.centralizer (gomiV G : Set Ω)).relIndex A = 2 ^ m ∧
      (Subgroup.centralizer (A : Set Ω)).relIndex (gomiV G) = 2 ^ m := by
  have hV : IsElemAbelian 2 (gomiV G) := (gomiV_moduleSetting G).1
  have hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hAn : A ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    (hA.1.trans h.isSylowTwoOf.1).trans hVG
  obtain ⟨-, hcardA, hcardV⟩ :=
    fact35_apply_g45la h35 hm hSL (mem_gomiOset_autOn_g45la h hA hAC)
  have hfix := CFSG.Quasithin.card_fixV_autOn_eq hV hAn
  refine ⟨?_, ?_⟩
  · rw [← CFSG.Quasithin.AutOn.card_autOn_eq_relIndex_centralizer hAn]
    exact hcardA
  · have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set Ω)) (gomiV G)
    rw [inf_comm, ← hfix, hcardV] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul

private theorem card_gomiV_eq_g45la (h35 : GomiFact35)
    {m : ℕ} (hm : 1 ≤ m) (hSL : IsSLn ↥(autOn G (gomiV G)) 2 m) {A : Subgroup Ω}
    (hmem : autOn A (gomiV G) ∈ gomiOset (autOn G (gomiV G))) :
    Nat.card (gomiV G) = 2 ^ (2 * m) * Nat.card (fixV (autOn G (gomiV G))) := by
  obtain ⟨hBNSL, -, -⟩ := fact35_apply_g45la h35 hm hSL hmem
  obtain ⟨K, hK, hKfin, hKcard, ⟨π, hπ⟩⟩ := hBNSL
  let _ : Field K := hK
  let _ : Finite K := hKfin
  have h := CFSG.Quasithin.G64.RealizesVia.card_eq hπ
  rw [CFSG.Quasithin.G64.card_natMod, hKcard] at h
  rw [Subgroup.card_top] at h
  have h2 : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]
  rwa [h2] at h

theorem relIndex_gomiV_centralizer_eq (h : GomiThm45Counterexample c G S) (h35 : GomiFact35)
    {m : ℕ} (hm : 1 ≤ m) (hSL : IsSLn ↥(autOn G (gomiV G)) 2 m) :
    (Subgroup.centralizer (G : Set Ω)).relIndex (gomiV G) = 2 ^ (2 * m) := by
  have hV : IsElemAbelian 2 (gomiV G) := (gomiV_moduleSetting G).1
  have hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  obtain ⟨A, hA, hAC⟩ := exists_isMaxElemAbelian_not_le_centralizer h
  have hcardV := card_gomiV_eq_g45la h35 hm hSL (mem_gomiOset_autOn_g45la h hA hAC)
  have hfix := CFSG.Quasithin.card_fixV_autOn_eq hV hVG
  have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer (G : Set Ω)) (gomiV G)
  rw [inf_comm, ← hfix, hcardV] at hmul
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul

end CFSG.GroupTheory.GomiThm45Counterexample
