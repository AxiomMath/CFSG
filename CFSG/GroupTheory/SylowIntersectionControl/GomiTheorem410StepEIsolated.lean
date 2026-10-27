module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEHyp21
public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiBenderSL2
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedBender
import CFSG.GroupTheory.SylowIntersectionControl.GomiL2StatedSL
import CFSG.GroupTheory.SylowIntersectionControl.AlternatingNotBender
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne

variable {Ω : Type} [Group Ω] [Finite Ω] {G : Subgroup Ω}

private theorem center_eq_bot_of_mulEquiv_alternating_eni {L : Type*} [Group L] {n : ℕ}
    (hn : 4 ≤ n) (e : L ≃* alternatingGroup (Fin n)) : Subgroup.center L = ⊥ := by
  have hmap : Subgroup.map (e : L →* alternatingGroup (Fin n)) (Subgroup.center L) = ⊥ := by
    rw [Subgroup.map_center_eq e]
    exact alternatingGroup.center_eq_bot (α := Fin n) (by simpa using hn)
  exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center L)
    (f := (e : L →* alternatingGroup (Fin n))) e.injective).mp hmap

private theorem eq_bot_of_normal_isPGroup_two_eni {Y X : Type} [Group Y] [Group X]
    (hY : CFSG.pCore 2 Y = ⊥) (e : Y ≃* X) (N : Subgroup X) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have hmap : N.map e.symm.toMonoidHom ≤ CFSG.pCore 2 Y :=
    le_sSup ⟨hN.map e.symm.toMonoidHom e.symm.surjective, hN2.map e.symm.toMonoidHom⟩
  rw [hY] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (H := N) e.symm.injective).mp
    (le_bot_iff.mp hmap)

private theorem odd_card_center_eni {Y X : Type} [Group Y] [Group X] [Finite X]
    (hY : CFSG.pCore 2 Y = ⊥) (e : Y ≃* X) : Odd (Nat.card (Subgroup.center X)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 2
    (even_iff_two_dvd.mp heven)
  let zx : X := z
  let N : Subgroup X := Subgroup.zpowers zx
  have hNle : N ≤ Subgroup.center X := Subgroup.zpowers_le.mpr z.2
  have hNnorm : N.Normal := Subgroup.normal_of_le_center hNle
  have hN2 : IsPGroup 2 N := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card (Subgroup.zpowers zx) = 2 ^ 1
    rw [Nat.card_zpowers, Subgroup.orderOf_coe z, hz]
    norm_num
  have hNbot : N = ⊥ := eq_bot_of_normal_isPGroup_two_eni hY e N hNnorm hN2
  have hzx : zx ∈ N := Subgroup.mem_zpowers zx
  rw [hNbot] at hzx
  have hzx1 : zx = 1 := Subgroup.mem_bot.mp hzx
  have hz1 : orderOf zx = 1 := by rw [hzx1, orderOf_one]
  rw [Subgroup.orderOf_coe z] at hz1
  omega

private theorem fusionIsBenderGroup_center_quotient_eni (hBender : GomiBender)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (hiso : IsPIsolatedOver 2 (⊤ : Subgroup ↥(autOn G (gomiV G))) ⊥) :
    fusionIsBenderGroup
      ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_gomiBarOf (G := G) (B := B) hB hCQ
  have hK2 : CFSG.pCore 2 (↥B ⧸ CFSG.pCore 2 ↥B) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥B) (p := 2)
  have hIsoBar : IsPIsolatedOver 2 (gomiBarOf G B) ⊥ :=
    hiso.of_isSubnormal_le (isSubnormal_gomiBarOf hB)
      (even_iff_two_dvd.mp (even_card_gomiBarOf hB hBt hCQ)) le_rfl
  have hisoB : IsPIsolatedOver 2 (⊤ : Subgroup ↥(gomiBarOf G B)) ⊥ := by
    have key := (isPIsolatedOver_subgroupOf_iff (p := 2) (H := ⊥)
      (K := gomiBarOf G B) (K' := gomiBarOf G B) bot_le le_rfl).mpr hIsoBar
    simpa [Subgroup.subgroupOf_self, Subgroup.bot_subgroupOf] using key
  let eTop : (↥B ⧸ CFSG.pCore 2 ↥B) ≃* ↥(⊤ : Subgroup ↥(gomiBarOf G B)) :=
    e.trans Subgroup.topEquiv.symm
  have hQs : CFSG.IsQuasisimple (↥(⊤ : Subgroup ↥(gomiBarOf G B))) :=
    (IsGomi410Type.isQuasisimple hB hBt).of_mulEquiv eTop.symm
  have hOdd : Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup ↥(gomiBarOf G B)))) :=
    odd_card_center_eni hK2 eTop
  have hmain := eq_top_of_isPIsolatedOver hBender (X := ↥(gomiBarOf G B)) (L := ⊤) hisoB
    (fun g hg => absurd (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective) hg)
    (by
      have hnc : Subgroup.normalClosure (⊤ : Set ↥(gomiBarOf G B)) = ⊤ :=
        Subgroup.normalClosure_eq_self (H := (⊤ : Subgroup ↥(gomiBarOf G B)))
      have hq0 : IsPGroup 2 (↥(gomiBarOf G B) ⧸ (⊤ : Subgroup ↥(gomiBarOf G B))) := by
        have : Subsingleton (↥(gomiBarOf G B) ⧸ (⊤ : Subgroup ↥(gomiBarOf G B))) :=
          QuotientGroup.subsingleton_quotient_top
        exact IsPGroup.of_subsingleton 2 _
      exact hq0.of_equiv (QuotientGroup.quotientMulEquivOfEq hnc).symm)
    (fun N hN hN2 => eq_bot_of_normal_isPGroup_two_eni hK2 e N hN hN2)
    (Or.inr ⟨hQs, hOdd⟩)
  have hBendBar : fusionIsBenderGroup
      (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B)) := hmain.2 hQs
  exact CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e
      (Subgroup.map_center_eq e)).symm hBendBar

theorem not_isPIsolatedOver_autOn (hBender : GomiBender) (hBSL : GomiBenderSL2)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    ¬ IsPIsolatedOver 2 (⊤ : Subgroup ↥(autOn G (gomiV G))) ⊥ := by
  intro hiso
  have hBendK := fusionIsBenderGroup_center_quotient_eni hBender hB hBt hCQ hiso
  rcases hBt with ⟨hc, hL2, hU3, hSz⟩ | ⟨m, hm, ⟨eA⟩⟩ | ⟨⟨eA7⟩, _⟩
  · have h43 : GomiHyp43Type (↥B ⧸ CFSG.pCore 2 ↥B) := Or.inl ⟨hc, hU3, hSz⟩
    obtain ⟨m, hm2, F, hF, hFfin, hFcard, ⟨eSL⟩⟩ :=
      hBSL (↥B ⧸ CFSG.pCore 2 ↥B) h43 hBendK
    let : Field F := hF
    let : Finite F := hFfin
    exact hL2 (isGomiL2_of_mulEquiv_statedSL hm2 hFcard eSL)
  · have hc := center_eq_bot_of_mulEquiv_alternating_eni (L := ↥B ⧸ CFSG.pCore 2 ↥B)
      (n := 2 * m) (by omega) eA
    have eQ := (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientBot.trans eA)
    exact not_fusionIsBenderGroup_of_mulEquiv_alternatingGroup (by omega) eQ hBendK
  · have hc := center_eq_bot_of_mulEquiv_alternating_eni (L := ↥B ⧸ CFSG.pCore 2 ↥B)
      (n := 7) (by norm_num) eA7
    have eQ := (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientBot.trans eA7)
    exact not_fusionIsBenderGroup_of_mulEquiv_alternatingGroup (by norm_num) eQ hBendK

end CFSG.GroupTheory
