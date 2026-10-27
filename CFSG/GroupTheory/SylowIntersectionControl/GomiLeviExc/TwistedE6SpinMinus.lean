module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Transfer
import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusModel
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDFrameE
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDKleinE
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDPairE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi

public section

namespace CFSG.GroupTheory.GomiLeviExc.TwistedE6

open Subgroup CFSG.Blueprint.Chevalley CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.Steinberg.TwistedE6

open CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.PartOne.CTP.SU4Even CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (isChevTwo_of_classicalTwoOrG2)
open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
  (isClassicalTwoOrG2_of_statedPOmegaMinus)
open scoped MatrixGroups

local instance twistedE6SpinMinusNeZeroRank : NeZero (Tag.rank .F4) := ⟨by decide⟩

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k} {q : ℕ}

omit [Finite k] [CharP k 2] q
  in
private theorem exists_ne_of_card_fixedField {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = (2 ^ f) ^ 2)
    (hF : Nat.card (fixedField θ) = 2 ^ f) : ∃ y : k, θ y ≠ y := by
  by_contra h
  push Not at h
  have hcard : Nat.card (fixedField θ) = Nat.card k :=
    Nat.card_congr
      { toFun := fun x => (x : k)
        invFun := fun y => ⟨y, h y⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => rfl }
  have h2 : 2 ^ f = (2 ^ f) ^ 2 := hF.symm.trans (hcard.trans hk)
  have hmul : 2 ^ f * 1 = 2 ^ f * 2 ^ f := by
    rw [mul_one]
    exact h2.trans (pow_two _)
  have hone : 1 = 2 ^ f := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos f) hmul
  have hlt : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega : f ≠ 0)
  omega

omit [CharP k 2] q
  in
private theorem theta_mem_unitaryGroup (hθ2 : ∀ c, θ (θ c) = c) [CharP (fixedField θ) 2]
    {b c : fixedField θ} (D : KleinDataEven (fixedField θ) k (involEquiv θ hθ2) b c)
    (hirr : ∀ s : fixedField θ, s ^ 2 + b * s + c ≠ 0)
    (s : spinGroup (quadMinus 3 (fixedField θ) b c)) :
    CompsPTwoDPairE.theta D hirr s ∈ unitaryGroup θ hθ2 := by
  have := CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  have htop := spinMinus6_blocks_sup_eq_top_even hirr
  change (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ at htop
  have hs : s ∈ (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range := by
    rw [htop]
    exact Subgroup.mem_top s
  have hle : (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range ≤
      (unitaryGroup θ hθ2).comap (CompsPTwoDPairE.theta D hirr) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_comap]
      have h := congrArg (fun f => f A)
        (CompsPTwoDPairE.theta_comp_lb (D := D) (hirr := hirr))
      simp only [MonoidHom.comp_apply] at h
      rw [h]
      show blockSL2 k 3 1 (Matrix.SpecialLinearGroup.map (algebraMap (fixedField θ) k) A) ∈
        unitaryGroup θ hθ2
      rw [Subfield.algebraMap_ofSubfield]
      exact ulbSL_mem θ hθ2 A
    · rintro _ ⟨B, rfl⟩
      rw [Subgroup.mem_comap]
      have hB : CompsPTwoDPairE.theta D hirr (shortBlock hirr 3 finOne B) ∈
          (usbSL (involEquiv θ hθ2).toRingHom (CompsPTwoDPairE.σσ' D)).range := by
        rw [← CompsPTwoDPairE.range_theta_sb (D := D) (hirr := hirr)]
        exact ⟨B, rfl⟩
      obtain ⟨B', hB'⟩ := hB
      rw [← hB']
      exact usbSL_mem (involEquiv θ hθ2).toRingHom (CompsPTwoDPairE.σσ' D) B'
  exact hle hs

omit [CharP k 2] q in
private theorem exists_spinMinus6_twistedE6 (hθ2 : ∀ c, θ (θ c) = c) [CharP (fixedField θ) 2]
    {b c : fixedField θ} [Fact (∀ r : fixedField θ, r ^ 2 ≠ -c + b * r)]
    (D : KleinDataEven (fixedField θ) k (involEquiv θ hθ2) b c)
    (hirr : ∀ s : fixedField θ, s ^ 2 + b * s + c ≠ 0) :
    ∃ Θ' : spinGroup (quadMinus 3 (fixedField θ) b c) →* fixedGroup k θ,
      Θ'.comp (minusLongBlock b c) = nodeHom1 θ ∧
        (shortBlock hirr 3 finOne).range.map Θ' = (nodeHom2 θ hθ2).range := by
  obtain ⟨emb, -, he1, he2⟩ := CFSG.ClassicalInvolution.WeakCT.exists_levi12 θ hθ2
  let Θr : spinGroup (quadMinus 3 (fixedField θ) b c) →* unitaryGroup θ hθ2 :=
    (CompsPTwoDPairE.theta D hirr).codRestrict (unitaryGroup θ hθ2)
      (theta_mem_unitaryGroup hθ2 D hirr)
  let Θ' : spinGroup (quadMinus 3 (fixedField θ) b c) →* fixedGroup k θ := emb.comp Θr
  have hlong : Θr.comp (minusLongBlock b c) = ulb θ hθ2 := by
    refine MonoidHom.ext fun A => Subtype.ext ?_
    change CompsPTwoDPairE.theta D hirr (minusLongBlock b c A) = ulbSL θ A
    have h := congrArg (fun f => f A)
      (CompsPTwoDPairE.theta_comp_lb (D := D) (hirr := hirr))
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    show blockSL2 k 3 1 (Matrix.SpecialLinearGroup.map (algebraMap (fixedField θ) k) A) =
      blockSL2 k 3 1 (liftSL θ 2 A)
    rw [Subfield.algebraMap_ofSubfield]
    rfl
  have hsb_u : (shortBlock hirr 3 finOne).range.map Θr = (usb θ hθ2).range := by
    apply Subgroup.map_injective (unitaryGroup θ hθ2).subtype_injective
    rw [Subgroup.map_map]
    have hcomp : (unitaryGroup θ hθ2).subtype.comp Θr = CompsPTwoDPairE.theta D hirr := by
      refine MonoidHom.ext fun s => rfl
    have husb : (unitaryGroup θ hθ2).subtype.comp (usb θ hθ2) =
        usbSL (involEquiv θ hθ2).toRingHom (CompsPTwoDPairE.σσ' D) := by
      refine MonoidHom.ext fun B => coe_usb θ hθ2 B
    rw [hcomp, ← MonoidHom.range_comp, ← MonoidHom.range_comp, husb]
    exact CompsPTwoDPairE.range_theta_sb (D := D) (hirr := hirr)
  refine ⟨Θ', ?_, ?_⟩
  · calc Θ'.comp (minusLongBlock b c)
        = emb.comp (Θr.comp (minusLongBlock b c)) := MonoidHom.comp_assoc _ _ _
      _ = emb.comp (ulb θ hθ2) := by rw [hlong]
      _ = nodeHom1 θ := he1
  · calc (shortBlock hirr 3 finOne).range.map Θ'
        = ((shortBlock hirr 3 finOne).range.map Θr).map emb := by
            rw [Subgroup.map_map]
      _ = (usb θ hθ2).range.map emb := by rw [hsb_u]
      _ = (emb.comp (usb θ hθ2)).range := (MonoidHom.range_comp _ _).symm
      _ = (nodeHom2 θ hθ2).range := by rw [he2]

omit [Finite k] [CharP k 2] q in
private theorem iSup_rankOne_eq_leviM_zero_one_two :
    (⨆ i : Fin 3, CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
        (nf i.val (by have := i.isLt; omega))) =
      leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))) := by
  refine le_antisymm (iSup_le fun i => rankOne_le_leviM ?_) ?_
  · fin_cases i
    · change (0 : Fin (Tag.rank .F4)) ∈ ({0, 1, 2} : Set (Fin (Tag.rank .F4)))
      decide
    · change (1 : Fin (Tag.rank .F4)) ∈ ({0, 1, 2} : Set (Fin (Tag.rank .F4)))
      decide
    · change (2 : Fin (Tag.rank .F4)) ∈ ({0, 1, 2} : Set (Fin (Tag.rank .F4)))
      decide
  · change (⨆ j ∈ ({0, 1, 2} : Set (Fin (Tag.rank .F4))),
        CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup j) ≤ _
    refine iSup₂_le fun j hj => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    rcases hj with rfl | rfl | rfl
    · exact le_iSup_of_le (0 : Fin 3) (le_of_eq (congrArg
        (fun i => CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup i)
        (Fin.ext rfl)))
    · exact le_iSup_of_le (1 : Fin 3) (le_of_eq (congrArg
        (fun i => CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup i)
        (Fin.ext rfl)))
    · exact le_iSup_of_le (2 : Fin 3) (le_of_eq (congrArg
        (fun i => CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup i)
        (Fin.ext rfl)))

omit [Finite k] [CharP k 2] q in
private theorem rankOne_le_leviM_zero_one_two (i : Fin 3) :
    CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
        (nf i.val (by have := i.isLt; omega)) ≤
      leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))) :=
  (le_iSup (fun j : Fin 3 => CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
    (nf j.val (by have := j.isLt; omega))) i).trans_eq iSup_rankOne_eq_leviM_zero_one_two

omit [CharP k 2] q in
private theorem mem_leviM_of_spinMinus6 (hθ2 : ∀ c, θ (θ c) = c) [CharP (fixedField θ) 2]
    {b c : fixedField θ} [Fact (∀ r : fixedField θ, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : fixedField θ, s ^ 2 + b * s + c ≠ 0)
    {Θ' : spinGroup (quadMinus 3 (fixedField θ) b c) →* fixedGroup k θ}
    (h1 : Θ'.comp (minusLongBlock b c) = nodeHom1 θ)
    (h2 : (shortBlock hirr 3 finOne).range.map Θ' = (nodeHom2 θ hθ2).range)
    (s : spinGroup (quadMinus 3 (fixedField θ) b c)) :
    Θ' s ∈ leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))) := by
  have htop := spinMinus6_blocks_sup_eq_top_even hirr
  change (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ at htop
  have hrange : Θ'.range = (nodeHom1 θ).range ⊔ (nodeHom2 θ hθ2).range := by
    rw [MonoidHom.range_eq_map Θ', ← htop, Subgroup.map_sup,
      MonoidHom.map_range Θ' (minusLongBlock b c), h1, h2]
  have hmem : Θ' s ∈ (nodeHom1 θ).range ⊔ (nodeHom2 θ hθ2).range := by
    rw [← hrange]
    exact ⟨s, rfl⟩
  have hle : (nodeHom1 θ).range ⊔ (nodeHom2 θ hθ2).range ≤
      leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))) := by
    refine sup_le ?_ ?_
    · rw [← rankOne_twistedE6_one θ]
      exact rankOne_le_leviM_zero_one_two 1
    · rw [← rankOne_twistedE6_two θ hθ2]
      exact rankOne_le_leviM_zero_one_two 2
  exact SetLike.le_def.mp hle hmem

omit [CharP k 2] q in
private theorem exists_sl3_zero_one :
    ∃ ψ : SL(3, fixedField θ) →* fixedGroup k θ,
      ψ.comp (blk (fixedField θ) 0) = nodeHom0 θ ∧ ψ.comp (blk (fixedField θ) 1) = nodeHom1 θ ∧
        ∀ g, ψ g ∈ leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))) := by
  obtain ⟨ψ, -, h0, h1⟩ := exists_levi01 θ
  refine ⟨ψ, h0, h1, fun g => ?_⟩
  have hrange : ψ.range = (nodeHom0 θ).range ⊔ (nodeHom1 θ).range := by
    rw [MonoidHom.range_eq_map ψ, ← B12_sup_B23 (K := fixedField θ), Subgroup.map_sup,
      show B12 (fixedField θ) = (blk (fixedField θ) 0).range from rfl,
      show B23 (fixedField θ) = (blk (fixedField θ) 1).range from rfl]
    rw [MonoidHom.map_range, MonoidHom.map_range, h0, h1]
  have hmem : ψ g ∈ ψ.range := ⟨g, rfl⟩
  rw [hrange] at hmem
  have hle : (nodeHom0 θ).range ⊔ (nodeHom1 θ).range ≤
      leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))) := by
    refine sup_le ?_ ?_
    · rw [← rankOne_twistedE6_zero θ]
      exact rankOne_le_leviM_zero_one_two 0
    · rw [← rankOne_twistedE6_one θ]
      exact rankOne_le_leviM_zero_one_two 1
  exact SetLike.le_def.mp hle hmem

omit [Finite k] [CharP k 2] q in
private theorem commute_subgroupOf_rankOne (hθ2 : ∀ c, θ (θ c) = c) (i j : Fin 3)
    (hij : i.val + 1 < j.val)
    (u : ↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))))
    (hu : u ∈ (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
      (nf i.val (by have := i.isLt; omega))).subgroupOf _)
    (v : ↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))))
    (hv : v ∈ (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
      (nf j.val (by have := j.isLt; omega))).subgroupOf _) :
    u * v = v * u := by
  have hi : i.val = 0 := by have := i.isLt; omega
  have hj : j.val = 2 := by have := j.isLt; omega
  have hu' : (u : fixedGroup k θ) ∈
      CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 0) := by
    have h := Subgroup.mem_subgroupOf.mp hu
    rwa [show nf i.val (by have := i.isLt; omega) = nf 0 from Fin.ext hi] at h
  have hv' : (v : fixedGroup k θ) ∈
      CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 2) := by
    have h := Subgroup.mem_subgroupOf.mp hv
    rwa [show nf j.val (by have := j.isLt; omega) = nf 2 from Fin.ext hj] at h
  apply Subtype.ext
  exact commute_rankOne_twistedE6_zero_two θ hθ2 (u : fixedGroup k θ) hu'
    (v : fixedGroup k θ) hv'

omit [Finite k] [CharP k 2] q in
private noncomputable def leviFrameRankOne :
    Fin (4 - 1) → Subgroup ↥(leviM (twistedDatum k θ)
      ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) :=
  fun i => (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
    (nf i.val (by have := i.isLt; omega))).subgroupOf
      (leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))))

omit q in
private noncomputable def leviFrameLongParam (ψ : SL(3, fixedField θ) →* fixedGroup k θ)
    (hψM : ∀ g, ψ g ∈ leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))))
    (i : Fin (4 - 2)) :
    SL(2, fixedField θ) →* ↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) :=
  (ψ.codRestrict _ hψM).comp (blk (fixedField θ) i)

omit [Finite k] [CharP k 2] q in
private theorem iSup_leviFrameRankOne_eq_top : (⨆ i, leviFrameRankOne (k := k) (θ := θ) i) = ⊤ := by
  refine le_antisymm le_top ?_
  let M := leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))
  let S : Fin 3 → Subgroup ↥(fixedGroup k θ) := fun i =>
    CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
      (nf i.val (by have := i.isLt; omega))
  have hM : (⨆ i : Fin 3, S i) = M := iSup_rankOne_eq_leviM_zero_one_two
  have hS : ∀ i, S i ≤ M := rankOne_le_leviM_zero_one_two
  have hjoin : (⨆ i : Fin 3, S i).subgroupOf M = ⨆ i : Fin 3, (S i).subgroupOf M :=
    CFSG.subgroupOf_iSup S hS
  calc
    ⊤ = M.subgroupOf M := (Subgroup.subgroupOf_self M).symm
    _ = (⨆ i : Fin 3, S i).subgroupOf M := by rw [hM]
    _ = ⨆ i : Fin 3, (S i).subgroupOf M := hjoin
    _ ≤ ⨆ j : Fin (4 - 1), leviFrameRankOne (k := k) (θ := θ) j :=
      iSup_le fun i => le_iSup (fun j : Fin (4 - 1) => leviFrameRankOne (k := k) (θ := θ) j)
        ⟨i.val, by omega⟩

omit [CharP k 2] q in
private theorem leviFrameTheta_shortBlock_range (hθ2 : ∀ c, θ (θ c) = c)
    [CharP (fixedField θ) 2] {b c : fixedField θ}
    [Fact (∀ r : fixedField θ, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : fixedField θ, s ^ 2 + b * s + c ≠ 0)
    {Θ' : spinGroup (quadMinus 3 (fixedField θ) b c) →* fixedGroup k θ}
    (h1 : Θ'.comp (minusLongBlock b c) = nodeHom1 θ)
    (h2 : (shortBlock hirr 3 finOne).range.map Θ' = (nodeHom2 θ hθ2).range) :
    (shortBlock hirr 3 finOne).range.map
        (Θ'.codRestrict (leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))))
          (mem_leviM_of_spinMinus6 hθ2 hirr h1 h2)) =
      leviFrameRankOne (k := k) (θ := θ) ⟨4 - 2, by omega⟩ := by
  change (shortBlock hirr 3 finOne).range.map
      (Θ'.codRestrict (leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))))
        (mem_leviM_of_spinMinus6 hθ2 hirr h1 h2)) =
    (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
      (nf 2 (by omega))).subgroupOf
      (leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))))
  rw [CFSG.map_codRestrict_eq_subgroupOf, h2,
    ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_two θ hθ2]

omit [CharP k 2] q in
private theorem leviFrameLongParam_one_eq_longBlock (hθ2 : ∀ c, θ (θ c) = c)
    [CharP (fixedField θ) 2]
    {b c : fixedField θ} [Fact (∀ r : fixedField θ, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : fixedField θ, s ^ 2 + b * s + c ≠ 0)
    {Θ' : spinGroup (quadMinus 3 (fixedField θ) b c) →* fixedGroup k θ}
    (h1 : Θ'.comp (minusLongBlock b c) = nodeHom1 θ)
    (h2 : (shortBlock hirr 3 finOne).range.map Θ' = (nodeHom2 θ hθ2).range)
    (ψ : SL(3, fixedField θ) →* fixedGroup k θ)
    (hψ1 : ψ.comp (blk (fixedField θ) 1) = nodeHom1 θ)
    (hψM : ∀ g, ψ g ∈ leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) :
    leviFrameLongParam ψ hψM ⟨4 - 2 - 1, by omega⟩ =
      (Θ'.codRestrict (leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))))
        (mem_leviM_of_spinMinus6 hθ2 hirr h1 h2)).comp (minusLongBlock b c) := by
  refine MonoidHom.ext fun A => Subtype.ext ?_
  show (ψ (blk (fixedField θ) 1 A) : fixedGroup k θ) = Θ' (minusLongBlock b c A)
  have hψ1A : ψ (blk (fixedField θ) 1 A) = nodeHom1 θ A := congrArg (fun φ => φ A) hψ1
  have h1A : Θ' (minusLongBlock b c A) = nodeHom1 θ A := congrArg (fun φ => φ A) h1
  rw [hψ1A, h1A]

omit [Finite k] [CharP k 2] q in
private theorem leviFrameLongParam_injective_and_range_of
    (ψ : SL(3, fixedField θ) →* fixedGroup k θ)
    (hψM : ∀ g, ψ g ∈ leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4))))
    (i : Fin (4 - 2)) {r : SL(2, fixedField θ) →* fixedGroup k θ}
    (hψ : ψ.comp (blk (fixedField θ) i) = r) (hr : Function.Injective r)
    (hU : CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
      (nf i.val (by have := i.isLt; omega)) = r.range) :
    Function.Injective (leviFrameLongParam ψ hψM i) ∧
      (leviFrameLongParam ψ hψM i).range =
        leviFrameRankOne (k := k) (θ := θ) ⟨i.val, by omega⟩ := by
  subst hψ
  refine ⟨fun x y h => hr (congrArg Subtype.val h), ?_⟩
  change ((ψ.codRestrict _ hψM).comp (blk (fixedField θ) i)).range =
    (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup
      (nf i.val (by have := i.isLt; omega))).subgroupOf _
  rw [hU, MonoidHom.range_comp, MonoidHom.range_comp, CFSG.map_codRestrict_eq_subgroupOf]

omit [Finite k] [CharP k 2] q in
private theorem leviFrameLongParam_injective_and_range (ψ : SL(3, fixedField θ) →* fixedGroup k θ)
    (hψ0 : ψ.comp (blk (fixedField θ) 0) = nodeHom0 θ)
    (hψ1 : ψ.comp (blk (fixedField θ) 1) = nodeHom1 θ)
    (hψM : ∀ g, ψ g ∈ leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) :
    ∀ i : Fin (4 - 2), Function.Injective (leviFrameLongParam ψ hψM i) ∧
      (leviFrameLongParam ψ hψM i).range =
        leviFrameRankOne (k := k) (θ := θ) ⟨i.val, by omega⟩ := by
  intro i
  fin_cases i
  · exact leviFrameLongParam_injective_and_range_of ψ hψM 0 hψ0 (rFixed_injective θ (nd 1) rfl)
      (rankOne_twistedE6_zero θ)
  · exact leviFrameLongParam_injective_and_range_of ψ hψM 1 hψ1 (rFixed_injective θ (nd 3) rfl)
      (rankOne_twistedE6_one θ)

omit [Finite k] [CharP k 2] q in
private theorem exists_sl3_leviFrameLongParam (ψ : SL(3, fixedField θ) →* fixedGroup k θ)
    (hψM : ∀ g, ψ g ∈ leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) :
    ∀ i j : Fin (4 - 2), i.val + 1 = j.val →
      ∃ ψ' : SL(3, fixedField θ) →* ↥(leviM (twistedDatum k θ)
        ({0, 1, 2} : Set (Fin (Tag.rank .F4)))),
        ψ'.comp (blk (fixedField θ) 0) = leviFrameLongParam ψ hψM i ∧
        ψ'.comp (blk (fixedField θ) 1) = leviFrameLongParam ψ hψM j := by
  intro i j hij
  fin_cases i
  all_goals fin_cases j
  all_goals simp at hij
  all_goals first | omega | exact ⟨ψ.codRestrict _ hψM, rfl, rfl⟩

omit [CharP k 2] q in
private theorem recognition_leviM_zero_one_two {f : ℕ} (hf : 1 ≤ f) (hθ2 : ∀ c, θ (θ c) = c)
    [CharP (fixedField θ) 2] (hF : Nat.card (fixedField θ) = 2 ^ f) {b c : fixedField θ}
    [Fact (∀ r : fixedField θ, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : fixedField θ, s ^ 2 + b * s + c ≠ 0)
    {Θ' : spinGroup (quadMinus 3 (fixedField θ) b c) →* fixedGroup k θ}
    (h1 : Θ'.comp (minusLongBlock b c) = nodeHom1 θ)
    (h2 : (shortBlock hirr 3 finOne).range.map Θ' = (nodeHom2 θ hθ2).range) :
    CFSG.IsQuasisimple ↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) ∧
      center ↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) = ⊥ ∧
      CFSG.Blueprint.LieModel (↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) ⧸
        center ↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))))
        .POmegaMinus 4 2 f := by
  classical
  let M := leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))
  have hmem : ∀ s, Θ' s ∈ M := mem_leviM_of_spinMinus6 hθ2 hirr h1 h2
  let θM : spinGroup (quadMinus 3 (fixedField θ) b c) →* ↥M := Θ'.codRestrict M hmem
  obtain ⟨ψ, hψ0, hψ1, hψM⟩ := exists_sl3_zero_one (k := k) (θ := θ)
  obtain ⟨Ψ, -, -, hq, hZ, hlie, -⟩ :=
    CompsPTwoDFrameE.weakCT_spinMinus_even_of_frame
      (n := 4) (f := f) ⟨Nat.prime_two, hf, le_rfl⟩ le_rfl (F := fixedField θ) hF
      (b := b) (c := c) hirr (U := leviFrameRankOne (k := k) (θ := θ))
      (hgen := iSup_leviFrameRankOne_eq_top) (hcomm := fun i j hij =>
        commute_subgroupOf_rankOne hθ2 i j hij)
      (θ := θM) (hθV := leviFrameTheta_shortBlock_range hθ2 hirr h1 h2)
      (ρ' := leviFrameLongParam ψ hψM)
      (hρ'₀ := leviFrameLongParam_one_eq_longBlock hθ2 hirr h1 h2 ψ hψ1 hψM)
      (hρ'U := leviFrameLongParam_injective_and_range ψ hψ0 hψ1 hψM)
      (hρ'ψ := exists_sl3_leviFrameLongParam ψ hψM)
  refine ⟨hq, ?_, hlie⟩
  rw [hZ, CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (n := 4)
    (by norm_num) hirr, Subgroup.map_bot]

theorem gomiLeviFactor_leviM_zero_one_two (hk : Nat.card k = q ^ 2) (hθ : ∀ c, θ c = c ^ q) :
    GomiLeviFactor ↥(leviM (twistedDatum k θ) ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) := by
  obtain ⟨f, hf, rfl⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hk
  have hθ2 : ∀ c, θ (θ c) = c :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card hk hθ
  have hF : Nat.card (fixedField θ) = 2 ^ f :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_fixedSubfield_of_card θ hk hθ
  have : CharP (fixedField θ) 2 :=
    RingHom.charP (fixedField θ).subtype (fixedField θ).subtype.injective 2
  obtain ⟨b, c, hirr, ⟨D⟩⟩ := CompsPTwoDKleinE.exists_kleinDataEven_of_fixed
    (F := fixedField θ) (involEquiv θ hθ2) hθ2 (fun r => r.2) (fun y hy => ⟨⟨y, hy⟩, rfl⟩)
    (exists_ne_of_card_fixedField hf hk hF)
  have := fact_shortField hirr
  obtain ⟨Θ', h1, h2⟩ := exists_spinMinus6_twistedE6 hθ2 D hirr
  obtain ⟨hq, hZ, ⟨-, hcl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ :=
    recognition_leviM_zero_one_two hf hθ2 hF hirr h1 h2
  · have := CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid k
    have : Finite ↥(fixedGroup k θ) := Subtype.finite
    refine gomiLeviFactor_of_injective hq ?_
      (isChevTwo_of_classicalTwoOrG2 (isClassicalTwoOrG2_of_statedPOmegaMinus hcl))
      (Subgroup.subtype _) (Subgroup.subtype_injective _) (Subgroup.range_subtype _)
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  all_goals omega

end CFSG.GroupTheory.GomiLeviExc.TwistedE6
