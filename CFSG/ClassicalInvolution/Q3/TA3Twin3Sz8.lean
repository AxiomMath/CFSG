module

public import CFSG.ClassicalInvolution.Q3.TA3Twin3Core
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinDefs
public import CFSG.GH74.KGroups.Cover
public import CFSG.GH74.KGroups.CoverSz8
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightRoot
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.TA3SOLCore
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreRank
public import CFSG.ClassicalInvolution.Q3.TA3SmallBase
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinReduce
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSL4
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSp4
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.GH74.Generic.Shapes
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

namespace Twin3

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_of_inducedHom_inner {L : Subgroup Y} [L.Normal] (hperf : Group.IsPerfect L)
    (hcent : ∀ y : Y, (∀ l ∈ L, y * l = l * y) → y ∈ L) {y : Y} {k : L}
    (hk : ∀ x, GH74.KGroups.inducedHom (MulAut.conjNormal y) x =
      (k : L ⧸ Subgroup.center L) * x * (k : L ⧸ Subgroup.center L)⁻¹) : y ∈ L := by
  have h1 : GH74.KGroups.inducedHom (MulAut.conjNormal y) =
      GH74.KGroups.inducedHom (MulAut.conj k) := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hk, GH74.KGroups.inducedHom_mk, MulAut.conj_apply]
    rfl
  have h2 := GH74.KGroups.inducedHom_injective hperf h1
  have hc : ∀ l ∈ L, ((k : Y)⁻¹ * y) * l = l * ((k : Y)⁻¹ * y) := by
    intro l hl
    have h3 := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : Y)) h2
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h3
    calc (k : Y)⁻¹ * y * l = (k : Y)⁻¹ * (y * l * y⁻¹) * y := by group
      _ = (k : Y)⁻¹ * ((k : Y) * l * (k : Y)⁻¹) * y := by rw [h3]
      _ = l * ((k : Y)⁻¹ * y) := by group
  have := L.mul_mem k.2 (hcent _ hc)
  rwa [mul_inv_cancel_left] at this

omit [Finite Y] in
theorem mem_of_two_power
    {L : Subgroup Y} [L.Normal] (hperf : Group.IsPerfect L)
    (hcent : ∀ y : Y, (∀ l ∈ L, y * l = l * y) → y ∈ L)
    (hS : LieModel (L ⧸ Subgroup.center L) .twistedB2 0 2 3) {y : Y} {n : ℕ}
    (hy : y ^ 2 ^ n = 1) : y ∈ L := by
  have hψ : GH74.KGroups.inducedHom (MulAut.conjNormal (H := L) y) ^ 2 ^ n = 1 := by
    rw [← map_pow, ← map_pow, hy, map_one, map_one]
  obtain ⟨k, hk⟩ := GH74.KGroups.Sz8.out_inner hS _ n hψ
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
  exact mem_of_inducedHom_inner hperf hcent hk

end Twin3

open Twin3 QuaternionGroup in
theorem twin2Sz8Leaf_holds : Twin2Sz8Leaf := by
  intro Y _ _ _ _ hsmall hS R S t hd hc hE2 _ _ _ _
  exfalso
  have hH := TwinFr.twinHyp_fstar hd hc hE2 hsmall
  set L := genFittingFStar Y
  have : L.Normal := genFittingFStar_normal Y
  have hperf : Group.IsPerfect L := hS.1.1
  obtain ⟨ι, -, -, ht⟩ := exists_q8_hom hd hc
  have hq8 : ∀ q : QuaternionGroup 2, q ^ 2 ^ 3 = 1 := by decide
  have hmem : ∀ q, ι q ∈ L := fun q =>
    mem_of_two_power hperf hH.cent hS.2.2 (by rw [← map_pow, hq8, map_one])
  let ι' : QuaternionGroup 2 →* L ⧸ Subgroup.center L :=
    (QuotientGroup.mk' (Subgroup.center L)).comp (ι.codRestrict L hmem)
  have hT : ι' (a 2) ≠ 1 := by
    intro h
    have hz := (QuotientGroup.eq_one_iff _).1 h
    obtain ⟨l, hl, hlt⟩ := hH.not_central
    apply hlt
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩)
    simpa [ht] using this
  have hQ8 : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num)
  have h2 : IsPGroup 2 ι'.range := hQ8.of_surjective ι'.rangeRestrict ι'.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := h2.exists_le_sylow
  obtain ⟨e₀⟩ := GH74.KGroups.CoverSz8.equiv_sz_of_lieModel hS.2.2
  have hmodel : CFSG.Theory.Comparator.SzModel 1 = Sz 1 := by
    simp only [CFSG.Open.Sz, CFSG.Open.SzGenerators, CFSG.Theory.Comparator.SzModel,
      CFSG.Theory.Comparator.SzGenerators]
  have hF := ProperTwoGeneratedCore.Lemma37.szEightSylowFacts_of_mulEquiv
    (e₀.trans (MulEquiv.subgroupCongr hmodel).symm) P
  have hsq : ∀ q : QuaternionGroup 2, q ^ 2 = a 2 → ∀ hq : ι' q ∈ (P : Subgroup _),
      (⟨ι' q, hq⟩ : (P : Subgroup _)) ^ 2 = ⟨ι' (a 2), hP ⟨_, rfl⟩⟩ := fun q h hq =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow, ← map_pow, h])
  have hi := hsq (a 1) (by decide) (hP ⟨_, rfl⟩)
  have hj := hsq (xa 0) (by decide) (hP ⟨_, rfl⟩)
  have hij := hF.comm_of_sq_eq _ _ (hi.trans hj.symm)
    (by rw [hi]; exact fun h => hT (congrArg Subtype.val h))
  have hc' : ι' (a 1 * xa 0) = ι' (xa 0 * a 1) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val hij
  rw [show (xa 0 * a 1 : QuaternionGroup 2) = a 2 * (a 1 * xa 0) by decide, map_mul ι' (a 2)] at hc'
  exact hT (mul_right_cancel (hc'.symm.trans (one_mul _).symm))

end CFSG.ClassicalInvolution.Q3.TA3
