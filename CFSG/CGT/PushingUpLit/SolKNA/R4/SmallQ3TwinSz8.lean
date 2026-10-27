module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3TwinBase
public import CFSG.ClassicalInvolution.Q3.TA3Twin3Sz8

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.TA3.Twin3 QuaternionGroup

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_sz8_q8
    (hd : TightDatum R S t) (hq : Q8Emb R t)
    (hH : TwinFr.TwinHyp (genFittingFStar Y) R S t)
    (hS : GH74.E2.Shape2Sz8 ↥(genFittingFStar Y)) : False := by
  set L := genFittingFStar Y
  have : L.Normal := genFittingFStar_normal Y
  have hperf : Group.IsPerfect L := hS.1.1
  obtain ⟨ι, -, -, ht⟩ := hq
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

end CFSG.CGT.PushingUpLit.SolKNA.R4
