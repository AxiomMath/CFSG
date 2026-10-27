module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourData
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 Matrix

set_option linter.unusedSectionVars false


@[expose] def vElt : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8P4WW

@[expose] def cElt : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd cWord

theorem weylMatrix_wordProd_E8 (ω : List (Fin Tag.E8.rank)) :
    weylMatrix ((coxeterSystem Tag.E8).wordProd ω) = wordMat Tag.E8 ω := by
  ext i j
  rw [weylMatrix_apply, wordProd_smul_eq_wordMat_mulVec, Matrix.mulVec_single_one]
  rfl

theorem cElt_pow_five : cElt ^ 5 = 1 :=
  weylMatrix_injective (by
    rw [weylMatrix_pow, weylMatrix_one, cElt, weylMatrix_wordProd_E8]
    exact wordMat_cWord_pow_five)

theorem cElt_ne_one : cElt ≠ 1 := fun h => wordMat_cWord_ne_one (by
  have := congrArg weylMatrix h
  rw [weylMatrix_one, cElt, weylMatrix_wordProd_E8] at this
  exact this)

theorem vElt_mul_cElt : vElt * cElt = cElt * vElt :=
  weylMatrix_injective (by
    rw [weylMatrix_mul, weylMatrix_mul, vElt, cElt, weylMatrix_wordProd_E8,
      weylMatrix_wordProd_E8]
    exact wordMat_cWord_comm.symm)

theorem orderOf_cElt : orderOf cElt = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  orderOf_eq_prime cElt_pow_five cElt_ne_one

theorem card_zpowers_cElt : Nat.card (Subgroup.zpowers cElt) = 5 := by
  rw [Nat.card_zpowers, orderOf_cElt]

theorem cElt_mem_zpowers_of_ne_one {w : WeylGroup Tag.E8} (hw : w ∈ Subgroup.zpowers cElt)
    (hw1 : w ≠ 1) : cElt ∈ Subgroup.zpowers w := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h1 : (⟨w, hw⟩ : Subgroup.zpowers cElt) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have h2 := zpowers_eq_top_of_prime_card card_zpowers_cElt h1
  have h3 : (⟨cElt, Subgroup.mem_zpowers cElt⟩ : Subgroup.zpowers cElt) ∈
      Subgroup.zpowers (⟨w, hw⟩ : Subgroup.zpowers cElt) := by
    rw [h2]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h3
  exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩

theorem dualMatrix_cElt : dualMatrix (ZMod 5) cElt = cTrans := by
  rw [dualMatrix, cElt, weylMatrix_wordProd_E8]
  rfl

theorem cTrans_mulVec_eq_self {w : WeylGroup Tag.E8} (hw : w ∈ Subgroup.zpowers cElt)
    (hw1 : w ≠ 1) {z : Fin Tag.E8.rank → ZMod 5} (h : w ∈ dualWeylStabilizer z) :
    cTrans *ᵥ z = z := by
  have hc : cElt ∈ dualWeylStabilizer z :=
    (Subgroup.zpowers_le (H := dualWeylStabilizer z)).2 h (cElt_mem_zpowers_of_ne_one hw hw1)
  have h1 : (dualMatrix (ZMod 5) cElt) *ᵥ z = z := by
    refine eq_of_charVal_single (τ := Tag.E8) fun j => ?_
    rw [charVal_dualMatrix]
    exact mem_dualWeylStabilizer.1 hc _
  have h2 := congrArg
    (fun M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5) => M *ᵥ z) dualMatrix_cElt
  exact h2.symm.trans h1

theorem weylQuotientHom_eq_one_iff {τ : Tag} {R : Type} [Field R] {g : ModGL τ R}
    (hg : g ∈ monomialSubgroup τ R) : weylQuotientHom τ R ⟨g, hg⟩ = 1 ↔ g ∈ torusGroup τ R := by
  constructor
  · intro h
    obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets hg
    have hmaps : MapsRootLines g w := by
      rw [hgk]
      simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
    have hw : w = 1 := (weylQuotientHom_eq (g := ⟨g, hg⟩) hmaps).symm.trans h
    rw [hgk, hw, canonicalRep_one, mul_one]
    exact hk
  · intro hg'
    exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hg')

end Four

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
