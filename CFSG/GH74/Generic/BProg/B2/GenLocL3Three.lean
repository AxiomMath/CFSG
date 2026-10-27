module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3ThreeLoc
public import CFSG.GH74.Generic.BProg.B2.GenLocL3ThreeGen

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace GenLocL3Three

theorem isRank23_map_conj {J : Type} [Group J] (D : Subgroup (MulAut J)) (hD : IsRank23 ↥D)
    (β : MulAut J) : IsRank23 ↥(D.map (MulAut.conj β).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj β).toMonoidHom := (MulAut.conj β).injective
  let e := D.equivMapOfInjective (MulAut.conj β).toMonoidHom hinj
  refine ⟨GenLocBasic.isEA_of_surjective hD.1 e.toMonoidHom e.surjective, ?_⟩
  rw [← GenLocBasic.pRank_congr e]
  exact hD.2

theorem genOrLoc_frame_three (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3) (hD : IsRank23 ↥D) :
    gammaAct D.subtype = ⊤ ∨ (LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype) := by
  have h := GenLocBasic.card_eq_two_pow_pRank_type hD.1
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card ↥D = 4 := by rw [h, hr2]; norm_num
    exact Or.inl (gammaAct_subtype_rank2_three D hfs hD h4)
  · have h8 : Nat.card ↥D = 8 := by rw [h, hr3]; norm_num
    have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
    exact Or.inr ⟨locE1_three D hfs hD h8, locE2_three D hfs hD.1, locE3_three D hfs⟩

theorem genLocSub_three : GenLocSub P3 := by
  refine genLocSub_of_conj fun D hD => ?_
  obtain ⟨β, hβ⟩ := exists_conj_le_frameStab (p := 3) (f := 1) Nat.prime_three (by norm_num)
    (by simp) D hD.1
  exact ⟨β, genOrLoc_frame_three _ hβ (isRank23_map_conj D hD β)⟩

theorem genLoc_projectiveSL3_three : GenLoc P3 :=
  genLoc_of_genLocSub genLocSub_three

@[expose] def slCongr {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') : SL(3, K) ≃* SL(3, K') where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _

@[expose] def projectiveSLCongr {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') :
    LinearFlag.projectiveSL 3 K ≃* LinearFlag.projectiveSL 3 K' :=
  QuotientGroup.congr (LinearFlag.scalars 3 K) (LinearFlag.scalars 3 K') (slCongr e) (by
    rw [LinearFlag.scalars_eq_center, LinearFlag.scalars_eq_center]
    exact CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv (slCongr e))

end GenLocL3Three

theorem genLoc_psl3_three {J : Type} [Group J] (hJ : LieModel J .PSL 3 3 1) : GenLoc J := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hJ
  let ψ : J ≃* LinearFlag.projectiveSL 3 F :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  have hF3 : Nat.card F = 3 := by simpa using hF
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 3 := by rw [Fintype.card_eq_nat_card]; exact hF3
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hF'
  exact GenLoc.of_mulEquiv (ψ.trans (GenLocL3Three.projectiveSLCongr eF.symm)).symm
    GenLocL3Three.genLoc_projectiveSL3_three

theorem genLoc4_l3_three {J : Type} [Group J] (hJ : LieModel J .PSL 3 3 1) : GenLoc4 J :=
  (genLoc_psl3_three hJ).genLoc4

end CFSG.GH74.Generic.BProg.B2
