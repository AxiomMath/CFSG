module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3FiveLocE23

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial GenLocL3NineR3
open scoped MatrixGroups

namespace GenLocL3Five

theorem genOrLoc_frame_five
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5))) (hfs : D ≤ frameStab 3 K5) (hD : IsRank23 ↥D) :
    gammaAct D.subtype = ⊤ ∨ (LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype) := by
  have hfin : Finite ↥D := inferInstance
  have h := GenLocBasic.card_eq_two_pow_pRank_type hD.1
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card ↥D = 4 := by rw [h, hr2]; norm_num
    exact Or.inl (gammaAct_subtype_rank2 card_K5 D hfs hD h4)
  · have h8 : Nat.card ↥D = 8 := by rw [h, hr3]; norm_num
    by_cases hS : ShapeE5 D
    · exact Or.inr ⟨locE1_of_shapeE5 D hfs hD h8 hS, locE2_five D hfs hD.1, locE3_five D hfs⟩
    · exact Or.inl (rank3_gen card_K5 D hfs hD h8 hS)

theorem isRank23_map_conj {J : Type} [Group J] (D : Subgroup (MulAut J)) (hD : IsRank23 ↥D)
    (β : MulAut J) : IsRank23 ↥(D.map (MulAut.conj β).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj β).toMonoidHom := (MulAut.conj β).injective
  let e := D.equivMapOfInjective (MulAut.conj β).toMonoidHom hinj
  refine ⟨GenLocBasic.isEA_of_surjective hD.1 e.toMonoidHom e.surjective, ?_⟩
  rw [← GenLocBasic.pRank_congr e]
  exact hD.2

theorem genLocSub_five : GenLocSub (LinearFlag.projectiveSL 3 K5) := by
  refine genLocSub_of_conj fun D hD => ?_
  obtain ⟨β, hβ⟩ := exists_conj_le_frameStab (p := 5) (f := 1) Nat.prime_five (by norm_num)
    (by simp) D hD.1
  exact ⟨β, genOrLoc_frame_five _ hβ (isRank23_map_conj D hD β)⟩

theorem genLoc_projectiveSL3_five :
    GenLoc (LinearFlag.projectiveSL 3 K5) :=
  genLoc_of_genLocSub genLocSub_five

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

end GenLocL3Five

section PSL3

theorem genLoc_psl3_five {J : Type} [Group J] {p f : ℕ} (h5 : p ^ f = 5)
    (hJ : LieModel J .PSL 3 p f) : GenLoc J := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hJ
  let ψ : J ≃* LinearFlag.projectiveSL 3 F :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  have hF5 : Nat.card F = 5 := hF.trans h5
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 5 := by rw [Fintype.card_eq_nat_card]; exact hF5
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_five hF'
  exact GenLoc.of_mulEquiv (ψ.trans (GenLocL3Five.projectiveSLCongr eF.symm)).symm
    GenLocL3Five.genLoc_projectiveSL3_five

end PSL3

end CFSG.GH74.Generic.BProg.B2
