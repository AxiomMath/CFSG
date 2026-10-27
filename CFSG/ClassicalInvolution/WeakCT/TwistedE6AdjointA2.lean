module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.Timmesfeld
  CFSG.RankThree.Classical2 CFSG.RankThree.E6 CFSG.RankThree.PartOne.KLCE
  CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.RankThree.PartOne.TCX.E
open scoped MatrixGroups

variable {k : Type} [Field k] [Finite k] [CharP k 2]


omit [Finite k] in
private lemma e6Sign_single_eq_one (a : Fin (Tag.rank .E6)) :
    (e6Sign (Pi.single a 1) : k) = 1 := by
  have h := e6Sign_mul_self (K := k) (Pi.single a 1)
  rcases (mul_self_eq_one_iff.mp h) with h1 | h1
  · exact h1
  · rw [h1, neg_one_eq_one_iff.mpr (ringChar.eq k 2)]

omit [Finite k]
  in
private lemma pinnedSign_smul_single (a : Fin (Tag.rank .E6)) (z : k) :
    (pinnedData Tag.E6 (Pi.single a 1)).2.2 • z = z := by
  rcases pinnedSign_eq Tag.E6 (Pi.single a 1) with h | h
  · rw [h, one_smul]
  · rw [h, neg_one_smul]
    exact CFSG.ClassicalGroups.Orthogonal.neg_eq_self_of_two_eq_zero
      (CharTwo.two_eq_zero (R := k)) z

theorem e6IsogenyT_comp_e6Rank1 (a : Fin (Tag.rank .E6)) :
    (adjointGroup TwistTag.E6.tag k).subtype.comp
      ((e6IsogenyT k).comp (e6Rank1 k a)) =
    rootSL2 Tag.E6 k (Pi.single a 1) := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · change (adjointGroup TwistTag.E6.tag k).subtype
      (e6IsogenyT k (e6Rank1 k a (tv 0 1 c))) =
      rootSL2 Tag.E6 k (Pi.single a 1) (tv 0 1 c)
    rw [e6Rank1_tv01]
    change ((e6IsogenyT k (e6Data_valid.xm k (Pi.single a 1) c) :
        adjointGroup TwistTag.E6.tag k) : ModGL TwistTag.E6.tag k) = _
    rw [coe_e6Isogeny_xm (IsRoot.basis a)]
    rw [tv01_eq_uSL (F := k), rootSL2_uSL_eq]
    rw [e6Sign_single_eq_one, one_mul]
    exact congrArg (pinnedX Tag.E6 k (Pi.single a 1))
      (by rw [pinnedSign_smul_single])
  · change (adjointGroup TwistTag.E6.tag k).subtype
      (e6IsogenyT k (e6Rank1 k a (tv 1 0 c))) =
      rootSL2 Tag.E6 k (Pi.single a 1) (tv 1 0 c)
    rw [e6Rank1_tv10]
    change ((e6IsogenyT k (e6Data_valid.xm k (-Pi.single a 1) c) :
        adjointGroup TwistTag.E6.tag k) : ModGL TwistTag.E6.tag k) = _
    rw [coe_e6Isogeny_xm (IsRoot.neg (IsRoot.basis a))]
    rw [tv10_eq_vSL (F := k)]
    obtain ⟨ε, hε, hroot⟩ := exists_rootSL2_vSL_eq (K := k) (τ := Tag.E6)
      (β := Pi.single a 1) (IsRoot.basis a)
    rw [hroot]
    have hε1 : ε = 1 := by
      rcases (mul_self_eq_one_iff.mp hε) with h | h
      · exact h
      · rw [h, neg_one_eq_one_iff.mpr (ringChar.eq k 2)]
    have hs : (e6Sign (-Pi.single a 1) : k) = 1 := by
      have h := e6Sign_mul_self (K := k) (-Pi.single a 1)
      rcases (mul_self_eq_one_iff.mp h) with h1 | h1
      · exact h1
      · rw [h1, neg_one_eq_one_iff.mpr (ringChar.eq k 2)]
    rw [hε1, hs]
    rfl

omit [Finite k]
  in
private lemma e6rhoA2₁_comp_blk0 :
    (e6rhoA2₁ k).comp (blk k 0) = rootSL2 Tag.E6 k (Pi.single 0 1) := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · change e6rhoA2₁ k (blk k 0 (tv 0 1 c)) =
      rootSL2 Tag.E6 k (Pi.single 0 1) (tv 0 1 c)
    rw [blk_zero_tv01]
    obtain ⟨s, hs, hρ⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := k) (i := 0) (j := 1) (by decide)
    have hs1 : (s : k) = 1 := by
      rcases hs with h | h
      · rw [h]; norm_num
      · rw [h]
        norm_num
        exact neg_one_eq_one_iff.mpr (ringChar.eq k 2)
    have h : e6rhoA2₁ k
        (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide) c) =
        pinnedX Tag.E6 k (chainRoot chain13 0 1) ((s : k) * c) := by
      have hsymm : (a2Equiv₁ k).symm
          (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide) c) =
          ⟨pinnedX Tag.E6 k (chainRoot chain13 0 1) ((s : k) * c),
            pinnedX_chainRoot13_mem (by decide) _⟩ := by
        rw [MulEquiv.symm_apply_eq]
        refine Subtype.ext ?_
        rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, hs1, one_mul]
        rw [Matrix.SpecialLinearGroup.transvection_coe, one_mul]
      simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [hsymm]
    change e6rhoA2₁ k
      (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide) c) =
      rootSL2 Tag.E6 k (Pi.single 0 1) (tv 0 1 c)
    rw [h, e6_base_01, hs1, one_mul, tv01_eq_uSL (F := k), rootSL2_uSL_eq]
    exact congrArg (pinnedX Tag.E6 k (Pi.single 0 1))
      (by rw [pinnedSign_smul_single])
  · change e6rhoA2₁ k (blk k 0 (tv 1 0 c)) =
      rootSL2 Tag.E6 k (Pi.single 0 1) (tv 1 0 c)
    rw [blk_zero_tv10]
    obtain ⟨s, hs, hρ⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := k) (i := 1) (j := 0) (by decide)
    have hs1 : (s : k) = 1 := by
      rcases hs with h | h
      · rw [h]; norm_num
      · rw [h]
        norm_num
        exact neg_one_eq_one_iff.mpr (ringChar.eq k 2)
    have h : e6rhoA2₁ k
        (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide) c) =
        pinnedX Tag.E6 k (chainRoot chain13 1 0) ((s : k) * c) := by
      have hsymm : (a2Equiv₁ k).symm
          (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide) c) =
          ⟨pinnedX Tag.E6 k (chainRoot chain13 1 0) ((s : k) * c),
            pinnedX_chainRoot13_mem (by decide) _⟩ := by
        rw [MulEquiv.symm_apply_eq]
        refine Subtype.ext ?_
        rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, hs1, one_mul]
        rw [Matrix.SpecialLinearGroup.transvection_coe, one_mul]
      simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [hsymm]
    change e6rhoA2₁ k
      (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide) c) =
      rootSL2 Tag.E6 k (Pi.single 0 1) (tv 1 0 c)
    rw [h, chainRoot_swap, e6_base_01, hs1, one_mul, tv10_eq_vSL (F := k)]
    obtain ⟨ε, hε, hroot⟩ := exists_rootSL2_vSL_eq (K := k) (τ := Tag.E6)
      (β := Pi.single 0 1) (IsRoot.basis 0)
    rw [hroot]
    have hε1 : ε = 1 := by
      rcases (mul_self_eq_one_iff.mp hε) with h | h
      · exact h
      · rw [h, neg_one_eq_one_iff.mpr (ringChar.eq k 2)]
    rw [hε1, one_mul]

omit [Finite k]
  in
private lemma e6rhoA2₁_comp_blk1 :
    (e6rhoA2₁ k).comp (blk k 1) = rootSL2 Tag.E6 k (Pi.single 2 1) := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · change e6rhoA2₁ k (blk k 1 (tv 0 1 c)) =
      rootSL2 Tag.E6 k (Pi.single 2 1) (tv 0 1 c)
    rw [blk_one_tv01]
    obtain ⟨s, hs, hρ⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := k) (i := 1) (j := 2) (by decide)
    have hs1 : (s : k) = 1 := by
      rcases hs with h | h
      · rw [h]; norm_num
      · rw [h]
        norm_num
        exact neg_one_eq_one_iff.mpr (ringChar.eq k 2)
    have h : e6rhoA2₁ k
        (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) c) =
        pinnedX Tag.E6 k (chainRoot chain13 1 2) ((s : k) * c) := by
      have hsymm : (a2Equiv₁ k).symm
          (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) c) =
          ⟨pinnedX Tag.E6 k (chainRoot chain13 1 2) ((s : k) * c),
            pinnedX_chainRoot13_mem (by decide) _⟩ := by
        rw [MulEquiv.symm_apply_eq]
        refine Subtype.ext ?_
        rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, hs1, one_mul]
        rw [Matrix.SpecialLinearGroup.transvection_coe, one_mul]
      simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [hsymm]
    change e6rhoA2₁ k
      (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) c) =
      rootSL2 Tag.E6 k (Pi.single 2 1) (tv 0 1 c)
    rw [h, e6_base_12, hs1, one_mul, tv01_eq_uSL (F := k), rootSL2_uSL_eq]
    exact congrArg (pinnedX Tag.E6 k (Pi.single 2 1))
      (by rw [pinnedSign_smul_single])
  · change e6rhoA2₁ k (blk k 1 (tv 1 0 c)) =
      rootSL2 Tag.E6 k (Pi.single 2 1) (tv 1 0 c)
    rw [blk_one_tv10]
    obtain ⟨s, hs, hρ⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := k) (i := 2) (j := 1) (by decide)
    have hs1 : (s : k) = 1 := by
      rcases hs with h | h
      · rw [h]; norm_num
      · rw [h]
        norm_num
        exact neg_one_eq_one_iff.mpr (ringChar.eq k 2)
    have h : e6rhoA2₁ k
        (Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) c) =
        pinnedX Tag.E6 k (chainRoot chain13 2 1) ((s : k) * c) := by
      have hsymm : (a2Equiv₁ k).symm
          (Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) c) =
          ⟨pinnedX Tag.E6 k (chainRoot chain13 2 1) ((s : k) * c),
            pinnedX_chainRoot13_mem (by decide) _⟩ := by
        rw [MulEquiv.symm_apply_eq]
        refine Subtype.ext ?_
        rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, hs1, one_mul]
        rw [Matrix.SpecialLinearGroup.transvection_coe, one_mul]
      simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [hsymm]
    change e6rhoA2₁ k
      (Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) c) =
      rootSL2 Tag.E6 k (Pi.single 2 1) (tv 1 0 c)
    rw [h, chainRoot_swap, e6_base_12, hs1, one_mul, tv10_eq_vSL (F := k)]
    obtain ⟨ε, hε, hroot⟩ := exists_rootSL2_vSL_eq (K := k) (τ := Tag.E6)
      (β := Pi.single 2 1) (IsRoot.basis 2)
    rw [hroot]
    have hε1 : ε = 1 := by
      rcases (mul_self_eq_one_iff.mp hε) with h | h
      · exact h
      · rw [h, neg_one_eq_one_iff.mpr (ringChar.eq k 2)]
    rw [hε1, one_mul]

theorem exists_e6Sl3_adjoint_frame :
    ∃ (Ψ : SL(3, k) →* e6Data_valid.minGroup k)
      (ρ : SL(3, k) →* adjointGroup TwistTag.E6.tag k),
      Function.Injective Ψ ∧ Function.Injective ρ ∧
      ρ = (e6IsogenyT k).comp Ψ ∧
      IsA2Frame ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ)
        (fun i j => chainRoot chain13 i j) ∧
      ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ) =
        e6rhoA2₁ k ∧
      ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ).comp (blk k 0) =
        rootSL2 Tag.E6 k (Pi.single 0 1) ∧
      ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ).comp (blk k 1) =
        rootSL2 Tag.E6 k (Pi.single 2 1) := by
  obtain ⟨Ψ, hΨinj, hΨ0, hΨ1⟩ :=
    exists_e6Sl3 (k := k) (a := 0) (b := 2) (by decide) (by decide) (by decide)
  let ρ : SL(3, k) →* adjointGroup TwistTag.E6.tag k := (e6IsogenyT k).comp Ψ
  have hρM0 : ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ).comp (blk k 0) =
      rootSL2 Tag.E6 k (Pi.single 0 1) := by
    rw [MonoidHom.comp_assoc]
    change (adjointGroup TwistTag.E6.tag k).subtype.comp
      ((e6IsogenyT k).comp (Ψ.comp (blk k 0))) = rootSL2 Tag.E6 k (Pi.single 0 1)
    rw [hΨ0]
    exact e6IsogenyT_comp_e6Rank1 0
  have hρM1 : ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ).comp (blk k 1) =
      rootSL2 Tag.E6 k (Pi.single 2 1) := by
    rw [MonoidHom.comp_assoc]
    change (adjointGroup TwistTag.E6.tag k).subtype.comp
      ((e6IsogenyT k).comp (Ψ.comp (blk k 1))) = rootSL2 Tag.E6 k (Pi.single 2 1)
    rw [hΨ1]
    exact e6IsogenyT_comp_e6Rank1 2
  have heq : (adjointGroup TwistTag.E6.tag k).subtype.comp ρ = e6rhoA2₁ k := by
    refine hom_ext_sl3 ?_ ?_
    · exact hρM0.trans (e6rhoA2₁_comp_blk0).symm
    · exact hρM1.trans (e6rhoA2₁_comp_blk1).symm
  have hρinj : Function.Injective ρ := by
    intro A B h
    apply e6rhoA2₁_injective
    have h2 : ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ) A =
        ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ) B := congrArg Subtype.val h
    rw [heq] at h2
    exact h2
  have hfr : IsA2Frame ((adjointGroup TwistTag.E6.tag k).subtype.comp ρ)
      (fun i j => chainRoot chain13 i j) := by
    rw [heq]
    exact e6_base_frame
  exact ⟨Ψ, ρ, hΨinj, hρinj, rfl, hfr, heq, hρM0, hρM1⟩

end CFSG.ClassicalInvolution.WeakCT

end
