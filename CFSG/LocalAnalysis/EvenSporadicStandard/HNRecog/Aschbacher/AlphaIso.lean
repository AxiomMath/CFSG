module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.AlphaQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.LeCommutator

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.RankThree.Literature.FSmith

variable {C C' : Type} [Group C] [Group C'] [Finite C] [Finite C'] {Q : Subgroup C}
  {Q' : Subgroup C'} [hQn : Q.Normal] [hQn' : Q'.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))] [Module (ZMod 2) (Additive (Abelianization Q'))]

theorem AschbacherHyp.exists_isometry (hC : AschbacherHyp C Q) (hC' : AschbacherHyp C' Q')
    (α : ↥(commutator C) ≃* ↥(commutator C')) :
    ∃ a : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q'),
      (∀ v, extraspecialQuadForm hC'.plus.isExtraspecialPGroup (a v) =
        extraspecialQuadForm hC.plus.isExtraspecialPGroup v) ∧
      (∀ (l : ↥(commutator C)) (v : Additive (Abelianization Q)),
        a (conjLinEquiv hQn (l : C) v) =
          conjLinEquiv hQn' ((α l : ↥(commutator C')) : C') (a v)) ∧
      (∀ (l : ↥(commutator C)) (hl : (l : C) ∈ Q),
        a (Additive.ofMul (Abelianization.of (⟨(l : C), hl⟩ : Q))) =
          Additive.ofMul (Abelianization.of
            (⟨((α l : ↥(commutator C')) : C'), hC.map_mem_of_mem hC' α hl⟩ : Q'))) := by
  let f : Q →* Q' :=
    { toFun := fun x => ⟨(α ⟨x, hC.le_commutator x.2⟩ : C'),
        hC.map_mem_of_mem hC' α (l := ⟨x, hC.le_commutator x.2⟩) x.2⟩
      map_one' := by
        apply Subtype.ext
        show (α ⟨(1 : Q), hC.le_commutator (1 : Q).2⟩ : C') = (1 : C')
        have h1 : (⟨(1 : Q), hC.le_commutator (1 : Q).2⟩ : ↥(commutator C)) = 1 :=
          Subtype.ext rfl
        rw [h1, map_one]
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        show (α ⟨((x * y : Q)), hC.le_commutator (x * y).2⟩ : C') =
          (α ⟨x, hC.le_commutator x.2⟩ : C') * (α ⟨y, hC.le_commutator y.2⟩ : C')
        have hxy : (⟨((x * y : Q)), hC.le_commutator (x * y).2⟩ : ↥(commutator C)) =
            ⟨x, hC.le_commutator x.2⟩ * ⟨y, hC.le_commutator y.2⟩ := Subtype.ext rfl
        rw [hxy, map_mul]
        rfl }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : (⟨x, hC.le_commutator x.2⟩ : ↥(commutator C)) =
        ⟨y, hC.le_commutator y.2⟩ := by
      apply α.injective
      apply Subtype.ext
      have := congrArg (fun z : Q' => (z : C')) hxy
      simpa [f] using this
    exact Subtype.ext (congrArg (fun z : ↥(commutator C) => (z : C)) h)
  have hsurj : Function.Surjective f := by
    intro y
    let l : ↥(commutator C) := α.symm ⟨y, hC'.le_commutator y.2⟩
    have hl : (l : C) ∈ Q := by
      refine (hC.map_mem_iff hC' α l).1 ?_
      show ((α (α.symm ⟨y, hC'.le_commutator y.2⟩) : ↥(commutator C')) : C') ∈ Q'
      rw [MulEquiv.apply_symm_apply]
      exact y.2
    refine ⟨⟨(l : C), hl⟩, ?_⟩
    apply Subtype.ext
    show (α ⟨(l : C), hC.le_commutator hl⟩ : C') = (y : C')
    have hl' : (⟨(l : C), hC.le_commutator hl⟩ : ↥(commutator C)) = l :=
      Subtype.ext rfl
    rw [hl']
    show ((α l : ↥(commutator C')) : C') = (y : C')
    rw [show α l = ⟨y, hC'.le_commutator y.2⟩ from α.apply_symm_apply ⟨y, hC'.le_commutator y.2⟩]
  let φ : Q ≃* Q' := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have φ_apply : ∀ y : Q, (φ y : C') = (α ⟨y, hC.le_commutator y.2⟩ : C') := fun _ => rfl
  have φ_apply_Q : ∀ (l : ↥(commutator C)) (hl : (l : C) ∈ Q),
      φ ⟨(l : C), hl⟩ = ⟨(α l : C'), hC.map_mem_of_mem hC' α hl⟩ := by
    intro l hl
    apply Subtype.ext
    show (α ⟨(l : C), hC.le_commutator hl⟩ : C') = (α l : C')
    rw [show (⟨(l : C), hC.le_commutator hl⟩ : ↥(commutator C)) = l from Subtype.ext rfl]
  let aAdd : Additive (Abelianization Q) ≃+ Additive (Abelianization Q') :=
    (MulEquiv.abelianizationCongr φ).toAdditive
  let a : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q') :=
    aAdd.toLinearEquiv fun c v => ZMod.map_smul aAdd c v
  have a_of : ∀ x : Q, a (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (φ x)) := fun _ => rfl
  refine ⟨a, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [a_of x, extraspecialQuadForm_apply, extraspecialQuadForm_apply]
    have h : (φ x) ^ 2 = 1 ↔ x ^ 2 = 1 := by
      rw [← map_pow, MulEquiv.map_eq_one_iff]
    by_cases hx : x ^ 2 = 1
    · rw [if_pos hx, if_pos (h.mpr hx)]
    · rw [if_neg hx, if_neg (fun h' => hx (h.mp h'))]
  · intro l v
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    have key : (⟨conjAut hQn (l : C) x, hC.le_commutator (conjAut hQn (l : C) x).2⟩ :
        ↥(commutator C)) = l * ⟨x, hC.le_commutator x.2⟩ * l⁻¹ := by
      apply Subtype.ext
      simpa using conjAut_apply hQn (l : C) x
    have hconj : φ (conjAut hQn (l : C) x) =
        conjAut hQn' ((α l : ↥(commutator C')) : C') (φ x) := by
      apply Subtype.ext
      calc (φ (conjAut hQn (l : C) x) : C')
          = (α ⟨conjAut hQn (l : C) x,
                hC.le_commutator (conjAut hQn (l : C) x).2⟩ : C') := φ_apply _
        _ = ((α l * α ⟨x, hC.le_commutator x.2⟩ * (α l)⁻¹ : ↥(commutator C')) : C') := by
              rw [key, map_mul, map_mul, map_inv]
        _ = (conjAut hQn' ((α l : ↥(commutator C')) : C') (φ x) : C') := by
              rw [conjAut_apply, φ_apply x]
              rfl
    simp only [conjLinEquiv_apply, a_of, hconj]
  · intro l hl
    rw [a_of (⟨(l : C), hl⟩ : Q), φ_apply_Q l hl]

end CFSG.EvenSporadicStandard.HNRecog
