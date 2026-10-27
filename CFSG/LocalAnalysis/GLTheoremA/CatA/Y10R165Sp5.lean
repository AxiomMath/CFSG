module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

namespace SpEngine

open Matrix

theorem exists_elemAbelian_qTorus_of_mulEquiv {F J : Type} [Field F] [Finite F] [CharP F 2]
    [Group J] [Finite J] {s q : ℕ} (hq : q.Prime) (hs : 3 ≤ s)
    (e : J ≃* StatedSp s F) (hdvd : q ∣ Nat.card F - 1) :
    ∃ Q : Subgroup J, IsElemAbelian q Q ∧ 3 ≤ CFSG.Open.pRank q Q := by
  let Q₀ : Subgroup (StatedSp s F) := symplecticQTorus (F := F) (ℓ := s) q
  have hQ₀ : IsElemAbelian q Q₀ := isElemAbelian_symplecticQTorus hq
  have hcard : Nat.card Q₀ = q ^ s := card_symplecticQTorus hq hdvd
  refine ⟨Q₀.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hQ₀ _, ?_⟩
  have hrank : CFSG.Open.pRank q (Q₀.map e.symm.toMonoidHom) =
      CFSG.Open.pRank q Q₀ := by
    have htop : (⊤ : Subgroup Q₀).map (e.symm.toMonoidHom.comp Q₀.subtype) =
        Q₀.map e.symm.toMonoidHom := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← htop, CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q₀]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt _
      (fun x y h => Subtype.ext (e.symm.injective h)) ⊤
  rw [hrank]
  have hle := CFSG.SectionRank.le_pRank hq.one_lt (H := Q₀) (E := Q₀)
    le_rfl hQ₀ (k := s) hcard
  omega

section PlaneThree

variable {F : Type} [Field F] [CharP F 2]

open Matrix
open CFSG.RankThree.SubgroupLists (spForm spForm_apply spForm_self spTrans spTrans_mulVec
  gl_ext_mulVec mem_statedSp_iff_preserves)

@[expose] noncomputable def planeThreeLin (s : ℕ) (i : Fin s) :
    (Fin s ⊕ Fin s → F) ≃ₗ[F] (Fin s ⊕ Fin s → F) where
  toFun x := fun j =>
    match j with
    | Sum.inl k => if k = i then x (Sum.inr i) else x (Sum.inl k)
    | Sum.inr k => if k = i then x (Sum.inl i) + x (Sum.inr i) else x (Sum.inr k)
  invFun x := fun j =>
    match j with
    | Sum.inl k => if k = i then x (Sum.inl i) + x (Sum.inr i) else x (Sum.inl k)
    | Sum.inr k => if k = i then x (Sum.inl i) else x (Sum.inr k)
  left_inv x := by
    funext j
    rcases j with k | k <;> by_cases h : k = i <;>
      simp only [h, if_true, if_false] <;> ring_nf <;> simp [CharTwo.two_eq_zero]
  right_inv x := by
    funext j
    rcases j with k | k <;> by_cases h : k = i <;>
      simp only [h, if_true, if_false] <;> ring_nf <;> simp [CharTwo.two_eq_zero]
  map_add' x y := by
    funext j
    rcases j with k | k <;> by_cases h : k = i <;>
      simp only [h, if_true, if_false, Pi.add_apply] <;> ring_nf <;> simp [CharTwo.two_eq_zero]
  map_smul' c x := by
    funext j
    rcases j with k | k <;> by_cases h : k = i <;>
      simp only [h, if_true, if_false, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring_nf

theorem planeThreeLin_apply_inl {s : ℕ} (i k : Fin s) (x : Fin s ⊕ Fin s → F) :
    planeThreeLin (F := F) s i x (Sum.inl k) =
      if k = i then x (Sum.inr i) else x (Sum.inl k) := rfl

theorem planeThreeLin_apply_inr {s : ℕ} (i k : Fin s) (x : Fin s ⊕ Fin s → F) :
    planeThreeLin (F := F) s i x (Sum.inr k) =
      if k = i then x (Sum.inl i) + x (Sum.inr i) else x (Sum.inr k) := rfl

theorem planeThreeLin_isometry {s : ℕ} (i : Fin s) (x y : Fin s ⊕ Fin s → F) :
    spForm s F (planeThreeLin (F := F) s i x) (planeThreeLin (F := F) s i y) =
      spForm s F x y := by
  rw [spForm_apply, spForm_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = i
  · rw [h]
    simp only [planeThreeLin_apply_inl, planeThreeLin_apply_inr, if_pos rfl, if_true]
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (x (Sum.inr i) * y (Sum.inr i)) * h2
  · simp only [planeThreeLin_apply_inl, planeThreeLin_apply_inr, if_neg h]

@[expose] noncomputable def planeThree (s : ℕ) (i : Fin s) : StatedSp s F :=
  ⟨Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (planeThreeLin (F := F) s i)), by
    rw [mem_statedSp_iff_preserves]
    intro x y
    have hx : ∀ x : Fin s ⊕ Fin s → F,
        (((Matrix.GeneralLinearGroup.toLin.symm
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (planeThreeLin (F := F) s i)) :
            GL (Fin s ⊕ Fin s) F) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) F) *ᵥ x =
          planeThreeLin (F := F) s i x) := by
      intro x
      rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.toLin_apply,
        MulEquiv.apply_symm_apply]
      rfl
    rw [hx, hx]
    exact planeThreeLin_isometry i x y⟩

@[expose] noncomputable def planeThreeMat (s : ℕ) (i : Fin s) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) F :=
  ↑(planeThree (F := F) s i : GL (Fin s ⊕ Fin s) F)

theorem planeThree_mulVec {s : ℕ} (i : Fin s) (x : Fin s ⊕ Fin s → F) :
    planeThreeMat (F := F) s i *ᵥ x =
      fun j =>
        match j with
        | Sum.inl k => if k = i then x (Sum.inr i) else x (Sum.inl k)
        | Sum.inr k => if k = i then x (Sum.inl i) + x (Sum.inr i) else x (Sum.inr k) := by
  change (↑(Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (planeThreeLin (F := F) s i)) :
        Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) F)) *ᵥ x = _
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin,
    MulEquiv.apply_symm_apply]
  rfl

theorem planeThree_apply_inl {s : ℕ} (i k : Fin s) (x : Fin s ⊕ Fin s → F) :
    (planeThreeMat (F := F) s i *ᵥ x) (Sum.inl k) =
      if k = i then x (Sum.inr i) else x (Sum.inl k) := by
  rw [planeThree_mulVec]

theorem planeThree_apply_inr {s : ℕ} (i k : Fin s) (x : Fin s ⊕ Fin s → F) :
    (planeThreeMat (F := F) s i *ᵥ x) (Sum.inr k) =
      if k = i then x (Sum.inl i) + x (Sum.inr i) else x (Sum.inr k) := by
  rw [planeThree_mulVec]

theorem generalLinearEquiv_toLin_planeThree {s : ℕ} (i : Fin s) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin s ⊕ Fin s → F)
        (Matrix.GeneralLinearGroup.toLin (planeThree (F := F) s i)) =
      planeThreeLin (F := F) s i := by
  change LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin s ⊕ Fin s → F)
    (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (planeThreeLin (F := F) s i)))) =
    planeThreeLin (F := F) s i
  rw [MulEquiv.apply_symm_apply]
  exact MulEquiv.apply_symm_apply _ _

theorem planeThree_pow_three {s : ℕ} (i : Fin s) :
    planeThree (F := F) s i ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  refine (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin s ⊕ Fin s → F))).injective ?_
  rw [map_pow, map_one, MulEquiv.trans_apply, generalLinearEquiv_toLin_planeThree]
  refine LinearEquiv.ext fun x => ?_
  change planeThreeLin (F := F) s i (planeThreeLin (F := F) s i
    (planeThreeLin (F := F) s i x)) = x
  funext j
  rcases j with k | k <;> by_cases h : k = i <;>
    simp only [planeThreeLin_apply_inl, planeThreeLin_apply_inr, h, if_true, if_false]
  all_goals first
    | rfl
    | (linear_combination x (Sum.inr i) * (CharTwo.two_eq_zero : (2 : F) = 0))
    | (linear_combination (x (Sum.inl i) + x (Sum.inr i)) *
        (CharTwo.two_eq_zero : (2 : F) = 0))
    | (linear_combination x (Sum.inl i) * (CharTwo.two_eq_zero : (2 : F) = 0))

theorem planeThree_ne_one {s : ℕ} (i : Fin s) : planeThree (F := F) s i ≠ 1 := by
  intro h
  have h1 : (planeThreeMat (F := F) s i *ᵥ Pi.single (Sum.inl i) 1) (Sum.inl i) =
      (((((1 : StatedSp s F) : GL (Fin s ⊕ Fin s) F) :
        Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) F) *ᵥ Pi.single (Sum.inl i) 1) (Sum.inl i)) := by
    rw [planeThreeMat]
    rw [h]
  rw [planeThree_apply_inl] at h1
  simp at h1

theorem planeThree_commute {s : ℕ} {i j : Fin s} (hij : i ≠ j) :
    planeThree (F := F) s i * planeThree (F := F) s j =
      planeThree (F := F) s j * planeThree (F := F) s i := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  refine (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin s ⊕ Fin s → F))).injective ?_
  rw [map_mul, map_mul, MulEquiv.trans_apply, MulEquiv.trans_apply,
    generalLinearEquiv_toLin_planeThree, generalLinearEquiv_toLin_planeThree]
  refine LinearEquiv.ext fun x => ?_
  funext k
  rcases k with k | k <;> by_cases h : k = i <;> by_cases h' : k = j <;>
    simp only [LinearEquiv.mul_apply, planeThreeLin_apply_inl, planeThreeLin_apply_inr, h, h',
      hij, Ne.symm hij, if_true, if_false]
  all_goals first
    | rfl
    | (linear_combination x (Sum.inr i) * (CharTwo.two_eq_zero : (2 : F) = 0))
    | (linear_combination x (Sum.inl i) * (CharTwo.two_eq_zero : (2 : F) = 0))
    | (linear_combination (x (Sum.inl i) + x (Sum.inr i)) *
        (CharTwo.two_eq_zero : (2 : F) = 0))

theorem planeThree_single_inl {s : ℕ} (i : Fin s) :
    planeThreeMat (F := F) s i *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inr i) 1 := by
  funext k
  rcases k with k | k
  · rw [planeThree_apply_inl]
    by_cases h : k = i
    · subst h; simp
    · rw [if_neg h]; simp [Pi.single_apply, h, Ne.symm h]
  · rw [planeThree_apply_inr]
    by_cases h : k = i
    · subst h; simp
    · rw [if_neg h]; simp [Pi.single_apply, h, Ne.symm h]

theorem planeThree_sq_single_inl {s : ℕ} (i : Fin s) :
    planeThreeMat (F := F) s i ^ 2 *ᵥ Pi.single (Sum.inl i) 1 =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, planeThree_single_inl]
  funext k
  rcases k with k | k
  · rw [planeThree_apply_inl]
    by_cases h : k = i
    · subst h; simp
    · rw [if_neg h]; simp [Pi.single_apply, h, Ne.symm h]
  · rw [planeThree_apply_inr]
    by_cases h : k = i
    · subst h; simp
    · rw [if_neg h]; simp [Pi.single_apply, h, Ne.symm h]

theorem planeThree_apply_single_inl_of_ne {s : ℕ} {i j : Fin s} (hij : i ≠ j) :
    planeThreeMat (F := F) s j *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1 := by
  funext m
  rcases m with m | m
  · rw [planeThree_apply_inl]
    by_cases hm : m = j
    · subst hm
      simp [Pi.single_apply, Ne.symm hij]
    · simp [Pi.single_apply, hm]
  · rw [planeThree_apply_inr]
    by_cases hm : m = j
    · subst hm
      simp [Pi.single_apply, Ne.symm hij]
    · simp [Pi.single_apply, hm]

end PlaneThree

end SpEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
