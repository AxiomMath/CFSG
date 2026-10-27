module

public import CFSG.LieType.Chevalley.E7Three.CentralizerComponent
public import CFSG.LieType.Chevalley.E7Three.FourCube

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KA5L CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.FourCube CFSG.LieType.Chevalley.E7Three.PauliWords
  CFSG.LieType.Chevalley.E7Three.Product

open scoped MatrixGroups Kronecker Pointwise

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] def diagSL2 : Kˣ →* SL(2, K) where
  toFun := HSL
  map_one' := Subtype.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [HSL])
  map_mul' s t := (CFSG.RankThree.PartOne.KLAY.HSL_mul_HSL s t).symm

theorem coe_kronSL2_HSL (t : Kˣ) :
    ((kronSL2 K (HSL t) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal ![(t : K), t, t, ((t⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K)] := by
  change reindex e6 e6 _ = _
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := e6.surjective p
  obtain ⟨⟨i', j'⟩, rfl⟩ := e6.surjective q
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    kroneckerMap_apply]
  obtain ⟨t00, t01, t02, t10, t11, t12⟩ := e6_table
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [t00, t01, t02, t10, t11, t12, HSL, Matrix.diagonal_apply, Matrix.one_apply]

theorem prod_hEntries (t : Kˣ) :
    hEntries 0 t * hEntries 1 (t ^ 2) * hEntries 2 (t ^ 3) * hEntries 3 (t ^ 2) * hEntries 4 t =
      ![(t : K), t, t, ((t⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K)] := by
  have ht : (t : K) ≠ 0 := t.ne_zero
  funext i
  fin_cases i <;> simp [hEntries] <;> field_simp

theorem kronSL2_HSL (t : Kˣ) :
    kronSL2 K (HSL t) = blockSL2 K 5 0 (HSL t) * blockSL2 K 5 1 (HSL (t ^ 2)) *
      blockSL2 K 5 2 (HSL (t ^ 3)) * blockSL2 K 5 3 (HSL (t ^ 2)) * blockSL2 K 5 4 (HSL t) := by
  apply Subtype.ext
  change ((kronSL2 K (HSL t) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = _
  simp only [coe_kronSL2_HSL, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_HSL,
    Matrix.diagonal_mul_diagonal']
  rw [← prod_hEntries]
  rfl

variable (K) in
@[expose] def fourTorus : Kˣ →* ModGL .E7 K := (cubeSL2 K).comp (diagSL2 K)

@[expose] def fourTorusExp : Fin Tag.E7.rank → ℤ := ![0, 0, -2, 0, 2, 0, 0]

theorem fourTorus_eq_rootDiagUnit (t : Kˣ) :
    fourTorus K t = rootDiagUnit .E7 fun i => t ^ fourTorusExp i := by
  change a5Frame K (kronSL2 K (HSL t)) = _
  rw [kronSL2_HSL, map_mul, map_mul, map_mul, map_mul, a5Frame_blockSL2_HSL,
    a5Frame_blockSL2_HSL, a5Frame_blockSL2_HSL, a5Frame_blockSL2_HSL, a5Frame_blockSL2_HSL,
    torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext l
  have key : ∀ l : Fin Tag.E7.rank, Tag.E7.cartan (a5chain 0) l + 2 * Tag.E7.cartan (a5chain 1) l +
      3 * Tag.E7.cartan (a5chain 2) l + 2 * Tag.E7.cartan (a5chain 3) l +
        Tag.E7.cartan (a5chain 4) l = fourTorusExp l := by
    decide +kernel
  simp only [Pi.mul_apply, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
  rw [← key l]
  congr 1
  all_goals (push_cast; ring)

theorem range_fourTorus_le_range_cubeSL2 : (fourTorus K).range ≤ (cubeSL2 K).range := by
  rintro _ ⟨t, rfl⟩
  exact ⟨HSL t, rfl⟩

theorem multiplicityWord_eq_fourTorus (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (Multiplicity.multiplicityWord ζ : ModGL .E7 K) = fourTorus K ζ := by
  rw [Multiplicity.multiplicityWord_val_product ζ hζ]
  change _ = a5Frame K (kronSL2 K (HSL ζ))
  rw [kronSL2_HSL, map_mul, map_mul, map_mul, map_mul, a5Frame_blockSL2_HSL,
    a5Frame_blockSL2_HSL, a5Frame_blockSL2_HSL, a5Frame_blockSL2_HSL, a5Frame_blockSL2_HSL, hζ,
    CFSG.Blueprint.Chevalley.torusElt_one, mul_one]
  rfl

theorem exists_HSL_of_commute {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {M : SL(2, K)}
    (h : M * HSL ζ = HSL ζ * M) : ∃ t : Kˣ, M = HSL t := by
  have hζK := IsPrimitiveRoot.coe_units_iff.2 hζ
  have hne : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := by
    intro he
    have h2 : (ζ : K) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [he]
      rw [Units.mul_inv]
    have := (hζK.pow_eq_one_iff_dvd 2).1 h2
    omega
  have hm : (M : Matrix (Fin 2) (Fin 2) K) * (HSL ζ : SL(2, K)) =
      ((HSL ζ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]
  have e := fun i j => congrFun (congrFun hm i) j
  have e01 : (M : Matrix (Fin 2) (Fin 2) K) 0 1 * ((ζ⁻¹ : Kˣ) : K) =
      (ζ : K) * (M : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    simpa [HSL, Matrix.mul_apply, Fin.sum_univ_two] using e 0 1
  have e10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 * (ζ : K) =
      ((ζ⁻¹ : Kˣ) : K) * (M : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simpa [HSL, Matrix.mul_apply, Fin.sum_univ_two] using e 1 0
  have h01 : (M : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have : (M : Matrix (Fin 2) (Fin 2) K) 0 1 * (((ζ⁻¹ : Kˣ) : K) - ζ) = 0 := by
      linear_combination e01
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hne
  have h10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have : (M : Matrix (Fin 2) (Fin 2) K) 1 0 * ((ζ : K) - ((ζ⁻¹ : Kˣ) : K)) = 0 := by
      linear_combination e10
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  have hdet : (M : Matrix (Fin 2) (Fin 2) K) 0 0 * (M : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have := M.2
    rw [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] at this
    exact this
  have h00 : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ h00, Subtype.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [HSL]
  · simp [HSL, h01]
  · simp [HSL, h10]
  · simp only [HSL, Units.val_inv_eq_inv_val, Units.val_mk0]
    simp
    field_simp
    linear_combination hdet

@[expose] def fourE (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : Subgroup (ModGL .E7 K) :=
  (fourCubeHom ζ hζ).range.map (adjointGroup .E7 K).subtype

@[expose] def fourCent (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : Subgroup (ModGL .E7 K) :=
  adjointGroup .E7 K ⊓ Subgroup.centralizer (fourE ζ hζ : Set (ModGL .E7 K))

theorem cubeE_le_fourE (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : cubeE ζ hζ ≤ fourE ζ hζ :=
  Subgroup.map_mono (cube_range_le_fourCube_range ζ hζ)

theorem multiplicityWord_mem_fourE (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (Multiplicity.multiplicityWord ζ : ModGL .E7 K) ∈ fourE ζ hζ := by
  have h1 : (1 : ZMod 3).val = 1 := by decide +kernel
  have hz : (fourCubeHom ζ hζ (1, Multiplicative.ofAdd (1 : ZMod 3)) : ModGL .E7 K) =
      Multiplicity.multiplicityWord ζ := by
    rw [fourCubeHom_apply, map_one, one_mul]
    simp [h1]
  rw [← hz]
  exact ⟨_, MonoidHom.mem_range.2 ⟨(1, Multiplicative.ofAdd (1 : ZMod 3)), rfl⟩, rfl⟩

theorem fourE_commute {ζ : Kˣ} {hζ : ζ ^ 3 = 1} {x y : ModGL .E7 K} (hx : x ∈ fourE ζ hζ)
    (hy : y ∈ fourE ζ hζ) : Commute x y := by
  obtain ⟨_, ⟨f, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨f', rfl⟩, rfl⟩ := hy
  change (fourCubeHom ζ hζ f : ModGL .E7 K) * fourCubeHom ζ hζ f' =
    fourCubeHom ζ hζ f' * fourCubeHom ζ hζ f
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm]

theorem mem_fourCent_iff {ζ : Kˣ} {hζ : ζ ^ 3 = 1} {g : ModGL .E7 K} :
    g ∈ fourCent ζ hζ ↔ g ∈ cubeCent ζ hζ ∧
      Commute g (Multiplicity.multiplicityWord ζ : ModGL .E7 K) := by
  constructor
  · rintro ⟨hG, hC⟩
    refine ⟨⟨hG, Subgroup.mem_centralizer_iff.2 fun x hx =>
      (Subgroup.mem_centralizer_iff.1 hC) x (cubeE_le_fourE ζ hζ hx)⟩, ?_⟩
    exact ((Subgroup.mem_centralizer_iff.1 hC) _ (multiplicityWord_mem_fourE ζ hζ)).symm
  · rintro ⟨⟨hG, hC⟩, hz⟩
    refine ⟨hG, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨_, ⟨f, rfl⟩, rfl⟩ := hx
    change (fourCubeHom ζ hζ f : ModGL .E7 K) * g = g * fourCubeHom ζ hζ f
    rw [fourCubeHom_apply, Subgroup.coe_mul, Subgroup.coe_pow]
    have h1 : Commute (cubeHom ζ hζ f.1 : ModGL .E7 K) g :=
      (Subgroup.mem_centralizer_iff.1 hC) _ ⟨_, ⟨f.1, rfl⟩, rfl⟩
    exact (h1.mul_left (hz.symm.pow_left _)).eq

theorem range_fourTorus_le_fourCent (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (fourTorus K).range ≤ fourCent ζ hζ := by
  rintro _ ⟨t, rfl⟩
  refine mem_fourCent_iff.2 ⟨range_cubeSL2_le_cubeCent ζ hζ
    (range_fourTorus_le_range_cubeSL2 ⟨t, rfl⟩), ?_⟩
  rw [multiplicityWord_eq_fourTorus ζ hζ, Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

theorem cubeE_le_fourCent (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : cubeE ζ hζ ≤ fourCent ζ hζ := fun _ hx =>
  mem_fourCent_iff.2 ⟨cubeE_le_cubeCent ζ hζ hx,
    fourE_commute (cubeE_le_fourE ζ hζ hx) (multiplicityWord_mem_fourE ζ hζ)⟩

section Steinberg

variable [IsAlgClosed K]

theorem fourCent_eq_sup {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    fourCent ζ hζ.pow_eq_one = (fourTorus K).range ⊔ cubeE ζ hζ.pow_eq_one := by
  refine le_antisymm ?_ (sup_le (range_fourTorus_le_fourCent ζ _) (cubeE_le_fourCent ζ _))
  intro g hg
  obtain ⟨hgC, hgz⟩ := mem_fourCent_iff.1 hg
  have hg' : g ∈ ((cubeSL2 K).range : Set (ModGL .E7 K)) *
      (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) := by
    rw [← coe_cubeCent_eq_mul hζ]
    exact hgC
  obtain ⟨_, ⟨M, rfl⟩, e, he, rfl⟩ := hg'
  have hez : Commute e (Multiplicity.multiplicityWord ζ : ModGL .E7 K) :=
    fourE_commute (cubeE_le_fourE ζ _ he) (multiplicityWord_mem_fourE ζ _)
  have hMz : Commute (cubeSL2 K M) (cubeSL2 K (HSL ζ)) := by
    have h3 := hgz.mul_left hez.inv_left
    rw [mul_inv_cancel_right, multiplicityWord_eq_fourTorus ζ hζ.pow_eq_one] at h3
    exact h3
  have hM : M * HSL ζ = HSL ζ * M := by
    apply cubeSL2_injective hζ
    rw [map_mul, map_mul]
    exact hMz.eq
  obtain ⟨t, rfl⟩ := exists_HSL_of_commute hζ hM
  exact mul_mem (Subgroup.mem_sup_left ⟨t, rfl⟩) (Subgroup.mem_sup_right he)

theorem fourCent_le_centralizer {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    fourCent ζ hζ.pow_eq_one ≤
      Subgroup.centralizer (fourCent ζ hζ.pow_eq_one : Set (ModGL .E7 K)) := by
  rw [fourCent_eq_sup hζ]
  have hT : (fourTorus K).range ≤
      Subgroup.centralizer ((fourTorus K).range : Set (ModGL .E7 K)) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hE : cubeE ζ hζ.pow_eq_one ≤
      Subgroup.centralizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) := fun _ hx _ hy =>
    (cubeE_commute hy hx).eq
  have hTE : (fourTorus K).range ≤
      Subgroup.centralizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) := fun _ hx =>
    Subgroup.centralizer_le (cubeE_le_fourE ζ _) (range_fourTorus_le_fourCent ζ _ hx).2
  exact sup_le (Subgroup.le_centralizer_iff.2 (sup_le hT (Subgroup.le_centralizer_iff.1 hTE)))
    (Subgroup.le_centralizer_iff.2 (sup_le hTE hE))

end Steinberg

end CFSG.LieType.Chevalley.E7Three.Centralizer
