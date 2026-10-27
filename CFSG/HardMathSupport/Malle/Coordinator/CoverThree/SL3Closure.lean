module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.RankThree.PartOne.CTP.SeitzDiag
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open scoped MatrixGroups
open Matrix

section Diagonal

variable {F : Type} [Field F]

theorem eq_top_of_transvections (S : Subgroup SL(3, F))
    (h : ∀ a b : Fin 3, ∀ hab : a ≠ b, ∀ c : F,
      Matrix.SpecialLinearGroup.transvection hab c ∈ S) : S = ⊤ := by
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, b, hab, c, rfl⟩
    exact h a b hab c
  rw [CFSG.LinearGroups.special_linear_elementary_generation] at hle
  exact top_unique hle

theorem transvection_mul_comm_of_diag {X : SL(3, F)}
    (hX : ∀ i j : Fin 3, i ≠ j → (X : Matrix (Fin 3) (Fin 3) F) i j = 0) {a b : Fin 3}
    (hab : a ≠ b) (h : (X : Matrix (Fin 3) (Fin 3) F) a a = (X : Matrix (Fin 3) (Fin 3) F) b b)
    (c : F) :
    Matrix.SpecialLinearGroup.transvection hab c * X = X * Matrix.SpecialLinearGroup.transvection hab c := by
  have h01 := hX 0 1 (by decide)
  have h02 := hX 0 2 (by decide)
  have h10 := hX 1 0 (by decide)
  have h12 := hX 1 2 (by decide)
  have h20 := hX 2 0 (by decide)
  have h21 := hX 2 1 (by decide)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  fin_cases a <;> fin_cases b <;> (try exact absurd rfl hab) <;>
    (fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.single_apply] <;> (try ring))

def diagEntry (P : Subgroup SL(3, F))
    (hdiag : ∀ x ∈ P, ∀ i j : Fin 3, i ≠ j → (x : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (i : Fin 3) : P →* F where
  toFun x := (x : Matrix (Fin 3) (Fin 3) F) i i
  map_one' := by simp
  map_mul' x y := by
    have hx := hdiag x x.2
    have hy := hdiag y y.2
    change ((x : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F)) i i = _
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> simp [hx 0 1 (by decide), hx 0 2 (by decide), hx 1 0 (by decide),
      hx 1 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide)]

theorem diagEntry_pow_eq (P : Subgroup SL(3, F))
    (hdiag : ∀ x ∈ P, ∀ i j : Fin 3, i ≠ j → (x : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center SL(3, F)) (x : P) (i j : Fin 3) :
    (diagEntry P hdiag i x) ^ 3 = (diagEntry P hdiag j x) ^ 3 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hP3 x x.2)
  have h1 : ((((x : SL(3, F)) ^ 3 : SL(3, F))) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) r := hr.symm
  have h : ∀ k : Fin 3, (diagEntry P hdiag k x) ^ 3 = r := by
    intro k
    rw [← map_pow]
    have h2 : (diagEntry P hdiag k (x ^ 3)) =
        ((((x : SL(3, F)) ^ 3 : SL(3, F))) : Matrix (Fin 3) (Fin 3) F) k k := rfl
    rw [h2, h1]
    simp
  rw [h i, h j]

theorem exists_noncentral_equal_entries [Finite F] (P : Subgroup SL(3, F))
    (hdiag : ∀ x ∈ P, ∀ i j : Fin 3, i ≠ j → (x : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (hP : Nat.card P = 27)
    (hPZ : Nat.card (P ⊓ Subgroup.center SL(3, F) : Subgroup SL(3, F)) = 3)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center SL(3, F)) (a b : Fin 3) :
    ∃ x ∈ P, x ∉ Subgroup.center SL(3, F) ∧
      (x : Matrix (Fin 3) (Fin 3) F) a a = (x : Matrix (Fin 3) (Fin 3) F) b b := by
  classical
  let ρ : P →* Fˣ := (diagEntry P hdiag a).toHomUnits / (diagEntry P hdiag b).toHomUnits
  have hρ : ∀ x, ρ x = 1 → diagEntry P hdiag a x = diagEntry P hdiag b x := by
    intro x hx
    have h1 : ((diagEntry P hdiag a).toHomUnits x : F) = (diagEntry P hdiag b).toHomUnits x := by
      have : (diagEntry P hdiag a).toHomUnits x / (diagEntry P hdiag b).toHomUnits x = 1 := hx
      rw [div_eq_one] at this
      rw [this]
    simpa using h1
  have hrange : Nat.card ρ.range ≤ 3 := by
    have hle : ρ.range ≤ rootsOfUnity 3 F := by
      rintro _ ⟨x, rfl⟩
      rw [mem_rootsOfUnity]
      have hx : ((diagEntry P hdiag a).toHomUnits x) ^ 3 =
          ((diagEntry P hdiag b).toHomUnits x) ^ 3 :=
        Units.ext (diagEntry_pow_eq P hdiag hP3 x a b)
      show ((diagEntry P hdiag a).toHomUnits x / (diagEntry P hdiag b).toHomUnits x) ^ 3 = 1
      rw [div_pow, hx, div_self']
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity F 3)
  have hidx : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hker9 : 9 ≤ Nat.card ρ.ker := by
    have h := ρ.ker.card_mul_index
    rw [hP, hidx] at h
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    by_contra hlt
    push Not at hlt
    nlinarith
  by_contra hcon
  push Not at hcon
  have hsub : ρ.ker.map P.subtype ≤ P ⊓ Subgroup.center SL(3, F) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    by_contra hnc
    exact hcon x x.2 hnc (hρ x hx)
  have hle3 : Nat.card (ρ.ker.map P.subtype) ≤ 3 := by
    have h := Subgroup.card_le_of_le hsub
    omega
  rw [Subgroup.card_map_of_injective P.subtype_injective] at hle3
  omega

theorem closure_centralizers_eq_top_of_diag [Finite F] (P : Subgroup SL(3, F))
    (hdiag : ∀ x ∈ P, ∀ i j : Fin 3, i ≠ j → (x : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (hP : Nat.card P = 27)
    (hPZ : Nat.card (P ⊓ Subgroup.center SL(3, F) : Subgroup SL(3, F)) = 3)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center SL(3, F)) :
    Subgroup.closure {g : SL(3, F) | ∃ x ∈ P, x ∉ Subgroup.center SL(3, F) ∧ g * x = x * g} =
      ⊤ := by
  apply eq_top_of_transvections
  intro a b hab c
  obtain ⟨x, hxP, hxc, hxe⟩ := exists_noncentral_equal_entries P hdiag hP hPZ hP3 a b
  exact Subgroup.subset_closure ⟨x, hxP, hxc,
    transvection_mul_comm_of_diag (hdiag x hxP) hab hxe c⟩

end Diagonal

section Conjugation

variable {G H : Type*} [Group G] [Group H]

theorem mem_center_map_iff (φ : G ≃* H) (x : G) :
    φ x ∈ Subgroup.center H ↔ x ∈ Subgroup.center G := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    have := h (φ y)
    rw [← map_mul, ← map_mul] at this
    exact φ.injective this
  · intro h y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, h y']

theorem closure_centralizers_map (φ : G ≃* H) (P : Subgroup G) :
    Subgroup.closure {g : H | ∃ x ∈ P.map φ.toMonoidHom, x ∉ Subgroup.center H ∧ g * x = x * g} =
      (Subgroup.closure {g : G | ∃ x ∈ P, x ∉ Subgroup.center G ∧ g * x = x * g}).map
        φ.toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, hxP, rfl⟩, hxc, hg⟩
    refine ⟨φ.symm g, ⟨x, hxP, fun hc => hxc ((mem_center_map_iff φ x).2 hc), ?_⟩, by simp⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hg
  · rintro ⟨g', ⟨x, hxP, hxc, hg⟩, rfl⟩
    refine ⟨φ x, ⟨x, hxP, rfl⟩, fun hc => hxc ((mem_center_map_iff φ x).1 hc), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hg]

theorem map_inf_center (φ : G ≃* H) (P : Subgroup G) :
    P.map φ.toMonoidHom ⊓ Subgroup.center H =
      (P ⊓ Subgroup.center G).map φ.toMonoidHom := by
  ext y
  constructor
  · rintro ⟨⟨x, hxP, rfl⟩, hc⟩
    exact ⟨x, ⟨hxP, (mem_center_map_iff φ x).1 hc⟩, rfl⟩
  · rintro ⟨x, ⟨hxP, hxc⟩, rfl⟩
    exact ⟨⟨x, hxP, rfl⟩, (mem_center_map_iff φ x).2 hxc⟩

end Conjugation

section Diagonalization

open CFSG.RankThree.PartOne.CTP

theorem exists_conj_diagonal_of_pow_eq_one {F : Type*} [Field F] {n m : ℕ} [NeZero m] {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (E : Subgroup (GL (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ m = 1) :
    ∃ g : GL (Fin n) F, ∀ x ∈ E, ∀ i j : Fin n, i ≠ j →
      ((g * x * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
  have hp : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let T : E → Module.End F (Fin n → F) := fun x =>
    Matrix.toLinAlgEquiv' ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hTcomm : ∀ x y, Commute (T x) (T y) := fun x y => by
    have h := congrArg Units.val (hcomm x x.2 y y.2)
    simp only [Units.val_mul] at h
    change Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _ =
      Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _
    rw [← map_mul, ← map_mul, h]
  have hTpow : ∀ x, T x ^ m = 1 := fun x => by
    change Matrix.toLinAlgEquiv' _ ^ m = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hexp x x.2, Units.val_one, map_one]
  have hss : ∀ x, (T x).IsSemisimple := fun x =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero (SeitzDiag.squarefree_X_pow_sub_one hζ)
      (by simp [hTpow x])
  have hdiag : ∀ x, ⨆ μ, (T x).eigenspace μ = ⊤ := fun x =>
    SeitzDiag.iSup_eigenspace_eq_top_of_pow_eq_one hp hζ (T x) (hTpow x)
  have hspan := SeitzDiag.span_commonEigenvectors_eq_top T hTcomm hss hdiag
  obtain ⟨B, hB⟩ :=
    SeitzDiag.exists_basis_subset_of_span_eq_top (Module.finrank_fin_fun F) _ hspan
  let e := Pi.basisFun F (Fin n)
  obtain ⟨g, hg, hginv⟩ : ∃ g : GL (Fin n) F, (g : Matrix (Fin n) (Fin n) F) = B.toMatrix e ∧
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = e.toMatrix B :=
    ⟨⟨B.toMatrix e, e.toMatrix B, B.toMatrix_mul_toMatrix_flip e,
      e.toMatrix_mul_toMatrix_flip B⟩, rfl, rfl⟩
  refine ⟨g, fun x hx i j hij => ?_⟩
  have h1 : ((g * x * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      LinearMap.toMatrix B B (T ⟨x, hx⟩) := by
    have h2 : LinearMap.toMatrix e e (T ⟨x, hx⟩) = (x : Matrix (Fin n) (Fin n) F) :=
      LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix B e B e (T ⟨x, hx⟩), h2,
      Units.val_mul, Units.val_mul, hg, hginv]
  rw [h1, LinearMap.toMatrix_apply]
  obtain ⟨μ, hμ⟩ := hB j ⟨x, hx⟩
  rw [hμ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_of_ne hij, smul_zero]

end Diagonalization

section ToSL

variable {F : Type} [Field F]

theorem exists_sl_conj_diag (P : Subgroup SL(3, F)) {m : ℕ} [NeZero m] {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hexp : ∀ x ∈ P, x ^ m = 1) :
    ∃ γ : SL(3, F), ∀ x ∈ P, ∀ i j : Fin 3, i ≠ j →
      ((γ * x * γ⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  classical
  let E : Subgroup (GL (Fin 3) F) := P.map Matrix.SpecialLinearGroup.toGL
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hexpE : ∀ x ∈ E, x ^ m = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  obtain ⟨g, hg⟩ := exists_conj_diagonal_of_pow_eq_one hζ E hcommE hexpE
  set d : Fˣ := Matrix.GeneralLinearGroup.det g with hd
  set G : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) F) with hG
  set N : Matrix (Fin 3) (Fin 3) F := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hN
  set D : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![((d⁻¹ : Fˣ) : F), 1, 1] with hD
  set D' : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![(d : F), 1, 1] with hD'
  have hGN : G * N = 1 := by rw [hG, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDD' : D * D' = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext k
    fin_cases k <;> simp
  have hdetG : G.det = d := by
    rw [hG, hd]
    rfl
  have hne : (d : F) ≠ 0 := d.ne_zero
  have hdetN : N.det = ((d⁻¹ : Fˣ) : F) := by
    have h1 : G.det * N.det = 1 := by rw [← Matrix.det_mul, hGN, Matrix.det_one]
    rw [hdetG] at h1
    rw [Units.val_inv_eq_inv_val]
    field_simp at h1 ⊢
    linear_combination h1
  have hdetD : D.det = ((d⁻¹ : Fˣ) : F) := by
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  have hdetD' : D'.det = (d : F) := by
    rw [hD', Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  let γ : SL(3, F) := ⟨D * G, by rw [Matrix.det_mul, hdetD, hdetG]; exact Units.inv_mul d⟩
  let δ : SL(3, F) := ⟨N * D', by rw [Matrix.det_mul, hdetN, hdetD']; exact Units.inv_mul d⟩
  have hγδ : γ * δ = 1 := by
    apply Subtype.ext
    change D * G * (N * D') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc G, hGN, Matrix.one_mul, hDD']
  have hinv : γ⁻¹ = δ := inv_eq_of_mul_eq_one_right hγδ
  refine ⟨γ, fun x hx i j hij => ?_⟩
  have hY := hg (Matrix.SpecialLinearGroup.toGL x) ⟨x, hx, rfl⟩ i j hij
  rw [hinv]
  have hmat : ((γ * x * δ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      D * ((g * Matrix.SpecialLinearGroup.toGL x * g⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * D' := by
    change D * G * (x : Matrix (Fin 3) (Fin 3) F) * (N * D') = _
    rw [Units.val_mul, Units.val_mul]
    change _ = D * (G * (x : Matrix (Fin 3) (Fin 3) F) * N) * D'
    simp only [Matrix.mul_assoc]
  rw [hmat, hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul, hY]
  simp

theorem exists_primitiveRoot_nine [Finite F] (h9 : 9 ∣ Nat.card F - 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ 9 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    intro h0
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hdvd : 9 ∣ orderOf g := hg ▸ h9
  have hord := orderOf_pow_orderOf_div hne hdvd
  refine ⟨((g ^ (orderOf g / 9) : Fˣ) : F), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff]
  have := IsPrimitiveRoot.orderOf (g ^ (orderOf g / 9))
  rwa [hord] at this

theorem pow_nine_eq_one_of_cube_central (x : SL(3, F)) (hx : x ^ 3 ∈ Subgroup.center SL(3, F)) :
    x ^ 9 = 1 := by
  obtain ⟨r, hr, hr'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hr3 : r ^ 3 = 1 := by simpa using hr
  apply Subtype.ext
  rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, Matrix.SpecialLinearGroup.coe_pow, ← hr', ← map_pow,
    hr3, map_one]
  rfl

theorem sl3_closure_centralizers [Finite F] (h9 : 9 ∣ Nat.card F - 1) (P : Subgroup SL(3, F))
    (hPc : IsMulCommutative P) (hP : Nat.card P = 27)
    (hPZ : Nat.card (P ⊓ Subgroup.center SL(3, F) : Subgroup SL(3, F)) = 3)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center SL(3, F)) :
    Subgroup.closure {g : SL(3, F) | ∃ x ∈ P, x ∉ Subgroup.center SL(3, F) ∧ g * x = x * g} =
      ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_nine h9
  have : NeZero 9 := ⟨by norm_num⟩
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hPc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨γ, hγ⟩ := exists_sl_conj_diag P hζ hcomm
    (fun x hx => pow_nine_eq_one_of_cube_central x (hP3 x hx))
  let φ : SL(3, F) ≃* SL(3, F) := MulAut.conj γ
  have hdiag : ∀ x ∈ P.map φ.toMonoidHom, ∀ i j : Fin 3, i ≠ j →
      (x : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
    rintro _ ⟨x, hx, rfl⟩ i j hij
    exact hγ x hx i j hij
  have hcard : Nat.card (P.map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hP
  have hcardZ : Nat.card (P.map φ.toMonoidHom ⊓ Subgroup.center SL(3, F) :
      Subgroup SL(3, F)) = 3 := by
    rw [map_inf_center, Subgroup.card_map_of_injective φ.injective]
    exact hPZ
  have hcube : ∀ x ∈ P.map φ.toMonoidHom, x ^ 3 ∈ Subgroup.center SL(3, F) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow]
    exact (mem_center_map_iff φ _).2 (hP3 x hx)
  have htop := closure_centralizers_eq_top_of_diag (P.map φ.toMonoidHom) hdiag hcard hcardZ hcube
  rw [closure_centralizers_map φ P] at htop
  refine eq_top_iff.2 fun g _ => ?_
  have hg : φ g ∈ (Subgroup.closure {g : SL(3, F) | ∃ x ∈ P, x ∉ Subgroup.center SL(3, F) ∧
      g * x = x * g}).map φ.toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨s, hs, hsg⟩ := hg
  exact (φ.injective hsg) ▸ hs

end ToSL

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
