module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Supp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Proj
public import CFSG.HardMathSupport.Dickson.Bal207.UniFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open Matrix

private theorem disjoint_of_forall_eq {α β : Type} {A B : Finset α} {g : α → β} {u u' : β}
    (hA : ∀ a ∈ A, g a = u) (hB : ∀ b ∈ B, g b = u') (hu : u ≠ u') : Disjoint A B :=
  Finset.disjoint_left.2 fun a ha hb => hu ((hA a ha).symm.trans (hB a hb))

private theorem forall_mem_pair {α β : Type} [DecidableEq α] {g : α → β} {a b : α} {u : β}
    (ha : g a = u) (hb : g b = u) : ∀ c ∈ ({a, b} : Finset α), g c = u := by
  intro c hc
  rcases Finset.mem_insert.1 hc with rfl | hc
  · exact ha
  · rw [Finset.mem_singleton.1 hc]
    exact hb

private theorem diag_pow_three {K : Type} [Field K] {n : ℕ} {A : GL (Fin n) K}
    (hA : A ^ 3 = 1) (hd : diagonal (diag (A : Matrix (Fin n) (Fin n) K)) = A) (l : Fin n) :
    diag (A : Matrix (Fin n) (Fin n) K) l ^ 3 = 1 := by
  have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) l l) hA
  rw [Units.val_pow_eq_pow_val, ← hd, diagonal_pow, diagonal_apply_eq, Units.val_one,
    one_apply_eq, Pi.pow_apply] at e
  exact e

theorem false_of_heisenberg_isotropic {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (h3 : 3 ∣ 2 ^ f + 1) {n : ℕ} (hn : n ≤ 6) {X Y Z : primeFormUnitary h (idGram K n)}
    (hX3 : X ^ 3 = 1) (hZ3 : Z ^ 3 = 1) (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y) {ω : Kˣ}
    (hω : ω ≠ 1)
    (hXY : (X : GL (Fin n) K) * (Y : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) ω * ((Y : GL (Fin n) K) * (X : GL (Fin n) K)))
    (hZs : ∀ c : Kˣ, (Z : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c)
    {W : Submodule K (Fin n → K)} (hW : W ≠ ⊥) (hiso : W ≤ W.orthogonalBilin (idForm h n))
    (hWX : ∀ w ∈ W, ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hWZ : ∀ w ∈ W, ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) : False := by
  classical
  have hX3' : (X : GL (Fin n) K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hX3, Subgroup.coe_one]
  have hZ3' : (Z : GL (Fin n) K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hZ3, Subgroup.coe_one]
  have hXZ' : (X : GL (Fin n) K) * Z = Z * X := by rw [← Subgroup.coe_mul, hXZ, Subgroup.coe_mul]
  have hYZ' : (Y : GL (Fin n) K) * Z = Z * Y := by rw [← Subgroup.coe_mul, hYZ, Subgroup.coe_mul]
  obtain ⟨P, hPU, hP⟩ := CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj
    h h3 {(X : GL (Fin n) K), (Z : GL (Fin n) K)} (by rintro x (rfl | rfl); exacts [X.2, Z.2])
    (by rintro x (rfl | rfl) y (rfl | rfl); exacts [rfl, hXZ', hXZ'.symm, rfl])
    (by rintro x (rfl | rfl); exacts [hX3', hZ3'])
  have hXd := (hP _ (Set.mem_insert _ _)).diagonal_diag
  have hZd := (hP _ (Set.mem_insert_of_mem _ rfl)).diagonal_diag
  set x := diag ((P⁻¹ * X * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hx
  set z := diag ((P⁻¹ * Z * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hz
  have hconj3 : ∀ A : GL (Fin n) K, A ^ 3 = 1 → (P⁻¹ * A * P) ^ 3 = 1 := fun A hA => by
    have e := conj_pow (a := P⁻¹) (b := A) (i := 3)
    rwa [inv_inv, hA, mul_one, inv_mul_cancel] at e
  have hx3 := diag_pow_three (hconj3 _ hX3') hXd
  have hz3 := diag_pow_three (hconj3 _ hZ3') hZd
  rw [← hx] at hx3
  rw [← hz] at hz3
  obtain ⟨i, j, hij, hxz⟩ := exists_eq_weight_of_isotropic h (ι := Bool)
    (X := fun b => bif b then (X : GL (Fin n) K) else Z) (R := P⁻¹) (inv_mem hPU)
    (d := fun b => bif b then x else z)
    (fun b => by
      cases b <;> simp only [cond_false, cond_true, inv_inv]
      exacts [hZd.symm, hXd.symm]) hW hiso
    (fun b w hw => by cases b; exacts [hWZ w hw, hWX w hw])
  have hxij : x i = x j := hxz true
  have hzij : z i = z j := hxz false
  set Ym := ((P⁻¹ * Y * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYm
  have eX : diagonal x * Ym = Matrix.scalar (Fin n) (ω : K) * (Ym * diagonal x) := by
    have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      (show P⁻¹ * X * P * (P⁻¹ * Y * P) =
          GeneralLinearGroup.scalar (Fin n) ω * (P⁻¹ * Y * P * (P⁻¹ * X * P)) by
        rw [show P⁻¹ * X * P * (P⁻¹ * Y * P) = P⁻¹ * (X * Y) * P by group, hXY,
          show P⁻¹ * (GeneralLinearGroup.scalar (Fin n) ω * (Y * X)) * P =
            P⁻¹ * GeneralLinearGroup.scalar (Fin n) ω * (Y * X) * P by group,
          ← GeneralLinearGroup.scalar_commute ω P⁻¹]
        group)
    simp only [Units.val_mul (P⁻¹ * (X : GL (Fin n) K) * P),
      Units.val_mul (GeneralLinearGroup.scalar (Fin n) ω),
      Units.val_mul (P⁻¹ * (Y : GL (Fin n) K) * P), GeneralLinearGroup.coe_scalar] at e
    rwa [← hXd] at e
  have eZ : Ym * diagonal z = diagonal z * Ym := by
    have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      (show P⁻¹ * Y * P * (P⁻¹ * Z * P) = P⁻¹ * Z * P * (P⁻¹ * Y * P) by
        rw [show P⁻¹ * Y * P * (P⁻¹ * Z * P) = P⁻¹ * (Y * Z) * P by group, hYZ']
        group)
    simp only [Units.val_mul (P⁻¹ * (Y : GL (Fin n) K) * P),
      Units.val_mul (P⁻¹ * (Z : GL (Fin n) K) * P)] at e
    rwa [← hZd] at e
  have hsupp : ∀ l k, Ym l k ≠ 0 → (x l, z l) = ((ω : K) * x k, z k) := by
    intro l k hlk
    have e1 := congrFun (congrFun eX l) k
    simp only [diagonal_mul, Matrix.scalar_apply, mul_diagonal] at e1
    refine Prod.ext (mul_right_cancel₀ hlk (by linear_combination e1)) ?_
    exact (eq_of_mul_diagonal_eq eZ hlk)
  have hdet : Ym.det ≠ 0 := by
    rw [hYm, ← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨π, hπ⟩ := exists_perm_of_support hdet hsupp
  have hπx : ∀ k, x (π k) = ω * x k := fun k => congrArg Prod.fst (hπ k)
  have hπz : ∀ k, z (π k) = z k := fun k => congrArg Prod.snd (hπ k)
  have hε0 : x i ≠ 0 := fun h0 => by simpa [h0] using hx3 i
  have hω3 : (ω : K) ^ 3 = 1 := by
    have e := hx3 (π i)
    rw [hπx, mul_pow, hx3 i, mul_one] at e
    exact e
  have hω1 : (ω : K) ≠ 1 := fun h1 => hω (Units.ext h1)
  have hω2 : (ω : K) ^ 2 ≠ 1 := fun h2 => hω1 (by linear_combination hω3 - (ω : K) * h2)
  have hne1 : x i ≠ ω * x i := fun e => hω1 (mul_right_cancel₀ hε0 (by rw [one_mul, ← e]))
  have hne2 : x i ≠ ω ^ 2 * x i := fun e => hω2 (mul_right_cancel₀ hε0 (by rw [one_mul, ← e]))
  have hne3 : ω * x i ≠ ω ^ 2 * x i := fun e => hne1 (mul_left_cancel₀ (Units.ne_zero ω)
    (by rw [← mul_assoc, ← sq]; exact e))
  set A : Finset (Fin n) := {i, j}
  set B : Finset (Fin n) := {π i, π j}
  set C : Finset (Fin n) := {π (π i), π (π j)}
  have hAx := forall_mem_pair (g := x) rfl hxij.symm
  have hBx := forall_mem_pair (g := x) (hπx i) (by rw [hπx, ← hxij])
  have hCx := forall_mem_pair (g := x) (u := ω ^ 2 * x i) (by rw [hπx, hπx, sq, mul_assoc])
    (by rw [hπx, hπx, ← hxij, sq, mul_assoc])
  have hABC : 6 ≤ (A ∪ B ∪ C).card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2
        ⟨disjoint_of_forall_eq hAx hCx hne2, disjoint_of_forall_eq hBx hCx hne3⟩),
      Finset.card_union_of_disjoint (disjoint_of_forall_eq hAx hBx hne1),
      Finset.card_pair hij, Finset.card_pair (π.injective.ne hij),
      Finset.card_pair (π.injective.ne (π.injective.ne hij))]
  have hsub : A ∪ B ∪ C ⊆ Finset.univ.filter fun l => z l = z i := by
    intro l hl
    refine Finset.mem_filter.2 ⟨Finset.mem_univ l, ?_⟩
    have hzA := forall_mem_pair (g := z) rfl hzij.symm
    have hzB := forall_mem_pair (g := z) (hπz i) (by rw [hπz, ← hzij])
    have hzC := forall_mem_pair (g := z) (u := z i) (by rw [hπz, hπz])
      (by rw [hπz, hπz, ← hzij])
    rcases Finset.mem_union.1 hl with hl | hl
    · rcases Finset.mem_union.1 hl with hl | hl
      exacts [hzA l hl, hzB l hl]
    · exact hzC l hl
  have hall : Finset.univ.filter (fun l => z l = z i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := Finset.card_le_card hsub
    have := Finset.card_le_univ (Finset.univ.filter fun l => z l = z i)
    rw [Fintype.card_fin] at this ⊢
    omega
  have hζ0 : z i ≠ 0 := fun h0 => by simpa [h0] using hz3 i
  apply hZs (Units.mk0 (z i) hζ0)
  have hZd' : P⁻¹ * (Z : GL (Fin n) K) * P =
      GeneralLinearGroup.scalar (Fin n) (Units.mk0 (z i) hζ0) := by
    refine Units.ext ?_
    rw [← hZd, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
    congr 1
    funext l
    have hl := Finset.mem_univ l
    rw [← hall, Finset.mem_filter] at hl
    exact hl.2
  calc (Z : GL (Fin n) K) = P * (P⁻¹ * Z * P) * P⁻¹ := by group
    _ = _ := by rw [hZd', ← GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
