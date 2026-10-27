module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section FixedPoint

theorem exists_ne_mem_fixedPoints_of_isPGroup {P : Type*} [Group P] (hP : IsPGroup 2 P)
    {α : Type*} [Finite α] [MulAction P α] (hα : 2 ∣ Nat.card α) {a : α}
    (ha : ∀ p : P, p • a = a) : ∃ b : α, b ≠ a ∧ ∀ p : P, p • b = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.card_modEq_card_fixedPoints α
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints P α) :=
    (Nat.modEq_zero_iff_dvd.1 ((Nat.modEq_zero_iff_dvd.2 hα).symm.trans h).symm)
  by_contra hne
  push Not at hne
  have hsub : Subsingleton (MulAction.fixedPoints P α) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : α) = a := by
      by_contra hxa
      exact hxa (by
        obtain ⟨p, hp⟩ := hne x hxa
        exact absurd (x.2 p) hp)
    have hy : (y : α) = a := by
      by_contra hya
      exact hya (by
        obtain ⟨p, hp⟩ := hne y hya
        exact absurd (y.2 p) hp)
    rw [hx, hy]
  have hpos : 0 < Nat.card (MulAction.fixedPoints P α) :=
    Nat.card_pos_iff.2 ⟨⟨⟨a, ha⟩⟩, inferInstance⟩
  have hle : Nat.card (MulAction.fixedPoints P α) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.2 hsub
  have h1 : Nat.card (MulAction.fixedPoints P α) = 1 := by omega
  rw [h1] at h2
  exact absurd h2 (by norm_num)

end FixedPoint

section Unitri

variable {F : Type*} [Field F] [Finite F]

theorem unitri_of_isPGroup (hF : 2 ∣ Nat.card F) (n : ℕ) {P : Type*} [Group P]
    (hP : IsPGroup 2 P) (ρ : P →* Matrix (Fin n) (Fin n) F)
    (hρ : ∀ i j : Fin n, i.val + 1 = j.val → ∃ p, ρ p = 1 + single i j 1) (p : P) :
    (∀ i j : Fin n, j < i → ρ p i j = 0) ∧ ∀ i, ρ p i i = 1 := by
  induction n generalizing P with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    let _ : MulAction P (Fin (n + 1) → F) :=
      { smul := fun p v => ρ p *ᵥ v
        one_smul := fun v => by
          change ρ 1 *ᵥ v = v
          rw [map_one, one_mulVec]
        mul_smul := fun p q v => by
          change ρ (p * q) *ᵥ v = ρ p *ᵥ (ρ q *ᵥ v)
          rw [map_mul, mulVec_mulVec] }
    have hcard : 2 ∣ Nat.card (Fin (n + 1) → F) := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (n + 1)), Fintype.card_fin]
      exact hF.trans (dvd_pow_self _ (Nat.succ_ne_zero n))
    obtain ⟨v, hv0, hvfix⟩ := exists_ne_mem_fixedPoints_of_isPGroup hP hcard
      (a := (0 : Fin (n + 1) → F)) (fun p => mulVec_zero (ρ p))
    have hfix : ∀ p, ρ p *ᵥ v = v := hvfix
    have hvj : ∀ j : Fin (n + 1), j ≠ 0 → v j = 0 := by
      intro j hj
      have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.2 (fun h => hj (Fin.ext h))
      obtain ⟨q, hq⟩ := hρ ⟨j.val - 1, by omega⟩ j (by simp only; omega)
      have h1 := congrFun (hfix q) ⟨j.val - 1, by omega⟩
      rw [hq, add_mulVec, one_mulVec, Pi.add_apply, single_mulVec, Function.update_self,
        one_mul] at h1
      exact left_eq_add.1 h1.symm
    have hv00 : v 0 ≠ 0 := by
      intro h
      apply hv0
      funext k
      by_cases hk : k = 0
      · rw [hk, h]
        rfl
      · rw [hvj k hk]
        rfl
    have hcol : ∀ p i, ρ p i 0 = if i = 0 then 1 else 0 := by
      intro p i
      have h1 := congrFun (hfix p) i
      rw [mulVec, dotProduct, Fin.sum_univ_succ, Finset.sum_eq_zero (fun k _ => by
        rw [hvj k.succ (Fin.succ_ne_zero k), mul_zero]), add_zero] at h1
      split_ifs with hi
      · subst hi
        exact (mul_eq_right₀ hv00).1 h1
      · rw [hvj i hi] at h1
        exact (mul_eq_zero.1 h1).resolve_right hv00
    let ρ' : P →* Matrix (Fin n) (Fin n) F :=
      { toFun := fun p => (ρ p).submatrix Fin.succ Fin.succ
        map_one' := by
          change (ρ 1).submatrix Fin.succ Fin.succ = 1
          rw [map_one]
          exact submatrix_one _ (Fin.succ_injective n)
        map_mul' := fun p q => by
          ext i j
          simp only [submatrix_apply, mul_apply, map_mul]
          rw [Fin.sum_univ_succ, hcol p i.succ, ite_eq_right (Fin.succ_ne_zero i), zero_mul,
            zero_add] }
    have hρ' : ∀ i j : Fin n, i.val + 1 = j.val → ∃ p, ρ' p = 1 + single i j 1 := by
      intro i j hij
      obtain ⟨q, hq⟩ := hρ i.succ j.succ (by simp only [Fin.val_succ]; omega)
      refine ⟨q, ?_⟩
      ext a b
      change (ρ q).submatrix Fin.succ Fin.succ a b = _
      rw [hq, submatrix_apply, Matrix.add_apply, Matrix.add_apply, one_apply, one_apply,
        single_apply, single_apply]
      simp only [Fin.succ_inj]
    obtain ⟨hlow, hdiag⟩ := ih hP ρ' hρ' p
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · cases j using Fin.cases with
      | zero => rw [hcol, ite_eq_right (Fin.pos_iff_ne_zero.1 hij)]
      | succ j =>
        cases i using Fin.cases with
        | zero => exact absurd hij (not_lt.2 (Fin.zero_le _))
        | succ i => exact hlow i j (Fin.succ_lt_succ_iff.1 hij)
    · cases i using Fin.cases with
      | zero => rw [hcol, ite_eq_left rfl]
      | succ i => exact hdiag i

omit [Finite F] in
theorem isPGroup_scalars_four : IsPGroup 2 (scalars 4 F) := by
  rintro ⟨g, c, hc, hg⟩
  refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
  change ((g ^ 2 ^ 2 : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1
  rw [Matrix.SpecialLinearGroup.coe_pow, hg, ← map_pow, ← Units.val_pow_eq_pow_val,
    show 2 ^ 2 = 4 by norm_num, hc, Units.val_one, map_one]

theorem le_projUnitriangular_of_isPGroup (hF : 2 ∣ Nat.card F) {n : ℕ}
    (hZ : IsPGroup 2 (scalars n F)) {P : Subgroup (projectiveSL n F)} (hP : IsPGroup 2 P)
    (hx : ∀ (i j : Fin n) (hij : i ≠ j), i.val + 1 = j.val →
      proj n F (SpecialLinearGroup.transvection hij 1) ∈ P) :
    P ≤ projUnitriangular n F := by
  set Pt := P.comap (proj n F) with hPt
  have hPt2 : IsPGroup 2 Pt := hP.comap_of_ker_isPGroup _ (by rw [ker_proj]; exact hZ)
  let ρ : Pt →* Matrix (Fin n) (Fin n) F :=
    { toFun := fun g => ((g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hρ : ∀ i j : Fin n, i.val + 1 = j.val → ∃ p, ρ p = 1 + single i j 1 := by
    intro i j hij
    have hne : i ≠ j := fun h => by rw [h] at hij; omega
    exact ⟨⟨SpecialLinearGroup.transvection hne 1, hx i j hne hij⟩, rfl⟩
  intro x hx'
  obtain ⟨g, rfl⟩ := proj_surjective n F x
  have hg : g ∈ Pt := hx'
  obtain ⟨hlow, hdiag⟩ := unitri_of_isPGroup hF n hPt2 ρ hρ ⟨g, hg⟩
  exact mem_map_of_mem _ (mem_unitriangular.2 ⟨hlow, hdiag⟩)

end Unitri

section Lang

variable {F : Type*} [Field F]

theorem exists_inv_mul_mul_fieldAut_eq_one {n : ℕ} {σ : F ≃+* F} (hσσ : ∀ x, σ (σ x) = x)
    {β : F} (hβ : β + σ β = 1) {u : projectiveSL n F} (hu : u ∈ projUnitriangular n F)
    (hc : u * fieldAut n F σ u = 1) :
    ∃ v ∈ projUnitriangular n F, v⁻¹ * u * fieldAut n F σ v = 1 := by
  obtain ⟨U, hU, rfl⟩ := hu
  rw [fieldAut_proj, ← map_mul, proj_eq_one_iff] at hc
  obtain ⟨c, -, hcU⟩ := hc
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hU
  have hσU : ∀ i j, ((SpecialLinearGroup.map σ.toRingHom U : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = σ ((U : Matrix (Fin n) (Fin n) F) i j) := fun i j => by
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    rfl
  have hσUmem : SpecialLinearGroup.map σ.toRingHom U ∈ unitriangular n F :=
    mem_unitriangular.2 ⟨fun i j hij => by rw [hσU, hlow i j hij, map_zero],
      fun i => by rw [hσU, hdiag i, map_one]⟩
  have hM := (mem_unitriangular.1 (mul_mem hU hσUmem)).2
  have hUU : (U : Matrix (Fin n) (Fin n) F) *
      ((SpecialLinearGroup.map σ.toRingHom U : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hM i, one_apply_eq]
    · rw [hcU, scalar_apply, diagonal_apply_ne _ hij, one_apply_ne hij]
  set V : Matrix (Fin n) (Fin n) F :=
    σ β • (1 : Matrix (Fin n) (Fin n) F) + β • (U : Matrix (Fin n) (Fin n) F) with hVdef
  have hVlow : ∀ i j : Fin n, j < i → V i j = 0 := fun i j hij => by
    rw [hVdef, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, one_apply_ne (ne_of_gt hij),
      hlow i j hij, smul_zero, smul_zero, add_zero]
  have hVdiag : ∀ i, V i i = 1 := fun i => by
    rw [hVdef, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, one_apply_eq, hdiag i,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, add_comm, hβ]
  have hVdet : V.det = 1 := by
    rw [det_of_isUpperTriangular (fun i j hij => hVlow i j hij),
      Finset.prod_eq_one (fun i _ => hVdiag i)]
  set V' : SpecialLinearGroup (Fin n) F := ⟨V, hVdet⟩ with hV'def
  have hV'U : V' ∈ unitriangular n F := mem_unitriangular.2 ⟨hVlow, hVdiag⟩
  have hσV : ((SpecialLinearGroup.map σ.toRingHom V' : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = β • (1 : Matrix (Fin n) (Fin n) F) +
        σ β • ((SpecialLinearGroup.map σ.toRingHom U : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
    ext i j
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, hσU]
    change σ (V i j) = _
    rw [hVdef, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hσσ]
    by_cases hij : i = j
    · rw [hij, one_apply_eq, map_one]
    · rw [one_apply_ne hij, map_zero]
  have hkey : U * SpecialLinearGroup.map σ.toRingHom V' = V' := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hσV, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_one, hUU]
    change _ = V
    rw [hVdef, add_comm]
  refine ⟨proj n F V', mem_map_of_mem _ hV'U, ?_⟩
  rw [fieldAut_proj, ← map_inv, ← map_mul, ← map_mul, mul_assoc, hkey, inv_mul_cancel, map_one]

theorem exists_add_fieldAut_eq_one [CharP F 2] {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : ∀ x, σ (σ x) = x) : ∃ β : F, β + σ β = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  have hγ : x + σ x ≠ 0 := by
    intro h
    apply hx
    have h' : σ x = -x := by linear_combination h
    rw [h', CharTwo.neg_eq]
  have hσγ : σ (x + σ x) = x + σ x := by rw [map_add, hσσ, add_comm]
  refine ⟨x * (x + σ x)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hσγ, ← add_mul, mul_inv_cancel₀ hγ]

end Lang

end CFSG.SeitzReduction.LinearPilot
