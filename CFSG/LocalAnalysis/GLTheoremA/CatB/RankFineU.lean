module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev K4 : Type := GaloisField 2 2

section Field

theorem K4_card : Nat.card K4 = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem K4_pow_card_sub_one {a : K4} (ha : a ≠ 0) : a ^ 3 = 1 := by
  haveI : Fintype K4 := Fintype.ofFinite _
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [← Nat.card_eq_fintype_card, K4_card] at h

theorem K4_unit_cube (a : K4ˣ) : a ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact K4_pow_card_sub_one a.ne_zero

theorem K4_card_units : Nat.card K4ˣ = 3 := by
  rw [Nat.card_units, K4_card]

theorem finrank_K4 : Module.finrank (ZMod 2) K4 = 2 :=
  GaloisField.finrank 2 (by norm_num)

theorem trace_one_K4 : Algebra.trace (ZMod 2) K4 1 = 0 := by
  have h : (1 : K4) = algebraMap (ZMod 2) K4 1 := (map_one _).symm
  rw [h, Algebra.trace_algebraMap, finrank_K4]
  decide

theorem trace_cube (a : K4) : Algebra.trace (ZMod 2) K4 (a ^ 3) = 0 := by
  by_cases ha : a = 0
  · rw [ha]
    simp
  · rw [K4_pow_card_sub_one ha]
    exact trace_one_K4

theorem trace_nondegenerate {a : K4} (h : ∀ c : K4, Algebra.trace (ZMod 2) K4 (a * c) = 0) :
    a = 0 := by
  by_contra ha
  obtain ⟨c₀, hc₀⟩ := Algebra.trace_surjective (ZMod 2) K4 1
  have := h (a⁻¹ * c₀)
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, hc₀] at this
  exact one_ne_zero this

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

end Field

section Form

@[expose] noncomputable def trForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin n → K4) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => Algebra.trace (ZMod 2) K4 (∑ i, x i ^ 2 * y i))
    (fun x₁ x₂ y => by
      rw [← map_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, CharTwo.add_sq, add_mul])
    (fun c x y => by
      rcases zmod_two_cases c with rfl | rfl <;> simp)
    (fun x y₁ y₂ => by
      rw [← map_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, mul_add])
    (fun c x y => by
      rcases zmod_two_cases c with rfl | rfl <;> simp)

variable (n : ℕ)

theorem trForm_apply (x y : Fin n → K4) :
    trForm n x y = Algebra.trace (ZMod 2) K4 (∑ i, x i ^ 2 * y i) := rfl

theorem trForm_alt (x : Fin n → K4) : trForm n x x = 0 := by
  rw [trForm_apply, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← trace_cube (x i)]
  congr 1
  ring

theorem trForm_isRefl : (trForm n).IsRefl := by
  intro x y h
  have h1 := trForm_alt n (x + y)
  simp only [map_add, LinearMap.add_apply, trForm_alt, h, zero_add, add_zero] at h1
  exact h1

theorem trForm_nondegenerate : (trForm n).Nondegenerate :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (trForm_isRefl n)).2 fun x hx => by
    funext i
    have h1 : (x i) ^ 2 = 0 := by
      apply trace_nondegenerate
      intro c
      have := hx (Pi.single i c)
      rw [trForm_apply] at this
      simpa [Pi.single_apply] using this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h1

theorem finrank_pi_K4 : Module.finrank (ZMod 2) (Fin n → K4) = 2 * n := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_K4]
  simp [mul_comm]

end Form

section Rep

variable (n : ℕ)

@[expose] noncomputable def glRepZ : GL (Fin n) K4 →* Module.End (ZMod 2) (Fin n → K4) where
  toFun g := (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) K4)).restrictScalars (ZMod 2)
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by
    simp [Matrix.mulVec_mulVec]

theorem glRepZ_apply (g : GL (Fin n) K4) (x : Fin n → K4) :
    glRepZ n g x = (g : Matrix (Fin n) (Fin n) K4) *ᵥ x := rfl

@[expose] noncomputable def scalRep : K4ˣ →* Module.End (ZMod 2) (Fin n → K4) where
  toFun a := (LinearMap.lsmul K4 (Fin n → K4) (a : K4)).restrictScalars (ZMod 2)
  map_one' := LinearMap.ext fun x => by simp
  map_mul' a b := LinearMap.ext fun x => by
    show ((a * b : K4ˣ) : K4) • x = (a : K4) • (b : K4) • x
    rw [Units.val_mul, mul_smul]

theorem scalRep_apply (a : K4ˣ) (x : Fin n → K4) : scalRep n a x = (a : K4) • x := rfl

end Rep

section Unitary

theorem mem_statedSU_K4 {m : ℕ} (hm : 1 ≤ m) {g : GL (Fin m) K4} (hg : g ∈ StatedSU m 2 K4) :
    (g : Matrix (Fin m) (Fin m) K4).det = 1 ∧
      ((g : Matrix (Fin m) (Fin m) K4).map (· ^ 2))ᵀ * (g : Matrix (Fin m) (Fin m) K4) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := K4) (p := 2) (f := 1) Nat.prime_two
    (by rw [K4_card]; norm_num) hm).1
  have h1 : g ∈ (StatedSU m (2 ^ 1) K4 : Set (GL (Fin m) K4)) := hg
  rw [h] at h1
  simpa using h1

theorem herm_mulVec {m : ℕ} {A : Matrix (Fin m) (Fin m) K4} (hA : (A.map (· ^ 2))ᵀ * A = 1)
    (x y : Fin m → K4) :
    ∑ i, (A *ᵥ x) i ^ 2 * (A *ᵥ y) i = ∑ i, x i ^ 2 * y i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (fun i => (A *ᵥ x) i ^ 2) = (A.map (· ^ 2)) *ᵥ (fun j => x j ^ 2) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [sum_pow_char 2]
    simp [mul_pow]
  calc ∑ i, (A *ᵥ x) i ^ 2 * (A *ᵥ y) i
      = (fun i => (A *ᵥ x) i ^ 2) ⬝ᵥ (A *ᵥ y) := rfl
    _ = ((A.map (· ^ 2)) *ᵥ (fun j => x j ^ 2)) ⬝ᵥ (A *ᵥ y) := by rw [h1]
    _ = (fun j => x j ^ 2) ⬝ᵥ ((A.map (· ^ 2))ᵀ *ᵥ (A *ᵥ y)) := by
        rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
    _ = (fun j => x j ^ 2) ⬝ᵥ y := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    _ = ∑ i, x i ^ 2 * y i := rfl

theorem trForm_mulVec {m : ℕ} {A : Matrix (Fin m) (Fin m) K4} (hA : (A.map (· ^ 2))ᵀ * A = 1)
    (x y : Fin m → K4) : trForm m (A *ᵥ x) (A *ᵥ y) = trForm m x y := by
  rw [trForm_apply, trForm_apply, herm_mulVec hA]

theorem trForm_smul (m : ℕ) (a : K4ˣ) (x y : Fin m → K4) :
    trForm m ((a : K4) • x) ((a : K4) • y) = trForm m x y := by
  rw [trForm_apply, trForm_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  have h3 : (a : K4) ^ 3 = 1 := by
    have := K4_unit_cube a
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  calc ((a : K4) * x i) ^ 2 * ((a : K4) * y i) = (a : K4) ^ 3 * (x i ^ 2 * y i) := by ring
    _ = x i ^ 2 * y i := by rw [h3, one_mul]

theorem rankFine_unitary (m : ℕ) (hm : 2 ≤ m) (hm3 : Nat.Coprime m 3)
    {M : Type*} [Group M] [Finite M] (f : M →* GL (Fin m) K4) (hf : Function.Injective f)
    (hfSU : ∀ g, f g ∈ StatedSU m 2 K4) : RankFine M (3 ^ (m - 2)) := by
  intro E T hE hT hTne hET
  have hcomm : ∀ a b : ↥E, a * b = b * a := by
    have := hE.1
    exact fun a b => mul_comm' a b
  have hN : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T := fun e he t ht =>
    (Subgroup.mem_normalizer_iff.1 (hET he) t).1 ht
  have hfaith : ∀ (g : M) (a : K4ˣ), ((glRepZ m).comp f) g * scalRep m a = 1 → g = 1 ∧ a = 1 := by
    intro g a h
    have hx : ∀ x : Fin m → K4, (f g : Matrix (Fin m) (Fin m) K4) *ᵥ ((a : K4) • x) = x := by
      intro x
      have := congrArg (fun φ : Module.End (ZMod 2) (Fin m → K4) => φ x) h
      simpa [glRepZ_apply, scalRep_apply] using this
    have hmat : (f g : Matrix (Fin m) (Fin m) K4) =
        ((a⁻¹ : K4ˣ) : K4) • (1 : Matrix (Fin m) (Fin m) K4) := by
      ext i j
      have h1 := congrFun (hx (Pi.single j 1)) i
      simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply] at h1
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
      by_cases hij : i = j
      · subst hij
        simp at h1 ⊢
        exact (eq_inv_of_mul_eq_one_right h1)
      · simp [hij] at h1 ⊢
        exact h1
    have hdet := (mem_statedSU_K4 (by omega) (hfSU g)).1
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have hpow : a ^ m = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have h2 : ((a⁻¹ : K4ˣ) : K4) ^ m = 1 := hdet
      rw [Units.val_inv_eq_inv_val, inv_pow] at h2
      exact inv_eq_one.1 h2
    have ha : a = 1 := (pow_eq_one_iff_of_coprime hm3).1 ⟨hpow, K4_unit_cube a⟩
    subst ha
    refine ⟨hf ?_, rfl⟩
    rw [map_one]
    apply Units.ext
    rw [hmat]
    simp
  have h := card_mul_le_of_normalizes (trForm m) (trForm_nondegenerate m) (trForm_isRefl m)
    ⟨m, by rw [finrank_pi_K4]; ring⟩ ((glRepZ m).comp f)
    (fun g x y => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, glRepZ_apply]
      exact trForm_mulVec (mem_statedSU_K4 (by omega) (hfSU g)).2 x y)
    (A := K4ˣ) K4_unit_cube (scalRep m)
    (fun a x y => by
      simp only [scalRep_apply]
      exact trForm_smul m a x y)
    (fun a g => LinearMap.ext fun x => by
      simp [glRepZ_apply, scalRep_apply, Matrix.mulVec_smul, Module.End.mul_apply])
    hfaith hcomm (fun e he => hE.2 e he) hT hN hTne
  rw [finrank_pi_K4, K4_card_units] at h
  have h2 : 2 * m / 2 - 1 = (m - 2) + 1 := by omega
  rw [h2, pow_succ] at h
  exact Nat.le_of_mul_le_mul_right h (by norm_num)

noncomputable def statedProjSUEquiv {m : ℕ} (hm : 1 ≤ m) (hm3 : Nat.Coprime m 3) :
    StatedProj (StatedSU m 2 K4) ≃* StatedSU m 2 K4 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := K4) (p := 2) (f := 1) Nat.prime_two
    (by rw [K4_card]; norm_num) hm).2.2
  have h' : Nat.card ((StatedScalars (Fin m) K4).subgroupOf (StatedSU m 2 K4)) = Nat.gcd m 3 := h
  have hbot : (StatedScalars (Fin m) K4).subgroupOf (StatedSU m 2 K4) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [h']
    exact hm3
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot

theorem rankFine_statedProjSU (m : ℕ) (hm : 2 ≤ m) (hm3 : Nat.Coprime m 3) :
    RankFine (StatedProj (StatedSU m 2 K4)) (3 ^ (m - 2)) :=
  RankFine.of_mulEquiv (statedProjSUEquiv (by omega) hm3)
    (rankFine_unitary m hm hm3 (StatedSU m 2 K4).subtype Subtype.val_injective fun g => g.2)

theorem rankFine_u4 : RankFine (StatedProj (StatedSU 4 2 K4)) 9 := by
  simpa using rankFine_statedProjSU 4 (by norm_num) (by norm_num)

theorem rankFine_u5 : RankFine (StatedProj (StatedSU 5 2 K4)) 27 := by
  simpa using rankFine_statedProjSU 5 (by norm_num) (by norm_num)

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.CatB
