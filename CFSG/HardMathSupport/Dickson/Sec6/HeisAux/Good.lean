module

public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.CoreGen
public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.NormalForm

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ω : K} {σ : K ≃+* K}

theorem conjAut_comm_fieldAut_of_rat (g : GL (Fin 3) K)
    (h : ∀ i j, σ ((g : Matrix (Fin 3) (Fin 3) K) i j) = (g : Matrix (Fin 3) (Fin 3) K) i j) :
    LinearFlag.conjAut 3 K g * LinearFlag.fieldAut 3 K σ =
      LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K g := by
  obtain ⟨g₀, hg₀⟩ := exists_iota_of_fixed σ g h
  rw [← hg₀]
  exact fieldAut_comm_conjAut_iota σ g₀

theorem core_gen_conj (hK : Nat.card K = 64) (hσ : orderOf σ = 3) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {z m : Fin 4} (hg : GoodPar z m)
    {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hf : LinearFlag.fieldAut 3 K σ ∈ A) (Bk g0 g1 : GL (Fin 3) K)
    (θ : K) (hθ : θ ≠ 0)
    (hBf : LinearFlag.conjAut 3 K Bk * LinearFlag.fieldAut 3 K σ =
      LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K Bk)
    (hg0 : (g0 : Matrix (Fin 3) (Fin 3) K) * Bk = Bk * (θ • toMat ω (dM z)))
    (hg1 : (g1 : Matrix (Fin 3) (Fin 3) K) * Bk = Bk * toMat ω (CM m))
    (hd : LinearFlag.conjAut 3 K g0 ∈ A) (hC : LinearFlag.conjAut 3 K g1 ∈ A) : GenP A := by
  set τ : MulAut (projectiveSL 3 K) := (LinearFlag.conjAut 3 K Bk)⁻¹ with hτ
  set A' : Subgroup (MulAut (projectiveSL 3 K)) := A.map (MulAut.conj τ).toMonoidHom with hA'
  have hf' : LinearFlag.fieldAut 3 K σ ∈ A' := by
    refine ⟨LinearFlag.fieldAut 3 K σ, hf, ?_⟩
    show τ * LinearFlag.fieldAut 3 K σ * τ⁻¹ = LinearFlag.fieldAut 3 K σ
    rw [hτ, inv_inv, mul_assoc, ← hBf, inv_mul_cancel_left]
  have hel : IsElemAbelian 3 A' := isElemAbelian_map _ hAel
  have hcard : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj τ).injective, hA27]
  have hcj : ∀ g : GL (Fin 3) K, LinearFlag.conjAut 3 K g ∈ A →
      LinearFlag.conjAut 3 K (Bk⁻¹ * g * Bk) ∈ A' := by
    intro g hgA
    refine ⟨LinearFlag.conjAut 3 K g, hgA, ?_⟩
    show τ * LinearFlag.conjAut 3 K g * τ⁻¹ = _
    rw [hτ, inv_inv, map_mul, map_mul, map_inv]
  have key : ∀ (g : GL (Fin 3) K) (X : Matrix (Fin 3) (Fin 3) K),
      (g : Matrix (Fin 3) (Fin 3) K) * Bk = Bk * X →
      ((Bk⁻¹ * g * Bk : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = X := by
    intro g X h
    rw [Units.val_mul, Units.val_mul, mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul]
  exact GenP_of_conj τ A (core_gen hK hσ hω hσω hg hel hcard hf' (Bk⁻¹ * g0 * Bk)
    (Bk⁻¹ * g1 * Bk) θ hθ (key g0 _ hg0) (key g1 _ hg1) (hcj g0 hd) (hcj g1 hC))

theorem exists_good_code (hω : ω ^ 2 + ω + 1 = 0) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ∃ z : Fin 4, (z = 2 ∨ z = 3) ∧ ev ω z = ζ := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  have h : (ζ - ω) * (ζ - (ω + 1)) = 0 := by
    linear_combination hζ + hω - (ω * ζ + ζ + 1) * h2
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨2, Or.inl rfl, by simp [ev, sub_eq_zero.1 h]⟩
  · exact ⟨3, Or.inr rfl, by simp [ev, sub_eq_zero.1 h]⟩

theorem good_gen (hK : Nat.card K = 64) (hσ : orderOf σ = 3) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hf : LinearFlag.fieldAut 3 K σ ∈ A) (ζ μ : K)
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hζσ : σ ζ = ζ) (hμ : μ ^ 2 + μ + 1 = 0) (hμσ : σ μ = μ)
    (g0 g1 : GL (Fin 3) K)
    (hg0 : ∀ i j, σ ((g0 : Matrix (Fin 3) (Fin 3) K) i j) = (g0 : Matrix (Fin 3) (Fin 3) K) i j)
    (hg1 : ∀ i j, σ ((g1 : Matrix (Fin 3) (Fin 3) K) i j) = (g1 : Matrix (Fin 3) (Fin 3) K) i j)
    (hcube0 : (g0 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1)
    (hcube1 : (g1 : Matrix (Fin 3) (Fin 3) K) ^ 3 = μ • (1 : Matrix (Fin 3) (Fin 3) K))
    (hcomm : (g0 : Matrix (Fin 3) (Fin 3) K) * g1 = ζ • ((g1 : Matrix (Fin 3) (Fin 3) K) * g0))
    (hd : LinearFlag.conjAut 3 K g0 ∈ A) (hC : LinearFlag.conjAut 3 K g1 ∈ A) : GenP A := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  obtain ⟨z, hz, hzζ⟩ := exists_good_code hω hζ
  obtain ⟨m, hm, hmμ⟩ := exists_good_code hω hμ
  have hg : GoodPar z m := ⟨hz, hm⟩
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h] at hζ
    have : (1 : K) = 0 := by linear_combination hζ - h2
    exact one_ne_zero this
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ
  let Φ : Matrix (Fin 3) (Fin 3) (fixSub σ) →+* Matrix (Fin 3) (Fin 3) K :=
    RingHom.mapMatrix (fixSub σ).subtype
  have hΦinj : Function.Injective Φ := Matrix.map_injective (fixSub σ).subtype_injective
  have hΦapp : ∀ (X : Matrix (Fin 3) (Fin 3) (fixSub σ)) i j, Φ X i j = ((X i j : fixSub σ) : K) :=
    fun X i j => rfl
  let M0F : Matrix (Fin 3) (Fin 3) (fixSub σ) :=
    Matrix.of fun i j => ⟨(g0 : Matrix (Fin 3) (Fin 3) K) i j, hg0 i j⟩
  let M1F : Matrix (Fin 3) (Fin 3) (fixSub σ) :=
    Matrix.of fun i j => ⟨(g1 : Matrix (Fin 3) (Fin 3) K) i j, hg1 i j⟩
  have hΦM0 : Φ M0F = (g0 : Matrix (Fin 3) (Fin 3) K) := by ext i j; rfl
  have hΦM1 : Φ M1F = (g1 : Matrix (Fin 3) (Fin 3) K) := by ext i j; rfl
  let ζF : fixSub σ := ⟨ζ, hζσ⟩
  let μF : fixSub σ := ⟨μ, hμσ⟩
  have hΦsmul : ∀ (c : fixSub σ) (X : Matrix (Fin 3) (Fin 3) (fixSub σ)),
      Φ (c • X) = (c : K) • Φ X := fun c X => by ext i j; rfl
  have hΦone : Φ (1 : Matrix (Fin 3) (Fin 3) (fixSub σ)) = 1 := map_one Φ
  have hζF : ζF ^ 2 + ζF + 1 = 0 := Subtype.ext (by simpa [ζF] using hζ)
  have hζF1 : ζF ≠ 1 := fun h => hζ1 (congrArg Subtype.val h)
  have hμF0 : μF ≠ 0 := fun h => hμ0 (congrArg Subtype.val h)
  have hM0F : M0F ^ 3 = 1 := hΦinj (by rw [map_pow, hΦM0, hcube0, hΦone])
  have hM1F : M1F ^ 3 = μF • (1 : Matrix (Fin 3) (Fin 3) (fixSub σ)) :=
    hΦinj (by rw [map_pow, hΦM1, hcube1, hΦsmul, hΦone])
  have hcommF : M0F * M1F = ζF • (M1F * M0F) :=
    hΦinj (by rw [map_mul, hΦM0, hΦM1, hcomm, hΦsmul, map_mul, hΦM0, hΦM1])
  obtain ⟨BF, θF, hBF, hθF, hE0, hE1⟩ := normal_form ζF μF hζF hζF1 hμF0 M0F M1F hM0F hM1F hcommF
  have hBu : IsUnit (Φ BF) := hBF.map Φ
  let Bk : GL (Fin 3) K := hBu.unit
  have hBk : (Bk : Matrix (Fin 3) (Fin 3) K) = Φ BF := rfl
  have hBrat : ∀ i j, σ ((Bk : Matrix (Fin 3) (Fin 3) K) i j) = (Bk : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => (BF i j).2
  have hBf := conjAut_comm_fieldAut_of_rat Bk hBrat
  have hdiag : Φ (Matrix.diagonal ![θF, θF * ζF, θF * ζF ^ 2]) = (θF : K) • toMat ω (dM z) := by
    rw [toMat_dM hω, hzζ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hΦapp, Matrix.diagonal_apply, ζF, pow_two]
  have hcomp : Φ (!![0, 0, μF; 1, 0, 0; 0, 1, 0]) = toMat ω (CM m) := by
    rw [toMat_CM, hmμ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hΦapp, μF]
  have hθ : (θF : K) ≠ 0 := fun h => hθF (Subtype.ext h)
  have hg0' : (g0 : Matrix (Fin 3) (Fin 3) K) * Bk = Bk * ((θF : K) • toMat ω (dM z)) := by
    rw [hBk, ← hΦM0, ← hdiag, ← map_mul, ← map_mul, hE0]
  have hg1' : (g1 : Matrix (Fin 3) (Fin 3) K) * Bk = Bk * toMat ω (CM m) := by
    rw [hBk, ← hΦM1, ← hcomp, ← map_mul, ← map_mul, hE1]
  exact core_gen_conj hK hσ hω hσω hg hAel hA27 hf Bk g0 g1 (θF : K) hθ hBf hg0' hg1' hd hC

end CFSG.HardMathSupport.Dickson.Sec6.Heis
