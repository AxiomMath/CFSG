module

public import Mathlib.FieldTheory.Finite.Basic
import CFSG.LieType.SeitzGeneration.NonabLinear
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLineSum
import CFSG.RankThree.PartTwo.Sec8.Hering88NLinAlg
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

open Module Polynomial LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_ker_conj_sub_one (g h : V ≃ₗ[K] V) :
    Module.finrank K ↥(LinearMap.ker ((h * g * h⁻¹).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker (g.toLinearMap - 1)) := by
  have hpoint : ∀ v : V,
      ((h * g * h⁻¹).toLinearMap - 1) (h v) = h (((g).toLinearMap - 1) v) := by
    intro v
    simp [LinearEquiv.mul_apply]
  have hmap : (LinearMap.ker (g.toLinearMap - 1)).map h.toLinearMap =
      LinearMap.ker ((h * g * h⁻¹).toLinearMap - 1) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [LinearMap.mem_ker]
      change ((h * g * h⁻¹).toLinearMap - 1) (h w) = 0
      rw [hpoint w, LinearMap.mem_ker.mp hw, map_zero]
    · intro hv
      refine ⟨h⁻¹ v, ?_, by simp⟩
      change (g.toLinearMap - 1) (h⁻¹ v) = 0
      have hv0 : ((h * g * h⁻¹).toLinearMap - 1) v = 0 := LinearMap.mem_ker.mp hv
      have h2 : ((h * g * h⁻¹).toLinearMap - 1) v = h (((g).toLinearMap - 1) (h⁻¹ v)) := by
        simpa using hpoint (h⁻¹ v)
      rw [h2] at hv0
      exact h.injective (by rw [hv0, map_zero])
  rw [← hmap, LinearEquiv.finrank_map_eq]

private theorem ker_sq_sub_one_eq_ker_sub_one (T : Module.End K V) (hT : T ^ 3 = 1) :
    LinearMap.ker (T ^ 2 - 1) = LinearMap.ker (T - 1) := by
  apply le_antisymm
  · intro v hv
    have hv' : T (T v) - v = 0 := by
      simpa [pow_two, Module.End.mul_apply] using (LinearMap.mem_ker.mp hv)
    have h2 : T (T v) = v := sub_eq_zero.mp hv'
    have h3 : T (T (T v)) = v := by
      have := LinearMap.congr_fun hT v
      simpa [pow_succ, Module.End.mul_apply] using this
    have h4 : T (T (T v)) = T v := by rw [h2]
    rw [h3] at h4
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact h4.symm
  · intro v hv
    have h2 : T v = v := sub_eq_zero.mp (by simpa using hv)
    rw [LinearMap.mem_ker]
    show (T ^ 2) v - v = 0
    rw [pow_two, Module.End.mul_apply, h2, h2, sub_self]

private lemma ker_sq_mul_eq_ker_mul_sq {y z : V ≃ₗ[K] V} (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hyz : Commute y z) :
    LinearMap.ker (y.toLinearMap ^ 2 * z.toLinearMap - 1) =
      LinearMap.ker ((y * z ^ 2).toLinearMap - 1) := by
  have hT3 : (y * z ^ 2) ^ 3 = 1 := by
    have hcomm2 : Commute y (z ^ 2) := hyz.pow_right 2
    rw [hcomm2.mul_pow]
    have hz6 : (z ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hz, one_pow]
    rw [hy, hz6, one_mul]
  have hT3' : ((y * z ^ 2).toLinearMap : Module.End K V) ^ 3 = 1 := by
    have h := map_pow
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) (y * z ^ 2) 3
    rw [show (y * z ^ 2) ^ 3 = 1 from hT3, map_one] at h
    simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using h.symm
  have hsq_group : (y * z ^ 2) ^ 2 = y ^ 2 * z := by
    rw [(hyz.pow_right 2).mul_pow, pow_two]
    congr 1
    calc (z ^ 2) ^ 2 = z ^ (2 * 2) := by rw [← pow_mul]
      _ = z ^ 4 := by norm_num
      _ = z ^ 3 * z := by rw [show 4 = 3 + 1 by norm_num, pow_add, pow_one]
      _ = z := by rw [hz, one_mul]
  have hsq : ((y * z ^ 2).toLinearMap : Module.End K V) ^ 2 =
      y.toLinearMap ^ 2 * z.toLinearMap := by
    ext v
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hsq_group
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  rw [← hsq, ker_sq_sub_one_eq_ker_sub_one _ hT3']

theorem finrank_add_three_mul_finrank_inf (hK : (3 : K) ≠ 0) {y z : V ≃ₗ[K] V}
    (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) (hyz : Commute y z) :
    Module.finrank K V + 3 * Module.finrank K ↥(LinearMap.ker (y.toLinearMap - 1) ⊓
        LinearMap.ker (z.toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker (y.toLinearMap - 1)) +
        Module.finrank K ↥(LinearMap.ker (z.toLinearMap - 1)) +
        Module.finrank K ↥(LinearMap.ker ((y * z).toLinearMap - 1)) +
        Module.finrank K ↥(LinearMap.ker ((y * z ^ 2).toLinearMap - 1)) := by
  have hy' : y.toLinearMap ^ 3 = 1 := by
    have h := map_pow
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) y 3
    rw [show y ^ 3 = 1 from hy, map_one] at h
    simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using h.symm
  have hz' : z.toLinearMap ^ 3 = 1 := by
    have h := map_pow
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) z 3
    rw [show z ^ 3 = 1 from hz, map_one] at h
    simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using h.symm
  have hcomm' : Commute y.toLinearMap z.toLinearMap := by
    rw [Commute]
    ext v
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hyz
    simpa [LinearEquiv.mul_apply] using this
  have h := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.finrank_lineSum
    (K := K) (V := V) hK hy' hz' hcomm'
  rw [ker_sq_mul_eq_ker_mul_sq hy hz hyz] at h
  rw [← h]
  rfl

private theorem eigen_conj_inv {g h : V ≃ₗ[K] V} (hgh : h * g * h⁻¹ = g⁻¹)
    {ν : K} (hν : ν ≠ 0) {v : V} (hv : g v = ν • v) :
    g (h v) = ν⁻¹ • h v := by
  have hcomm : ∀ w, h (g w) = g⁻¹ (h w) := by
    intro w
    have := congrArg (fun e : V ≃ₗ[K] V => e (h w)) hgh
    simpa [LinearEquiv.mul_apply] using this
  have h1 : g (h (g v)) = h v := by
    rw [hcomm v]
    simp
  rw [hv, map_smul] at h1
  show g (h v) = ν⁻¹ • h v
  calc g (h v) = ν⁻¹ • (ν • g (h v)) := by rw [inv_smul_smul₀ hν]
    _ = ν⁻¹ • (g (ν • h v)) := by rw [map_smul]
    _ = ν⁻¹ • h v := by rw [h1]

private lemma cube_root_add_sq_add_one {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    linear_combination hω3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)

private lemma omega_ne_zero_of_pow_three {ω : K} (hω3 : ω ^ 3 = 1) : ω ≠ 0 := by
  intro h0
  rw [h0] at hω3
  norm_num at hω3

private lemma omega_sub_sq_ne_zero {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω - ω ^ 2 ≠ 0 := by
  intro hzero
  have h' : ω * (1 - ω) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, hzero]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact omega_ne_zero_of_pow_three hω3 h0
  · exact hω1 (by linear_combination -h0)

private lemma X_sub_C_mul_X_sub_C {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (X - C ω : K[X]) * (X - C (ω ^ 2)) = X ^ 2 + X + 1 := by
  have hωsum := cube_root_add_sq_add_one hω3 hω1
  have hsum : ω + ω ^ 2 = -1 := by linear_combination hωsum
  have hprod : ω * ω ^ 2 = 1 := by
    rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3]
  have hfac : (X - C ω : K[X]) * (X - C (ω ^ 2)) =
      X ^ 2 + X + 1 - C (ω + ω ^ 2 + 1) * X + C (ω * ω ^ 2 - 1) := by
    have f1 : (C (ω + ω ^ 2 + 1) : K[X]) = C ω + C (ω ^ 2) + 1 := by simp
    have f2 : (C (ω * ω ^ 2 - 1) : K[X]) = C ω * C (ω ^ 2) - 1 := by simp
    rw [f1, f2]
    ring
  have h1 : (C (ω + ω ^ 2 + 1) : K[X]) = 0 := by
    rw [show ω + ω ^ 2 + 1 = 0 by linear_combination hωsum]
    simp
  have h2 : (C (ω * ω ^ 2 - 1) : K[X]) = 0 := by
    rw [hprod, sub_self]
    simp
  rw [hfac, h1, h2]
  ring

private lemma ker_aeval_X_sub_C (G : Module.End K V) (a : K) :
    ((aeval G) (X - C a : K[X])).ker = LinearMap.ker (G - a • 1) := by
  congr 1
  simp [Algebra.algebraMap_eq_smul_one]

private lemma ker_aeval_sq_add_one (G : Module.End K V) :
    ((aeval G) (X ^ 2 + X + 1 : K[X])).ker = LinearMap.ker (G ^ 2 + G + 1) := by
  congr 1
  simp [map_add, map_mul, map_pow, Algebra.algebraMap_eq_smul_one]

private lemma sup_ker_sq_add_eq_eigenspaces {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (G : Module.End K V) :
    LinearMap.ker (G ^ 2 + G + 1) =
      LinearMap.ker (G - ω • 1) ⊔ LinearMap.ker (G - ω ^ 2 • 1) := by
  have hne := omega_sub_sq_ne_zero hω3 hω1
  have hcop : IsCoprime (X - C ω : K[X]) (X - C (ω ^ 2)) :=
    isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr hne)
  have h := sup_ker_aeval_eq_ker_aeval_mul_of_coprime G hcop
  rw [ker_aeval_X_sub_C, ker_aeval_X_sub_C, X_sub_C_mul_X_sub_C hω3 hω1,
    ker_aeval_sq_add_one] at h
  exact h.symm

private lemma disjoint_ker_eigenspaces {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (G : Module.End K V) :
    Disjoint (LinearMap.ker (G - ω • 1)) (LinearMap.ker (G - ω ^ 2 • 1)) := by
  have hne := omega_sub_sq_ne_zero hω3 hω1
  have hcop : IsCoprime (X - C ω : K[X]) (X - C (ω ^ 2)) :=
    isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr hne)
  have h := Polynomial.disjoint_ker_aeval_of_isCoprime G hcop
  rwa [ker_aeval_X_sub_C, ker_aeval_X_sub_C] at h

private lemma mem_ker_sub_smul {G : Module.End K V} {a : K} {x : V} :
    x ∈ LinearMap.ker (G - a • 1) ↔ G x = a • x := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero]

private lemma finrank_eq_of_mapsTo {A B : Submodule K V} {e : V ≃ₗ[K] V}
    (hAB : A.map e.toLinearMap ≤ B) (hBA : B.map e.toLinearMap ≤ A) :
    finrank K ↥A = finrank K ↥B := by
  have h1 : finrank K ↥A ≤ finrank K ↥B := by
    calc finrank K ↥A = finrank K ↥(A.map e.toLinearMap) :=
          (LinearEquiv.finrank_map_eq e A).symm
      _ ≤ finrank K ↥B := Submodule.finrank_mono hAB
  have h2 : finrank K ↥B ≤ finrank K ↥A := by
    calc finrank K ↥B = finrank K ↥(B.map e.toLinearMap) :=
          (LinearEquiv.finrank_map_eq e B).symm
      _ ≤ finrank K ↥A := Submodule.finrank_mono hBA
  omega

private lemma finrank_eigenspaces_eq {g h : V ≃ₗ[K] V} (hgh : h * g * h⁻¹ = g⁻¹)
    {ω : K} (hω3 : ω ^ 3 = 1) :
    finrank K ↥(LinearMap.ker (g.toLinearMap - ω • 1)) =
      finrank K ↥(LinearMap.ker (g.toLinearMap - ω ^ 2 • 1)) := by
  have hω0 := omega_ne_zero_of_pow_three hω3
  have hωinv : ω⁻¹ = ω ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3]
  have hω2inv : (ω ^ 2)⁻¹ = ω := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [show ω ^ 2 * ω = ω ^ 3 by ring, hω3]
  have hAB : (LinearMap.ker (g.toLinearMap - ω • 1)).map h.toLinearMap ≤
      LinearMap.ker (g.toLinearMap - ω ^ 2 • 1) := by
    rintro x ⟨v, hv, rfl⟩
    have hv' : g.toLinearMap v = ω • v := by
      simpa [mem_ker_sub_smul, sub_eq_zero] using hv
    have hgoal : g.toLinearMap (h v) = ω ^ 2 • h v := by
      have := eigen_conj_inv hgh hω0 hv'
      rwa [hωinv] at this
    exact mem_ker_sub_smul.mpr hgoal
  have hBA : (LinearMap.ker (g.toLinearMap - ω ^ 2 • 1)).map h.toLinearMap ≤
      LinearMap.ker (g.toLinearMap - ω • 1) := by
    rintro x ⟨v, hv, rfl⟩
    have hv' : g.toLinearMap v = ω ^ 2 • v := by
      simpa [mem_ker_sub_smul, sub_eq_zero] using hv
    have hgoal : g.toLinearMap (h v) = ω • h v := by
      have := eigen_conj_inv hgh (pow_ne_zero 2 hω0) hv'
      rwa [hω2inv] at this
    exact mem_ker_sub_smul.mpr hgoal
  exact finrank_eq_of_mapsTo hAB hBA

private theorem even_finrank_ker_sq_add_of_cube_root {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {g h : V ≃ₗ[K] V} (hg : g ^ 3 = 1) (hgh : h * g * h⁻¹ = g⁻¹) :
    Even (finrank K ↥(LinearMap.ker (g.toLinearMap ^ 2 + g.toLinearMap + 1))) := by
  have hsup := sup_ker_sq_add_eq_eigenspaces hω3 hω1 g.toLinearMap
  have hdisj := disjoint_ker_eigenspaces hω3 hω1 g.toLinearMap
  have hdimAB := finrank_eigenspaces_eq hgh hω3
  have hdimW : finrank K ↥(LinearMap.ker (g.toLinearMap - ω • 1) ⊔
      LinearMap.ker (g.toLinearMap - ω ^ 2 • 1)) =
      finrank K ↥(LinearMap.ker (g.toLinearMap - ω • 1)) +
        finrank K ↥(LinearMap.ker (g.toLinearMap - ω ^ 2 • 1)) := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (g.toLinearMap - ω • 1))
      (LinearMap.ker (g.toLinearMap - ω ^ 2 • 1))
    have hinf : LinearMap.ker (g.toLinearMap - ω • 1) ⊓
        LinearMap.ker (g.toLinearMap - ω ^ 2 • 1) = ⊥ := disjoint_iff.mp hdisj
    rw [hinf, finrank_bot, add_zero] at hd
    exact hd
  rw [hsup, hdimW, hdimAB]
  exact ⟨_, rfl⟩

private lemma three_not_dvd_card [Finite K] (hK : (3 : K) ≠ 0) :
    ¬ 3 ∣ Nat.card K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 3 := by
    intro h
    apply hK
    have hd : ringChar K ∣ 3 := by
      simpa [h] using (dvd_refl 3 : (3 : ℕ) ∣ 3)
    exact (CharP.cast_eq_zero_iff K (ringChar K) 3).mpr hd
  obtain ⟨n, hpprime, hcard⟩ := FiniteField.card K (ringChar K)
  have hcard' : Nat.card K = (ringChar K) ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  rw [hcard']
  intro h
  have h3p : 3 ∣ ringChar K := Nat.prime_three.dvd_of_dvd_pow h
  have hp3 : ringChar K = 3 := by
    rcases (Nat.dvd_prime (CharP.char_is_prime K (ringChar K))).mp h3p with h1 | h1
    · omega
    · exact h1.symm
  exact hchar hp3

private lemma card_mod_three_eq_two [Finite K] (hK : (3 : K) ≠ 0)
    (hno : ∀ ω : K, ω ^ 3 = 1 → ω = 1) : Nat.card K % 3 = 2 := by
  have h3q := three_not_dvd_card hK
  have hno3 : ¬ 3 ∣ Nat.card K - 1 := by
    intro h
    obtain ⟨ζ, hζ⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_of_dvd_card_sub_one
      (F := K) Nat.prime_three h
    exact hζ.ne_one (by norm_num) (hno ζ hζ.pow_eq_one)
  have hlt : Nat.card K % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne0 : Nat.card K % 3 ≠ 0 := fun h => h3q (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hne1 : Nat.card K % 3 ≠ 1 := by
    intro h1
    apply hno3
    have hdvd := Nat.dvd_sub_mod (n := 3) (Nat.card K)
    rw [h1] at hdvd
    simpa [Nat.card_eq_fintype_card] using hdvd
  omega

private lemma mem_ker_sq_add {G : Module.End K V} {x : V} :
    x ∈ LinearMap.ker (G ^ 2 + G + 1) ↔ G (G x) + G x + x = 0 := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
    pow_two, Module.End.mul_apply]

private lemma ker_sq_add_invariant (G : Module.End K V) {x : V}
    (hx : x ∈ LinearMap.ker (G ^ 2 + G + 1)) :
    G x ∈ LinearMap.ker (G ^ 2 + G + 1) := by
  rw [mem_ker_sq_add] at hx ⊢
  have h : G (G (G x) + G x + x) = G (G (G x)) + G (G x) + G x := by
    rw [map_add, map_add]
  rw [← h, hx, map_zero]

private lemma card_ker_sq_add_modEq_one [Finite K] (hK : (3 : K) ≠ 0)
    {G : Module.End K V} (hG : G ^ 3 = 1) :
    Nat.card ↥(LinearMap.ker (G ^ 2 + G + 1)) ≡ 1 [MOD 3] := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  let W : Submodule K V := LinearMap.ker (G ^ 2 + G + 1)
  let f : Function.End W := fun w => ⟨G w.1, ker_sq_add_invariant G w.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext w
    apply Subtype.ext
    show G (G (G w.1)) = w.1
    have h := LinearMap.congr_fun hG w.1
    simpa [pow_succ, Module.End.mul_apply] using h
  have hfix1 : Fintype.card ↥(Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, W.zero_mem⟩, ?_⟩, ?_⟩
    · rw [Function.mem_fixedPoints]
      apply Subtype.ext
      simp [f]
    · intro y
      apply Subtype.ext
      apply Subtype.ext
      have hyfix : f y = y := by
        have := y.2
        rwa [Function.mem_fixedPoints] at this
      have hyval : G y.1.1 = y.1.1 := by
        have := congrArg Subtype.val hyfix
        simpa [f] using this
      have hyW : G (G y.1.1) + G y.1.1 + y.1.1 = 0 := (mem_ker_sq_add).mp y.1.2
      have h3 : (3 : K) • y.1.1 = 0 := by
        have hgg : G (G y.1.1) = y.1.1 := by rw [hyval, hyval]
        rw [hgg, hyval] at hyW
        simpa [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul] using hyW
      exact (smul_eq_zero.mp h3).resolve_left hK
  have hcong := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  rw [hfix1] at hcong
  rwa [Nat.card_eq_fintype_card]

private lemma two_eq_neg_one_zmod_three : (2 : ZMod 3) = -1 := by decide

private lemma neg_one_ne_one_zmod_three : (-1 : ZMod 3) ≠ 1 := by decide

private theorem even_finrank_ker_sq_add_of_no_cube_root [Finite K]
    (hK : (3 : K) ≠ 0) (hno : ∀ ω : K, ω ^ 3 = 1 → ω = 1)
    {G : Module.End K V} (hG : G ^ 3 = 1) :
    Even (finrank K ↥(LinearMap.ker (G ^ 2 + G + 1))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  have hqmod : Nat.card K % 3 = 2 := card_mod_three_eq_two hK hno
  set W : Submodule K V := LinearMap.ker (G ^ 2 + G + 1) with hW
  have hcong : Nat.card W ≡ 1 [MOD 3] := by
    rw [hW]
    exact card_ker_sq_add_modEq_one hK hG
  have hcardW : Nat.card W = Nat.card K ^ finrank K W := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W),
      ← Nat.card_eq_fintype_card]
  have hz : (Nat.card K : ZMod 3) ^ finrank K W = 1 := by
    have h1 : (Nat.card W : ZMod 3) = 1 :=
      (ZMod.natCast_eq_natCast_iff (Nat.card W) 1 3).mpr (by simpa using hcong)
    rwa [hcardW, Nat.cast_pow] at h1
  have hq2 : (Nat.card K : ZMod 3) = -1 := by
    have h2 : (Nat.card K : ZMod 3) = (2 : ZMod 3) :=
      (ZMod.natCast_eq_natCast_iff (Nat.card K) 2 3).mpr (by simpa [Nat.ModEq] using hqmod)
    rw [h2]
    exact two_eq_neg_one_zmod_three
  rw [hq2] at hz
  exact (neg_one_pow_eq_one_iff_even (R := ZMod 3) neg_one_ne_one_zmod_three).mp hz

theorem even_finrank_sub_finrank_ker [Finite K] (hK : (3 : K) ≠ 0) {g h : V ≃ₗ[K] V}
    (hg : g ^ 3 = 1) (hh : h * g * h⁻¹ = g⁻¹) :
    Even (Module.finrank K V - Module.finrank K ↥(LinearMap.ker (g.toLinearMap - 1))) := by
  have hg' : g.toLinearMap ^ 3 = 1 := by
    have h := map_pow
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) g 3
    rw [show g ^ 3 = 1 from hg, map_one] at h
    simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using h.symm
  have hcompl :=
    CFSG.RankThree.PartTwo.Sec8.Hering88N.isCompl_ker_sub_one_ker_sq_add_add_one
      hK g.toLinearMap hg'
  have hdim : Module.finrank K V - Module.finrank K ↥(LinearMap.ker (g.toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker (g.toLinearMap ^ 2 + g.toLinearMap + 1)) := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  rw [hdim]
  by_cases hω : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1
  · obtain ⟨ω, hω3, hω1⟩ := hω
    exact even_finrank_ker_sq_add_of_cube_root hω3 hω1 hg hh
  · have hno : ∀ ω : K, ω ^ 3 = 1 → ω = 1 := by
      intro ω hω3
      by_contra hω1
      exact hω ⟨ω, hω3, hω1⟩
    exact even_finrank_ker_sq_add_of_no_cube_root hK hno hg'

theorem finrank_ker_sub_one_lt_finrank {g : V ≃ₗ[K] V} (hg : g ≠ 1) :
    Module.finrank K ↥(LinearMap.ker (g.toLinearMap - 1)) < Module.finrank K V := by
  refine Submodule.finrank_lt fun htop => hg ?_
  ext v
  have hv : v ∈ LinearMap.ker (g.toLinearMap - 1) := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
  simpa using hv

theorem finrank_add_three_mul_finrank_inf_map (hK : (3 : K) ≠ 0) {X : Type*} [Group X]
    (ρ : X →* (V ≃ₗ[K] V)) {y z : X} (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hyz : Commute y z) :
    Module.finrank K V + 3 * Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1) ⊓
        LinearMap.ker ((ρ z).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1)) +
        Module.finrank K ↥(LinearMap.ker ((ρ z).toLinearMap - 1)) +
        Module.finrank K ↥(LinearMap.ker ((ρ (y * z)).toLinearMap - 1)) +
        Module.finrank K ↥(LinearMap.ker ((ρ (y * z ^ 2)).toLinearMap - 1)) := by
  have hρy3 : (ρ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hρz3 : (ρ z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have h := finrank_add_three_mul_finrank_inf hK hρy3 hρz3 (hyz.map ρ)
  rw [show ρ y * ρ z = ρ (y * z) from (map_mul ρ y z).symm,
    show ρ y * ρ z ^ 2 = ρ (y * z ^ 2) by rw [map_mul, map_pow]] at h
  exact h

theorem finrank_ker_eq_of_isConj {X : Type*} [Group X] (ρ : X →* (V ≃ₗ[K] V)) {a b : X}
    (h : IsConj a b) :
    Module.finrank K ↥(LinearMap.ker ((ρ a).toLinearMap - 1)) =
      Module.finrank K ↥(LinearMap.ker ((ρ b).toLinearMap - 1)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hconj : ρ c * ρ a * (ρ c)⁻¹ = ρ b := by
    calc ρ c * ρ a * (ρ c)⁻¹ = ρ (c * a * c⁻¹) := by simp only [map_mul, map_inv]
      _ = ρ b := by rw [hc]
  have hdim := finrank_ker_conj_sub_one (K := K) (V := V) (g := ρ a) (h := ρ c)
  rw [hconj] at hdim
  exact hdim.symm

theorem even_finrank_sub_of_isConj_inv [Finite K] (hK : (3 : K) ≠ 0) {X : Type*} [Group X]
    (ρ : X →* (V ≃ₗ[K] V)) {y : X} (hy3 : y ^ 3 = 1) (h : IsConj y y⁻¹) :
    Even (Module.finrank K V -
      Module.finrank K ↥(LinearMap.ker ((ρ y).toLinearMap - 1))) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hρy3 : (ρ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hh : ρ c * ρ y * (ρ c)⁻¹ = (ρ y)⁻¹ := by
    calc ρ c * ρ y * (ρ c)⁻¹ = ρ (c * y * c⁻¹) := by simp only [map_mul, map_inv]
      _ = ρ y⁻¹ := by rw [hc]
      _ = (ρ y)⁻¹ := map_inv ρ y
  exact even_finrank_sub_finrank_ker (K := K) (V := V) hK hρy3 hh

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin
