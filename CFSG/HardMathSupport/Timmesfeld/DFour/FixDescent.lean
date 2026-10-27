module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankCount
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open Module CFSG.StandardType.D4Rank

section Ring

variable {R : Type*} [CommRing R] {c : R}

abbrev fp3 (c z : R) : R := c * (1 + z + z ^ 2)

theorem fp3_sq (hc : 3 * c = 1) {z : R} (hz : z ^ 3 = 1) : fp3 c z * fp3 c z = fp3 c z := by
  unfold fp3
  linear_combination (c * (1 + z + z ^ 2)) * hc + (c ^ 2 * (2 + z)) * hz

theorem fp3_mul_eq {a b a' b' : R} (h : fp a * fp b = fp a' * fp b') :
    fp3 c a * fp3 c b = fp3 c a' * fp3 c b' := by
  simp only [fp3, fp] at h ⊢
  linear_combination c ^ 2 * h

theorem fp3_sum (hc : 3 * c = 1) {g h : R} (hh : h ^ 3 = 1) :
    fp3 c g + fp3 c h + fp3 c (g * h) + fp3 c (g * h ^ 2) = 1 + 3 * (fp3 c g * fp3 c h) := by
  unfold fp3
  linear_combination (1 - c * ((1 + g + g ^ 2) * (1 + h + h ^ 2))) * hc + (c * g ^ 2 * h) * hh

end Ring

section Rank

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem rank_formula3 {A : Type*} [CommRing A] (φ : A →+* Module.End K V)
    {q₁ q₂ q₃ q₄ T P : A} (h₁ : q₁ * q₁ = q₁) (h₂ : q₂ * q₂ = q₂) (h₃ : q₃ * q₃ = q₃)
    (h₄ : q₄ * q₄ = q₄) (h12 : q₁ * q₂ = T) (h13 : q₁ * q₃ = T) (h14 : q₁ * q₄ = T)
    (h23 : q₂ * q₃ = T) (h24 : q₂ * q₄ = T) (h34 : q₃ * q₄ = T)
    (hsum : q₁ + q₂ + q₃ + q₄ = P + 3 * T) :
    rk (φ q₁) + rk (φ q₂) + rk (φ q₃) + rk (φ q₄) = rk (φ P) + 3 * rk (φ T) := by
  have hTT : T * T = T := by
    rw [← h12]; linear_combination q₂ ^ 2 * h₁ + q₁ * h₂
  have hT1 : T * q₁ = T := by rw [← h12]; linear_combination q₂ * h₁
  have hT2 : T * q₂ = T := by rw [← h12]; linear_combination q₁ * h₂
  have hT3 : T * q₃ = T := by
    rw [← h12]; linear_combination q₁ * h23 - q₁ * h12 + q₂ * h₁
  have hT4 : T * q₄ = T := by
    rw [← h12]; linear_combination q₁ * h24 - q₁ * h12 + q₂ * h₁
  have hr : ∀ q : A, q * q = q → T * q = T → (q - T) * (q - T) = q - T := by
    intro q hq hTq
    linear_combination hq - 2 * hTq + hTT
  have hrT : ∀ q : A, T * q = T → (q - T) * T = 0 := by
    intro q hTq
    linear_combination hTq - hTT
  have hTr : ∀ q : A, T * q = T → T * (q - T) = 0 := by
    intro q hTq
    linear_combination hTq - hTT
  have hrr : ∀ q q' : A, q * q' = T → T * q = T → T * q' = T → (q - T) * (q' - T) = 0 := by
    intro q q' hqq' hTq hTq'
    linear_combination hqq' - hTq - hTq' + hTT
  have hsplit : ∀ q : A, q * q = q → T * q = T → rk (φ q) = rk (φ (q - T)) + rk (φ T) := by
    intro q hq hTq
    have e : q = (q - T) + T := by ring
    conv_lhs => rw [e]
    rw [map_add φ (q - T) T]
    refine rk_add_of_orth ?_ ?_ ?_ ?_
    · rw [← map_mul, hr q hq hTq]
    · rw [← map_mul, hrT q hTq, map_zero]
    · rw [← map_mul, hTr q hTq, map_zero]
    · rw [← map_mul, hTT]
  set e : Fin 5 → A := ![T, q₁ - T, q₂ - T, q₃ - T, q₄ - T] with he
  have eP : φ P = ∑ i, φ (e i) := by
    rw [Fin.sum_univ_five, ← map_add, ← map_add, ← map_add, ← map_add]
    congr 1
    simp only [he, Matrix.cons_val]
    linear_combination -hsum
  have hidem : ∀ i ∈ (Finset.univ : Finset (Fin 5)), φ (e i) * φ (e i) = φ (e i) := by
    intro i _
    rw [← map_mul]
    congr 1
    fin_cases i
    · exact hTT
    · exact hr q₁ h₁ hT1
    · exact hr q₂ h₂ hT2
    · exact hr q₃ h₃ hT3
    · exact hr q₄ h₄ hT4
  have horth : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ j ∈ (Finset.univ : Finset (Fin 5)),
      i ≠ j → φ (e i) * φ (e j) = 0 := by
    have hs : ∀ x y : A, x * y = 0 → y * x = 0 := fun x y h => by rw [mul_comm, h]
    have o12 := hrr q₁ q₂ h12 hT1 hT2
    have o13 := hrr q₁ q₃ h13 hT1 hT3
    have o14 := hrr q₁ q₄ h14 hT1 hT4
    have o23 := hrr q₂ q₃ h23 hT2 hT3
    have o24 := hrr q₂ q₄ h24 hT2 hT4
    have o34 := hrr q₃ q₄ h34 hT3 hT4
    have t1 := hTr q₁ hT1
    have t2 := hTr q₂ hT2
    have t3 := hTr q₃ hT3
    have t4 := hTr q₄ hT4
    intro i _ j _ hij
    rw [← map_mul, ← map_zero φ]
    congr 1
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | simp only [he]
        first
          | assumption
          | exact hs _ _ (by assumption)
  have hP := rk_sum_of_orth Finset.univ (fun i => φ (e i)) hidem horth
  rw [← eP, Fin.sum_univ_five] at hP
  simp only [he, Matrix.cons_val] at hP
  rw [hsplit q₁ h₁ hT1, hsplit q₂ h₂ hT2, hsplit q₃ h₃ hT3, hsplit q₄ h₄ hT4, hP]
  ring

end Rank

section Model

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {E : Type*} [Group E] [IsMulCommutative E]

@[reducible, expose] noncomputable def adjCommRing3 (ρ : E →* Module.End K V) :
    CommRing (Algebra.adjoin K (Set.range ρ)) :=
  { (inferInstance : Ring (Algebra.adjoin K (Set.range ρ))) with
    mul_comm := fun a b =>
      (Algebra.isMulCommutative_adjoin K (pairwise_commute_range ρ)).is_comm.comm a b }

theorem exists_commRing_model3 (h3 : (3 : K) ≠ 0) (ρ : E →* Module.End K V) :
    ∃ (A : Type v) (_ : CommRing A) (φ : A →+* Module.End K V) (ι : E →* A) (c : A),
      Function.Injective φ ∧ (∀ x, φ (ι x) = ρ x) ∧ 3 * c = 1 := by
  let _ : CommRing (Algebra.adjoin K (Set.range ρ)) := adjCommRing3 ρ
  let φ : Algebra.adjoin K (Set.range ρ) →+* Module.End K V :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  have hφ : Function.Injective φ := Subtype.val_injective
  refine ⟨↥(Algebra.adjoin K (Set.range ρ)), adjCommRing3 ρ, φ,
    { toFun := fun x => ⟨ρ x, Algebra.subset_adjoin ⟨x, rfl⟩⟩,
      map_one' := Subtype.ext (map_one ρ), map_mul' := fun x y => Subtype.ext (map_mul ρ x y) },
    ⟨(3 : K)⁻¹ • 1, Subalgebra.smul_mem _ (Subalgebra.one_mem _) _⟩, hφ, fun _ => rfl, ?_⟩
  apply hφ
  rw [map_mul, map_one, map_ofNat]
  change (3 : Module.End K V) * ((3 : K)⁻¹ • 1) = 1
  ext v
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [← Nat.cast_ofNat, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  norm_num [h3]

theorem range_fp3 {A : Type*} [CommRing A] (φ : A →+* Module.End K V) {c z : A}
    (hc : 3 * c = 1) (hz : z ^ 3 = 1) :
    LinearMap.range (φ (fp3 c z)) = LinearMap.ker (φ z - 1) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    have h : (z - 1) * fp3 c z = 0 := by
      unfold fp3
      linear_combination c * hz
    have := congrArg (fun f : Module.End K V => f w) (congrArg φ h)
    simpa [map_mul, map_sub, map_one, Module.End.mul_apply] using this
  · intro hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    refine ⟨v, ?_⟩
    have e : fp3 c z = c * 1 + c * z + c * z ^ 2 := by unfold fp3; ring
    have hv2 : (φ (z ^ 2)) v = v := by
      rw [map_pow, pow_two, Module.End.mul_apply, hv, hv]
    have h1 : φ (c * 1 + c * z + c * z ^ 2) v = φ c v + φ c v + φ c v := by
      simp only [map_add, map_mul, mul_one, LinearMap.add_apply, Module.End.mul_apply, hv, hv2]
    have h2 : φ (3 * c) v = φ c v + φ c v + φ c v := by
      rw [show (3 : A) * c = c + c + c by ring, map_add, map_add, LinearMap.add_apply,
        LinearMap.add_apply]
    rw [e, h1, ← h2, hc, map_one, Module.End.one_apply]

theorem range_mul_of_idem {P Q : Module.End K V} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = Q * P) : LinearMap.range (P * Q) = LinearMap.range P ⊓ LinearMap.range Q := by
  have hfix : ∀ {R : Module.End K V}, R * R = R → ∀ v ∈ LinearMap.range R, R v = v := by
    rintro R hR _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, hR]
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨⟨Q w, rfl⟩, ⟨P w, ?_⟩⟩
    rw [← Module.End.mul_apply, ← hPQ]
  · rintro ⟨hvP, hvQ⟩
    refine ⟨v, ?_⟩
    rw [Module.End.mul_apply, hfix hQ v hvQ, hfix hP v hvP]

end Model

section Identities

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {A : Type*} [CommRing A] (φ : A →+* Module.End K V) {c : A} (hc : 3 * c = 1)
include hc

abbrev fixA (z : A) : Submodule K V := LinearMap.ker (φ z - 1)

theorem fp3_idem {z : A} (hz : z ^ 3 = 1) : φ (fp3 c z) * φ (fp3 c z) = φ (fp3 c z) := by
  rw [← map_mul, fp3_sq hc hz]

theorem idem_two {x y : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    φ (fp3 c x * fp3 c y) * φ (fp3 c x * fp3 c y) = φ (fp3 c x * fp3 c y) := by
  rw [← map_mul]
  congr 1
  linear_combination (fp3 c y) ^ 2 * fp3_sq hc hx + fp3 c x * fp3_sq hc hy

theorem idem_three {x y z : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) :
    φ (fp3 c x * fp3 c y * fp3 c z) * φ (fp3 c x * fp3 c y * fp3 c z) =
      φ (fp3 c x * fp3 c y * fp3 c z) := by
  rw [← map_mul]
  congr 1
  linear_combination (fp3 c y * fp3 c z) ^ 2 * fp3_sq hc hx +
    fp3 c x * (fp3 c z) ^ 2 * fp3_sq hc hy + fp3 c x * fp3 c y * fp3_sq hc hz

theorem range_fp3_two {x y : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    LinearMap.range (φ (fp3 c x * fp3 c y)) = fixA φ x ⊓ fixA φ y := by
  rw [map_mul, range_mul_of_idem (fp3_idem φ hc hx) (fp3_idem φ hc hy)
    (by rw [← map_mul, ← map_mul, mul_comm]), range_fp3 φ hc hx, range_fp3 φ hc hy]

theorem range_fp3_three {x y z : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) :
    LinearMap.range (φ (fp3 c x * fp3 c y * fp3 c z)) = fixA φ x ⊓ fixA φ y ⊓ fixA φ z := by
  rw [map_mul φ (fp3 c x * fp3 c y), range_mul_of_idem (idem_two φ hc hx hy)
    (fp3_idem φ hc hz) (by rw [← map_mul, ← map_mul, mul_comm]), range_fp3_two φ hc hx hy,
    range_fp3 φ hc hz]

theorem range_fp3_four {x y z w : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hw : w ^ 3 = 1) :
    LinearMap.range (φ (fp3 c x * fp3 c y * fp3 c z * fp3 c w)) =
      fixA φ x ⊓ fixA φ y ⊓ fixA φ z ⊓ fixA φ w := by
  rw [map_mul φ (fp3 c x * fp3 c y * fp3 c z), range_mul_of_idem (idem_three φ hc hx hy hz)
    (fp3_idem φ hc hw) (by rw [← map_mul, ← map_mul, mul_comm]), range_fp3_three φ hc hx hy hz,
    range_fp3 φ hc hw]

theorem rk_fp3 {z : A} (hz : z ^ 3 = 1) : rk (φ (fp3 c z)) = finrank K (fixA φ z) := by
  rw [rk, range_fp3 φ hc hz]

theorem rk_fp3_two {x y : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    rk (φ (fp3 c x * fp3 c y)) = finrank K ↥(fixA φ x ⊓ fixA φ y) := by
  rw [rk, range_fp3_two φ hc hx hy]

theorem rk_fp3_three {x y z : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) :
    rk (φ (fp3 c x * fp3 c y * fp3 c z)) =
      finrank K ↥(fixA φ x ⊓ fixA φ y ⊓ fixA φ z) := by
  rw [rk, range_fp3_three φ hc hx hy hz]

theorem rk_fp3_four {x y z w : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hw : w ^ 3 = 1) :
    rk (φ (fp3 c x * fp3 c y * fp3 c z * fp3 c w)) =
      finrank K ↥(fixA φ x ⊓ fixA φ y ⊓ fixA φ z ⊓ fixA φ w) := by
  rw [rk, range_fp3_four φ hc hx hy hz hw]

omit hc in
theorem fp3_products {g h : A} (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) :
    fp3 c g * fp3 c (g * h) = fp3 c g * fp3 c h ∧
      fp3 c g * fp3 c (g * h ^ 2) = fp3 c g * fp3 c h ∧
      fp3 c h * fp3 c (g * h) = fp3 c g * fp3 c h ∧
      fp3 c h * fp3 c (g * h ^ 2) = fp3 c g * fp3 c h ∧
      fp3 c (g * h) * fp3 c (g * h ^ 2) = fp3 c g * fp3 c h :=
  ⟨fp3_mul_eq (ring_fixProj_mul_g_gh hg), fp3_mul_eq (ring_fixProj_mul_g_gh2 hg hh),
    fp3_mul_eq (ring_fixProj_mul_h_gh hh), fp3_mul_eq (ring_fixProj_mul_h_gh2 hh),
    fp3_mul_eq (ring_fixProj_mul_gh_gh2 hg hh)⟩

omit hc in
theorem cube_mul {g h : A} (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) : (g * h) ^ 3 = 1 := by
  rw [mul_pow, hg, hh, one_mul]

omit hc in
theorem cube_mul_sq {g h : A} (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) : (g * h ^ 2) ^ 3 = 1 := by
  rw [mul_pow, hg, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hh, one_pow, one_mul]

theorem card_fix_one {g h : A} (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) :
    finrank K (fixA φ g) + finrank K (fixA φ h) + finrank K (fixA φ (g * h)) +
        finrank K (fixA φ (g * h ^ 2)) =
      finrank K V + 3 * finrank K ↥(fixA φ g ⊓ fixA φ h) := by
  obtain ⟨p13, p14, p23, p24, p34⟩ := fp3_products (c := c) hg hh
  have hf := rank_formula3 φ (fp3_sq hc hg) (fp3_sq hc hh) (fp3_sq hc (cube_mul hg hh))
    (fp3_sq hc (cube_mul_sq hg hh)) rfl p13 p14 p23 p24 p34
    (P := 1) (by rw [fp3_sum hc hh])
  rw [rk_fp3 φ hc hg, rk_fp3 φ hc hh, rk_fp3 φ hc (cube_mul hg hh),
    rk_fp3 φ hc (cube_mul_sq hg hh), rk_fp3_two φ hc hg hh, map_one] at hf
  rw [hf, rk, LinearMap.range_eq_top.mpr fun v => ⟨v, rfl⟩, finrank_top]

theorem card_fix_two {x g h : A} (hx : x ^ 3 = 1) (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) :
    finrank K ↥(fixA φ x ⊓ fixA φ g) + finrank K ↥(fixA φ x ⊓ fixA φ h) +
        finrank K ↥(fixA φ x ⊓ fixA φ (g * h)) + finrank K ↥(fixA φ x ⊓ fixA φ (g * h ^ 2)) =
      finrank K (fixA φ x) + 3 * finrank K ↥(fixA φ x ⊓ fixA φ g ⊓ fixA φ h) := by
  obtain ⟨p13, p14, p23, p24, p34⟩ := fp3_products (c := c) hg hh
  have hxx := fp3_sq hc hx
  have hI : ∀ a : A, a * a = a → (fp3 c x * a) * (fp3 c x * a) = fp3 c x * a := fun a ha => by
    linear_combination a ^ 2 * hxx + fp3 c x * ha
  have hP : ∀ a b : A, a * b = fp3 c g * fp3 c h →
      (fp3 c x * a) * (fp3 c x * b) = fp3 c x * fp3 c g * fp3 c h := fun a b hab => by
    linear_combination (a * b) * hxx + fp3 c x * hab
  have hf := rank_formula3 φ (hI _ (fp3_sq hc hg)) (hI _ (fp3_sq hc hh))
    (hI _ (fp3_sq hc (cube_mul hg hh))) (hI _ (fp3_sq hc (cube_mul_sq hg hh)))
    (hP _ _ rfl) (hP _ _ p13) (hP _ _ p14) (hP _ _ p23) (hP _ _ p24) (hP _ _ p34)
    (P := fp3 c x) (by linear_combination fp3 c x * fp3_sum (g := g) hc hh)
  rw [rk_fp3_two φ hc hx hg, rk_fp3_two φ hc hx hh, rk_fp3_two φ hc hx (cube_mul hg hh),
    rk_fp3_two φ hc hx (cube_mul_sq hg hh), rk_fp3 φ hc hx, rk_fp3_three φ hc hx hg hh] at hf
  exact hf

theorem card_fix_three {x y g h : A} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hg : g ^ 3 = 1)
    (hh : h ^ 3 = 1) :
    finrank K ↥(fixA φ x ⊓ fixA φ y ⊓ fixA φ g) + finrank K ↥(fixA φ x ⊓ fixA φ y ⊓ fixA φ h) +
        finrank K ↥(fixA φ x ⊓ fixA φ y ⊓ fixA φ (g * h)) +
        finrank K ↥(fixA φ x ⊓ fixA φ y ⊓ fixA φ (g * h ^ 2)) =
      finrank K ↥(fixA φ x ⊓ fixA φ y) +
        3 * finrank K ↥(fixA φ x ⊓ fixA φ y ⊓ fixA φ g ⊓ fixA φ h) := by
  obtain ⟨p13, p14, p23, p24, p34⟩ := fp3_products (c := c) hg hh
  have hxy : (fp3 c x * fp3 c y) * (fp3 c x * fp3 c y) = fp3 c x * fp3 c y := by
    linear_combination (fp3 c y) ^ 2 * fp3_sq hc hx + fp3 c x * fp3_sq hc hy
  have hI : ∀ a : A, a * a = a →
      (fp3 c x * fp3 c y * a) * (fp3 c x * fp3 c y * a) = fp3 c x * fp3 c y * a :=
    fun a ha => by
      linear_combination a ^ 2 * hxy + (fp3 c x * fp3 c y) * ha
  have hP : ∀ a b : A, a * b = fp3 c g * fp3 c h →
      (fp3 c x * fp3 c y * a) * (fp3 c x * fp3 c y * b) =
        fp3 c x * fp3 c y * fp3 c g * fp3 c h := fun a b hab => by
    linear_combination (a * b) * hxy + (fp3 c x * fp3 c y) * hab
  have hf := rank_formula3 φ (hI _ (fp3_sq hc hg)) (hI _ (fp3_sq hc hh))
    (hI _ (fp3_sq hc (cube_mul hg hh))) (hI _ (fp3_sq hc (cube_mul_sq hg hh)))
    (hP _ _ rfl) (hP _ _ p13) (hP _ _ p14) (hP _ _ p23) (hP _ _ p24) (hP _ _ p34)
    (P := fp3 c x * fp3 c y)
    (by linear_combination (fp3 c x * fp3 c y) * fp3_sum (g := g) hc hh)
  rw [rk_fp3_three φ hc hx hy hg, rk_fp3_three φ hc hx hy hh,
    rk_fp3_three φ hc hx hy (cube_mul hg hh), rk_fp3_three φ hc hx hy (cube_mul_sq hg hh),
    rk_fp3_two φ hc hx hy, rk_fp3_four φ hc hx hy hg hh] at hf
  exact hf

end Identities

section Descent

open scoped Pointwise

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {E : Type*} [Group E] [IsMulCommutative E] [Finite E]

omit [IsMulCommutative E] [Finite E] in
theorem card_zpowers_le_three (hexp : ∀ x : E, x ^ 3 = 1) (x : E) :
    Nat.card (Subgroup.zpowers x) ≤ 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) (hexp x)

omit [Finite E] in
theorem card_sup_zpowers_le (hexp : ∀ x : E, x ^ 3 = 1) (H : Subgroup E) (y : E) :
    Nat.card ↥(H ⊔ Subgroup.zpowers y) ≤ Nat.card H * 3 := by
  have e : Nat.card ↥(H ⊔ Subgroup.zpowers y) =
      Nat.card ((H : Set E) * (Subgroup.zpowers y : Set E)) := by
    rw [← Subgroup.mul_normal]
    rfl
  rw [e]
  refine (Set.natCard_mul_le).trans (Nat.mul_le_mul le_rfl ?_)
  exact card_zpowers_le_three hexp y

omit [IsMulCommutative E] in
theorem exists_not_mem_of_card_lt {H : Subgroup E} (h : Nat.card H < Nat.card E) :
    ∃ z, z ∉ H := by
  by_contra hall
  push Not at hall
  have hle := Subgroup.card_le_of_le (show (⊤ : Subgroup E) ≤ H from fun x _ => hall x)
  rw [Subgroup.card_top] at hle
  omega

omit [IsMulCommutative E] [Finite E] in
theorem not_mem_mul_facts {H : Subgroup E} (hexp : ∀ x : E, x ^ 3 = 1) {y z : E}
    (hy : y ∈ H) (hz : z ∉ H) : y * z ∉ H ∧ y * z ^ 2 ∉ H := by
  refine ⟨fun h => hz ?_, fun h => hz ?_⟩
  · have : z = y⁻¹ * (y * z) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem hy) h
  · have hz2 : z ^ 2 ∈ H := by
      have : z ^ 2 = y⁻¹ * (y * z ^ 2) := by group
      rw [this]
      exact H.mul_mem (H.inv_mem hy) h
    have : z = (z ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hexp z, one_mul]
    rw [this]
    exact H.pow_mem hz2 2

theorem exists_fixDim_six (h3 : (3 : K) ≠ 0) (hV : finrank K V = 8) (ρ : E →* Module.End K V)
    (hρ : Function.Injective ρ) (hexp : ∀ x : E, x ^ 3 = 1) (hcard : 81 ≤ Nat.card E)
    (heven : ∀ x : E, Even (finrank K (LinearMap.ker (ρ x - 1)))) :
    ∃ x : E, x ≠ 1 ∧ finrank K (LinearMap.ker (ρ x - 1)) = 6 := by
  classical
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨A, _, φ, ι, c, hφ, hφι, hc⟩ := exists_commRing_model3 h3 ρ
  set F : E → Submodule K V := fun x => LinearMap.ker (ρ x - 1) with hF
  have hFA : ∀ x, fixA φ (ι x) = F x := fun x => by simp only [fixA, hF, hφι]
  have hι3 : ∀ x, ι x ^ 3 = 1 := fun x => by rw [← map_pow, hexp, map_one]
  have e1 : ∀ g h : E, ι g * ι h = ι (g * h) := fun g h => (map_mul ι g h).symm
  have e2 : ∀ g h : E, ι g * ι h ^ 2 = ι (g * h ^ 2) := fun g h => by rw [map_mul, map_pow]
  have R1 : ∀ g h : E, finrank K (F g) + finrank K (F h) + finrank K (F (g * h)) +
      finrank K (F (g * h ^ 2)) = 8 + 3 * finrank K ↥(F g ⊓ F h) := by
    intro g h
    have := card_fix_one φ hc (hι3 g) (hι3 h)
    rw [e1, e2, hFA, hFA, hFA, hFA, hV] at this
    exact this
  have R2 : ∀ x g h : E, finrank K ↥(F x ⊓ F g) + finrank K ↥(F x ⊓ F h) +
      finrank K ↥(F x ⊓ F (g * h)) + finrank K ↥(F x ⊓ F (g * h ^ 2)) =
        finrank K (F x) + 3 * finrank K ↥(F x ⊓ F g ⊓ F h) := by
    intro x g h
    have := card_fix_two φ hc (hι3 x) (hι3 g) (hι3 h)
    rw [e1, e2, hFA, hFA, hFA, hFA, hFA] at this
    exact this
  have R3 : ∀ x y g h : E, finrank K ↥(F x ⊓ F y ⊓ F g) + finrank K ↥(F x ⊓ F y ⊓ F h) +
      finrank K ↥(F x ⊓ F y ⊓ F (g * h)) + finrank K ↥(F x ⊓ F y ⊓ F (g * h ^ 2)) =
        finrank K ↥(F x ⊓ F y) + 3 * finrank K ↥(F x ⊓ F y ⊓ F g ⊓ F h) := by
    intro x y g h
    have := card_fix_three φ hc (hι3 x) (hι3 y) (hι3 g) (hι3 h)
    rw [e1, e2, hFA, hFA, hFA, hFA, hFA, hFA] at this
    exact this
  have hFmul : ∀ a b : E, F a ⊓ F b ≤ F (a * b) := by
    intro a b v hv
    obtain ⟨ha, hb⟩ := Submodule.mem_inf.mp hv
    simp only [hF, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  have hFsq : ∀ a b : E, F a ⊓ F b ≤ F (a * b ^ 2) := by
    intro a b
    have hb2 : F b ≤ F (b ^ 2) := by
      rw [pow_two]
      exact (le_inf le_rfl le_rfl).trans (hFmul b b)
    exact (inf_le_inf_left _ hb2).trans (hFmul a (b ^ 2))
  have hF8 : ∀ x, finrank K (F x) = 8 → x = 1 := by
    intro x hx
    have htop : F x = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hx, hV])
    apply hρ
    rw [map_one]
    have h0 : ρ x - 1 = 0 := LinearMap.ker_eq_top.mp htop
    exact sub_eq_zero.mp h0
  have hFle : ∀ x, finrank K (F x) ≤ 8 := fun x => hV ▸ Submodule.finrank_le _
  have E1 : ∀ x, finrank K (F x) % 2 = 0 := fun x => Nat.even_iff.mp (heven x)
  have E2 : ∀ a b, finrank K ↥(F a ⊓ F b) % 2 = 0 := by
    intro a b
    have := R1 a b
    have := E1 a
    have := E1 b
    have := E1 (a * b)
    have := E1 (a * b ^ 2)
    omega
  have E3 : ∀ a b z, finrank K ↥(F a ⊓ F b ⊓ F z) % 2 = 0 := by
    intro a b z
    have := R2 a b z
    have := E1 a
    have := E2 a b
    have := E2 a z
    have := E2 a (b * z)
    have := E2 a (b * z ^ 2)
    omega
  obtain ⟨x0, hx0⟩ : ∃ x0 : E, x0 ≠ 1 := by
    have h1 : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  obtain ⟨x₁, hx₁mem, hx₁max⟩ := Finset.exists_max_image (Finset.univ.filter (· ≠ 1))
    (fun x => finrank K (F x)) ⟨x0, by simp [hx0]⟩
  have hx₁ : x₁ ≠ 1 := (Finset.mem_filter.mp hx₁mem).2
  have hmax1 : ∀ x, x ≠ 1 → finrank K (F x) ≤ finrank K (F x₁) := fun x hx =>
    hx₁max x (by simp [hx])
  refine ⟨x₁, hx₁, ?_⟩
  by_contra hne
  set d₁ := finrank K (F x₁) with hd₁def
  have hd₁8 : d₁ ≠ 8 := fun h => hx₁ (hF8 x₁ h)
  have hd₁4 : d₁ ≤ 4 := by
    have := E1 x₁
    have := hFle x₁
    omega
  have step1 : ∀ y, y ∉ Subgroup.zpowers x₁ → finrank K ↥(F x₁ ⊓ F y) + 2 ≤ d₁ := by
    intro y hy
    have hlt : finrank K ↥(F x₁ ⊓ F y) < d₁ := by
      by_contra hge
      push Not at hge
      have hle : F x₁ ⊓ F y = F x₁ := Submodule.eq_of_le_of_finrank_le inf_le_left hge
      have hsub : F x₁ ≤ F y := by
        rw [← hle]
        exact inf_le_right
      obtain ⟨hn1, hn2⟩ := not_mem_mul_facts hexp (Subgroup.mem_zpowers x₁) hy
      have hy1 : y ≠ 1 := fun h => hy (h ▸ one_mem _)
      have hxy1 : x₁ * y ≠ 1 := fun h => hn1 (h ▸ one_mem _)
      have hxy21 : x₁ * y ^ 2 ≠ 1 := fun h => hn2 (h ▸ one_mem _)
      have d1 : finrank K (F y) = d₁ :=
        le_antisymm (hmax1 y hy1) (Submodule.finrank_mono hsub)
      have d2 : finrank K (F (x₁ * y)) = d₁ := le_antisymm (hmax1 _ hxy1)
        (Submodule.finrank_mono ((le_inf le_rfl hsub).trans (hFmul x₁ y)))
      have d3 : finrank K (F (x₁ * y ^ 2)) = d₁ := le_antisymm (hmax1 _ hxy21)
        (Submodule.finrank_mono ((le_inf le_rfl hsub).trans (hFsq x₁ y)))
      have := R1 x₁ y
      rw [d1, d2, d3, hle] at this
      omega
    have := E2 x₁ y
    have := E1 x₁
    omega
  obtain ⟨y0, hy0⟩ := exists_not_mem_of_card_lt (H := Subgroup.zpowers x₁)
    (by have := card_zpowers_le_three hexp x₁; omega)
  obtain ⟨y₁, hy₁mem, hy₁max⟩ := Finset.exists_max_image
    (Finset.univ.filter (· ∉ Subgroup.zpowers x₁)) (fun y => finrank K ↥(F x₁ ⊓ F y))
    ⟨y0, by simp [hy0]⟩
  have hy₁ : y₁ ∉ Subgroup.zpowers x₁ := (Finset.mem_filter.mp hy₁mem).2
  have hmax2 : ∀ y, y ∉ Subgroup.zpowers x₁ →
      finrank K ↥(F x₁ ⊓ F y) ≤ finrank K ↥(F x₁ ⊓ F y₁) := fun y hy =>
    hy₁max y (by simp [hy])
  set d₂ := finrank K ↥(F x₁ ⊓ F y₁) with hd₂def
  have hd₂ : d₂ + 2 ≤ d₁ := step1 y₁ hy₁
  set H₂ := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers y₁ with hH₂
  have hH₂card : Nat.card H₂ ≤ 9 := by
    have h1 := card_sup_zpowers_le hexp (Subgroup.zpowers x₁) y₁
    rw [← hH₂] at h1
    have := card_zpowers_le_three hexp x₁
    omega
  have step2 : ∀ z, z ∉ H₂ → finrank K ↥(F x₁ ⊓ F y₁ ⊓ F z) + 2 ≤ d₂ := by
    intro z hz
    have hlt : finrank K ↥(F x₁ ⊓ F y₁ ⊓ F z) < d₂ := by
      by_contra hge
      push Not at hge
      have hle : F x₁ ⊓ F y₁ ⊓ F z = F x₁ ⊓ F y₁ :=
        Submodule.eq_of_le_of_finrank_le inf_le_left hge
      have hsub : F x₁ ⊓ F y₁ ≤ F z := by
        rw [← hle]
        exact inf_le_right
      have hzx : z ∉ Subgroup.zpowers x₁ := fun h => hz (Subgroup.mem_sup_left h)
      obtain ⟨hn1, hn2⟩ := not_mem_mul_facts hexp (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers y₁) : y₁ ∈ H₂) hz
      have hyz : y₁ * z ∉ Subgroup.zpowers x₁ := fun h => hn1 (Subgroup.mem_sup_left h)
      have hyz2 : y₁ * z ^ 2 ∉ Subgroup.zpowers x₁ := fun h => hn2 (Subgroup.mem_sup_left h)
      have hV : F x₁ ⊓ F y₁ ≤ F y₁ ⊓ F z := le_inf inf_le_right hsub
      have d1 : finrank K ↥(F x₁ ⊓ F z) = d₂ := le_antisymm (hmax2 z hzx)
        (Submodule.finrank_mono (le_inf inf_le_left hsub))
      have d2 : finrank K ↥(F x₁ ⊓ F (y₁ * z)) = d₂ := le_antisymm (hmax2 _ hyz)
        (Submodule.finrank_mono (le_inf inf_le_left (hV.trans (hFmul y₁ z))))
      have d3 : finrank K ↥(F x₁ ⊓ F (y₁ * z ^ 2)) = d₂ := le_antisymm (hmax2 _ hyz2)
        (Submodule.finrank_mono (le_inf inf_le_left (hV.trans (hFsq y₁ z))))
      have := R2 x₁ y₁ z
      rw [d1, d2, d3, hle] at this
      omega
    have := E3 x₁ y₁ z
    have := E2 x₁ y₁
    omega
  obtain ⟨z₁, hz₁⟩ := exists_not_mem_of_card_lt (H := H₂) (by omega)
  set H₃ := H₂ ⊔ Subgroup.zpowers z₁ with hH₃
  have hH₃card : Nat.card H₃ ≤ 27 := by
    have h1 := card_sup_zpowers_le hexp H₂ z₁
    rw [← hH₃] at h1
    omega
  obtain ⟨z₂, hz₂⟩ := exists_not_mem_of_card_lt (H := H₃) (by omega)
  have hz₂' : z₂ ∉ H₂ := fun h => hz₂ (Subgroup.mem_sup_left h)
  obtain ⟨hn1, hn2⟩ := not_mem_mul_facts hexp (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers z₁) : z₁ ∈ H₃) hz₂
  have hzz : z₁ * z₂ ∉ H₂ := fun h => hn1 (Subgroup.mem_sup_left h)
  have hzz2 : z₁ * z₂ ^ 2 ∉ H₂ := fun h => hn2 (Subgroup.mem_sup_left h)
  have := R3 x₁ y₁ z₁ z₂
  have := step2 z₁ hz₁
  have := step2 z₂ hz₂'
  have := step2 _ hzz
  have := step2 _ hzz2
  omega

end Descent

end CFSG.HardMathSupport.Timmesfeld.DFour
