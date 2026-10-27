module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Comm

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

variable {K : Type} [Field K]

section Basic

variable [CharP K 2] (σ : K ≃+* K)

theorem add_self_d4 (c : K) : c + c = 0 :=
  CharTwo.add_self_eq_zero c

theorem mul_eq_comm_mul_d4 {G : Type*} [Group G] (x y : G) : x * y = ⁅x, y⁆ * y * x := by
  simp only [commutatorElement_def]
  group

theorem mul_mul_of_commute_d4 {G : Type*} [Group G] {x y : G} (h : Commute x y) (r : G) :
    x * (y * r) = y * (x * r) := by
  rw [← mul_assoc, h.eq, mul_assoc]

theorem mul_mul_of_eq_d4 {G : Type*} [Group G] {x y z : G} (h : x * y = y * x * z) (r : G) :
    x * (y * r) = y * (x * (z * r)) := by
  rw [← mul_assoc, h]
  group

theorem d4x₁_mul_self
    (c : K) : d4x₁ K σ c * d4x₁ K σ c = 1 := by
  rw [← d4x₁_add, add_self_d4, d4x₁_zero]

theorem d4x₃_mul_self
    (c : K) : d4x₃ K σ c * d4x₃ K σ c = 1 := by
  rw [← d4x₃_add, add_self_d4, d4x₃_zero]

theorem d4x₄_mul_self
    (c : K) : d4x₄ K σ c * d4x₄ K σ c = 1 := by
  rw [← d4x₄_add, add_self_d4, d4x₄_zero]

variable (K) in
theorem d4x₂_mul_self
    (c : K) : d4x₂ K c * d4x₂ K c = 1 := by
  rw [← d4x₂_add, add_self_d4, d4x₂, pinnedX_zero]

variable (K) in
theorem d4x₆_mul_self
    (c : K) : d4x₆ K c * d4x₆ K c = 1 := by
  rw [← d4x₆_add, add_self_d4, d4x₆, pinnedX_zero]

omit [CharP K 2] in
variable (K) in
theorem d4x₂_zero : d4x₂ K 0 = 1 :=
  pinnedX_zero _ _ _

omit [CharP K 2] in
variable (K) in
theorem d4x₅_zero : d4x₅ K 0 = 1 :=
  pinnedX_zero _ _ _

omit [CharP K 2] in
variable (K) in
theorem d4x₆_zero : d4x₆ K 0 = 1 :=
  pinnedX_zero _ _ _

theorem d4x₁_inv
    (c : K) : (d4x₁ K σ c)⁻¹ = d4x₁ K σ c :=
  inv_eq_of_mul_eq_one_right (d4x₁_mul_self σ c)

theorem d4x₃_inv
    (c : K) : (d4x₃ K σ c)⁻¹ = d4x₃ K σ c :=
  inv_eq_of_mul_eq_one_right (d4x₃_mul_self σ c)

theorem d4x₄_inv
    (c : K) : (d4x₄ K σ c)⁻¹ = d4x₄ K σ c :=
  inv_eq_of_mul_eq_one_right (d4x₄_mul_self σ c)

variable (K) in
theorem d4x₂_inv
    (c : K) : (d4x₂ K c)⁻¹ = d4x₂ K c :=
  inv_eq_of_mul_eq_one_right (d4x₂_mul_self K c)

end Basic

section Collect

variable [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4x₅_mul_d4x₂
    (e b : K) :
    d4x₅ K e * d4x₂ K b = d4x₂ K b * d4x₅ K e * d4x₆ K (e * b) := by
  rw [mul_eq_comm_mul_d4, comm_d4x₅_d4x₂, (commute_d4x₆_d4x₂ K (e * b) b).eq, mul_assoc,
    (commute_d4x₅_d4x₆ K e (e * b)).symm.eq, ← mul_assoc]

include hσ in
theorem d4x₄_mul_d4x₃
    (d c : K) :
    d4x₄ K σ d * d4x₃ K σ c =
      d4x₃ K σ c * d4x₄ K σ d * d4x₆ K (d * c + σ (d * c) + σ (σ (d * c))) := by
  rw [mul_eq_comm_mul_d4, comm_d4x₄_d4x₃ σ hσ,
    (commute_d4x₆_d4x₃ σ (d * c + σ (d * c) + σ (σ (d * c))) c).eq, mul_assoc,
    (commute_d4x₄_d4x₆ σ d (d * c + σ (d * c) + σ (σ (d * c)))).symm.eq, ← mul_assoc]

end Collect

section Vr

variable [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

variable (K) in
@[expose] noncomputable def d4v
    (b c d e f : K) : ModGL TwistTag.D4.tag K :=
  d4x₂ K b * d4x₃ K σ c * d4x₄ K σ d * d4x₅ K e * d4x₆ K f

omit [CharP K 2] in
theorem d4x_merge
    (a a' : K) (r : ModGL TwistTag.D4.tag K) :
    d4x₂ K a * (d4x₂ K a' * r) = d4x₂ K (a + a') * r ∧
    d4x₃ K σ a * (d4x₃ K σ a' * r) = d4x₃ K σ (a + a') * r ∧
    d4x₄ K σ a * (d4x₄ K σ a' * r) = d4x₄ K σ (a + a') * r ∧
    d4x₅ K a * (d4x₅ K a' * r) = d4x₅ K (a + a') * r ∧
    d4x₆ K a * (d4x₆ K a' * r) = d4x₆ K (a + a') * r ∧
    d4x₆ K a * d4x₆ K a' = d4x₆ K (a + a') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, (d4x₆_add K a a').symm⟩ <;> rw [← mul_assoc]
  · rw [d4x₂_add]
  · rw [d4x₃_add]
  · rw [d4x₄_add]
  · rw [d4x₅_add]
  · rw [d4x₆_add]

omit [CharP K 2] in
theorem d4v_mul_d4x₆
    (b c d e f f' : K) :
    d4v K σ b c d e f * d4x₆ K f' = d4v K σ b c d e (f + f') := by
  simp only [d4v, mul_assoc, (d4x_merge σ f f' 1).2.2.2.2.2]

theorem d4v_mul_d4x₅
    (b c d e f e' : K) :
    d4v K σ b c d e f * d4x₅ K e' = d4v K σ b c d (e + e') f := by
  simp only [d4v, mul_assoc]
  rw [(commute_d4x₅_d4x₆ K e' f).symm.eq, (d4x_merge σ e e' _).2.2.2.1]

theorem d4v_mul_d4x₄
    (b c d e f d' : K) :
    d4v K σ b c d e f * d4x₄ K σ d' = d4v K σ b c (d + d') e f := by
  simp only [d4v, mul_assoc]
  rw [(commute_d4x₄_d4x₆ σ d' f).symm.eq, mul_mul_of_commute_d4 (commute_d4x₅_d4x₄ σ e d'),
    (d4x_merge σ d d' _).2.2.1]

include hσ in
theorem d4v_mul_d4x₃
    (b c d e f c' : K) :
    d4v K σ b c d e f * d4x₃ K σ c' =
      d4v K σ b (c + c') d e ((d * c' + σ (d * c') + σ (σ (d * c'))) + f) := by
  simp only [d4v, mul_assoc]
  rw [(commute_d4x₆_d4x₃ σ f c').eq, mul_mul_of_commute_d4 (commute_d4x₅_d4x₃ σ e c'),
    mul_mul_of_eq_d4 (d4x₄_mul_d4x₃ σ hσ d c'), (d4x_merge σ c c' _).2.1,
    mul_mul_of_commute_d4 (commute_d4x₅_d4x₆ K e _).symm, (d4x_merge σ _ f 1).2.2.2.2.2]

theorem d4v_mul_d4x₂
    (b c d e f b' : K) :
    d4v K σ b c d e f * d4x₂ K b' = d4v K σ (b + b') c d e (e * b' + f) := by
  simp only [d4v, mul_assoc]
  rw [(commute_d4x₆_d4x₂ K f b').eq, mul_mul_of_eq_d4 (d4x₅_mul_d4x₂ e b'),
    mul_mul_of_commute_d4 (commute_d4x₄_d4x₂ σ d b'),
    mul_mul_of_commute_d4 (commute_d4x₃_d4x₂ σ c b'), (d4x_merge σ b b' _).1,
    (d4x_merge σ _ f 1).2.2.2.2.2]

include hσ in
theorem d4v_mul
    (b c d e f b' c' d' e' f' : K) :
    d4v K σ b c d e f * d4v K σ b' c' d' e' f' = d4v K σ (b + b') (c + c') (d + d') (e + e')
      ((d * c' + σ (d * c') + σ (σ (d * c'))) + (e * b' + f) + f') := by
  rw [show d4v K σ b' c' d' e' f' = d4x₂ K b' * d4x₃ K σ c' * d4x₄ K σ d' * d4x₅ K e' *
      d4x₆ K f' from rfl]
  simp only [← mul_assoc]
  rw [d4v_mul_d4x₂, d4v_mul_d4x₃ σ hσ, d4v_mul_d4x₄, d4v_mul_d4x₅, d4v_mul_d4x₆]

omit [CharP K 2] in
theorem d4v_single
    (a : K) :
    d4v K σ a 0 0 0 0 = d4x₂ K a ∧ d4v K σ 0 a 0 0 0 = d4x₃ K σ a ∧
      d4v K σ 0 0 a 0 0 = d4x₄ K σ a ∧ d4v K σ 0 0 0 a 0 = d4x₅ K a ∧
      d4v K σ 0 0 0 0 a = d4x₆ K a := by
  simp only [d4v, d4x₂_zero, d4x₃_zero, d4x₄_zero, d4x₅_zero, d4x₆_zero, mul_one, one_mul]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

omit [CharP K 2] in
theorem d4v_congr
    {b c d e f b' c' d' e' f' : K} (hb : b = b') (hc : c = c')
    (hd : d = d') (he : e = e') (hf : f = f') : d4v K σ b c d e f = d4v K σ b' c' d' e' f' := by
  rw [hb, hc, hd, he, hf]

include hσ in
theorem d4v_mul_self
    (b c d e f : K) :
    d4v K σ b c d e f * d4v K σ b c d e f =
      d4x₆ K (b * e + (c * d + σ (c * d) + σ (σ (c * d)))) := by
  rw [d4v_mul σ hσ, ← (d4v_single σ _).2.2.2.2]
  refine d4v_congr σ (add_self_d4 b) (add_self_d4 c) (add_self_d4 d) (add_self_d4 e) ?_
  have hf : f + f = 0 := add_self_d4 f
  rw [mul_comm d c]
  linear_combination (mul_comm e b + hf)

include hσ in
theorem d4x₂_conj_d4v
    (β b c d e f : K) :
    d4x₂ K β * d4v K σ b c d e f * (d4x₂ K β)⁻¹ = d4v K σ b c d e (e * β + f) := by
  rw [d4x₂_inv, ← (d4v_single σ β).1, d4v_mul σ hσ, d4v_mul σ hσ]
  refine d4v_congr σ ?_ (by ring) (by ring) (by ring) ?_
  · linear_combination add_self_d4 β
  · simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add]

include hσ in
theorem d4x₃_conj_d4v
    (γ b c d e f : K) :
    d4x₃ K σ γ * d4v K σ b c d e f * (d4x₃ K σ γ)⁻¹ =
      d4v K σ b c d e (d * γ + σ (d * γ) + σ (σ (d * γ)) + f) := by
  rw [d4x₃_inv, ← (d4v_single σ γ).2.1, d4v_mul σ hσ, d4v_mul σ hσ]
  refine d4v_congr σ (by ring) ?_ (by ring) (by ring) ?_
  · linear_combination add_self_d4 γ
  · simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add]

include hσ in
theorem trialityOuterRep_conj_d4v
    (b c d e f : K) :
    trialityOuterRep K * d4v K σ b c d e f * (trialityOuterRep K)⁻¹ =
      d4v K σ e d c b (b * e + (c * d + σ (c * d) + σ (σ (c * d))) + f) := by
  rw [← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply,
    trialityOuterRep_conj_d4x₂, trialityOuterRep_conj_d4x₃, trialityOuterRep_conj_d4x₄,
    trialityOuterRep_conj_d4x₅, trialityOuterRep_conj_d4x₆]
  rw [← (d4v_single σ b).2.2.2.1, ← (d4v_single σ c).2.2.1, ← (d4v_single σ d).2.1,
    ← (d4v_single σ e).1, ← (d4v_single σ f).2.2.2.2, d4v_mul σ hσ, d4v_mul σ hσ, d4v_mul σ hσ,
    d4v_mul σ hσ]
  refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
  simp only [mul_zero, map_zero, add_zero, zero_add]

include hσ in
theorem trialityMiddleRep_conj_d4v
    (d e f : K) :
    trialityMiddleRep K * d4v K σ 0 0 d e f * (trialityMiddleRep K)⁻¹ = d4v K σ 0 0 d f e := by
  rw [← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply,
    d4x₂_zero, d4x₃_zero, mul_one, mul_inv_cancel, one_mul,
    trialityMiddleRep_conj_d4x₄, trialityMiddleRep_conj_d4x₅, trialityMiddleRep_conj_d4x₆]
  rw [← (d4v_single σ d).2.2.1, ← (d4v_single σ e).2.2.2.2, ← (d4v_single σ f).2.2.2.1, one_mul,
    d4v_mul σ hσ, d4v_mul σ hσ]
  refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
  simp only [mul_zero, map_zero, add_zero, zero_add]

omit [CharP K 2] in
theorem d4x₂_eq_d4v
    (a : K) : d4x₂ K a = d4v K σ a 0 0 0 0 := by
  simp only [d4v, d4x₃_zero, d4x₄_zero, d4x₅_zero, d4x₆_zero, mul_one]

omit [CharP K 2] in
theorem d4x₃_eq_d4v
    (a : K) : d4x₃ K σ a = d4v K σ 0 a 0 0 0 := by
  simp only [d4v, d4x₂_zero, d4x₄_zero, d4x₅_zero, d4x₆_zero, mul_one, one_mul]

omit [CharP K 2] in
theorem d4x₄_eq_d4v
    (a : K) : d4x₄ K σ a = d4v K σ 0 0 a 0 0 := by
  simp only [d4v, d4x₂_zero, d4x₃_zero, d4x₅_zero, d4x₆_zero, mul_one, one_mul]

omit [CharP K 2] in
theorem d4x₅_eq_d4v
    (a : K) : d4x₅ K a = d4v K σ 0 0 0 a 0 := by
  simp only [d4v, d4x₂_zero, d4x₃_zero, d4x₄_zero, d4x₆_zero, mul_one, one_mul]

omit [CharP K 2] in
theorem d4x₆_eq_d4v
    (a : K) : d4x₆ K a = d4v K σ 0 0 0 0 a := by
  simp only [d4v, d4x₂_zero, d4x₃_zero, d4x₄_zero, d4x₅_zero, one_mul]

omit [CharP K 2] in
theorem d4v_zero :
    d4v K σ 0 0 0 0 0 = 1 := by
  simp only [d4v, d4x₂_zero, d4x₃_zero, d4x₄_zero, d4x₅_zero, d4x₆_zero, mul_one]

include hσ in
theorem d4v_inv
    (b c d e f : K) :
    (d4v K σ b c d e f)⁻¹ = d4v K σ b c d e (b * e + (c * d + σ (c * d) + σ (σ (c * d))) + f) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [d4v_mul σ hσ, ← d4v_zero σ]
  refine d4v_congr σ (add_self_d4 b) (add_self_d4 c) (add_self_d4 d) (add_self_d4 e) ?_
  rw [mul_comm d c, mul_comm e b]
  linear_combination ((c * d + σ (c * d) + σ (σ (c * d))) + b * e + f) * (CharTwo.two_eq_zero : (2
      : K) = 0)

include hσ in
theorem d4x₁_conj_d4v
    (s b c d e f : K) (hb : σ b = b) :
    ∃ F, d4x₁ K σ s * d4v K σ b c d e f * (d4x₁ K σ s)⁻¹ = d4v K σ b (c + b * s)
      (d + b * (σ s * σ (σ s)) + (σ s * σ (σ c) + σ (σ s) * σ c))
      (e + b * (s * σ s * σ (σ s)) + (σ s * σ (σ s) * c + σ (σ s * σ (σ s) * c) +
        σ (σ (σ s * σ (σ s) * c))) + (s * d + σ (s * d) + σ (σ (s * d)))) F := by
  have hconj : ∀ y, d4x₁ K σ s * y * (d4x₁ K σ s)⁻¹ = ⁅d4x₁ K σ s, y⁆ * y := fun y => by
    simp only [commutatorElement_def]
    group
  rw [← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, hconj, hconj,
    hconj, comm_d4x₁_d4x₂ σ hσ s b hb, comm_d4x₁_d4x₃ σ hσ, comm_d4x₁_d4x₄ σ hσ,
    (commute_d4x₁_d4x₅ σ s e).eq, mul_inv_cancel_right, (commute_d4x₁_d4x₆ σ s f).eq,
    mul_inv_cancel_right]
  simp only [d4x₂_eq_d4v σ, d4x₃_eq_d4v σ, d4x₄_eq_d4v σ, d4x₅_eq_d4v σ, d4x₆_eq_d4v σ,
    d4v_mul σ hσ]
  exact ⟨_, d4v_congr σ (by ring) (by ring) (by ring) (by ring) rfl⟩

omit [CharP K 2] in
include hσ in
theorem ho_conj_d4v
    (a : Kˣ) (b c d e f : K) :
    trialityOuterTorus K σ a * d4v K σ b c d e f * (trialityOuterTorus K σ a)⁻¹ =
      d4v K σ (((a : K) * σ a * σ (σ a))⁻¹ * b) ((a : K) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹ * c)
        (σ a ^ 2 * σ (σ a) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹ * d) (((a : K) * σ a * σ (σ a)) * e)
        f := by
  rw [← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, ho_conj_d4x₂,
    ho_conj_d4x₃ σ hσ, ho_conj_d4x₄ σ hσ, ho_conj_d4x₅, ho_conj_d4x₆]
  rfl

omit [CharP K 2] in
theorem hm_conj_d4v
    (μ : (trialityFixedField K σ.toRingHom)ˣ) (b c d e f : K) :
    trialityMiddleTorus K σ μ * d4v K σ b c d e f * (trialityMiddleTorus K σ μ)⁻¹ =
      d4v K σ (((trialityFixedUnit K σ μ : Kˣ) : K) ^ 2 * b)
        (((trialityFixedUnit K σ μ : Kˣ) : K) * c) d
        (((trialityFixedUnit K σ μ : Kˣ) : K)⁻¹ * e) (((trialityFixedUnit K σ μ : Kˣ) : K) *
            f) := by
  rw [← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, hm_conj_d4x₂,
    hm_conj_d4x₃, hm_conj_d4x₄, hm_conj_d4x₅, hm_conj_d4x₆]
  rfl

end Vr

section Coord

variable [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def d4factors
    (a b c d e f : K) : Fin 6 → ModGL TwistTag.D4.tag K :=
  ![d4x₁ K σ a, d4x₂ K b, d4x₃ K σ c, d4x₄ K σ d, d4x₅ K e, d4x₆ K f]

omit [CharP K 2] in
theorem d4factors_prod
    (a b c d e f : K) :
    (List.ofFn (d4factors σ a b c d e f)).prod = d4x₁ K σ a * d4v K σ b c d e f := by
  rw [list_ofFn_prod_fin_six]
  simp only [d4factors, d4v, mul_assoc]
  rfl

omit [CharP K 2] in
theorem d4factors_mem
    (a b c d e f : K) (j : Fin 6) :
    d4factors σ a b c d e f j ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  fin_cases j
  · exact trialityOrbitProd_mem_rootSpan σ.toRingHom a
  · exact pinnedX_mem_rootSpan (TwistTag.D4.self_mem_diagramOrbit (trialityRoot 1)) b
  · exact trialityOrbitProd_mem_rootSpan σ.toRingHom c
  · exact trialityOrbitProd_mem_rootSpan σ.toRingHom d
  · exact pinnedX_mem_rootSpan (TwistTag.D4.self_mem_diagramOrbit (trialityRoot 4)) e
  · exact pinnedX_mem_rootSpan (TwistTag.D4.self_mem_diagramOrbit (trialityRoot 5)) f

omit [CharP K 2] in
theorem d4coord_injective
    {a b c d e f a' b' c' d' e' f' : K}
    (h : d4x₁ K σ a * d4v K σ b c d e f = d4x₁ K σ a' * d4v K σ b' c' d' e' f') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
  rw [← d4factors_prod, ← d4factors_prod] at h
  have hu := eq_of_prod_rootSpan_eq (fun i j hij => trialityOrbit_disjoint i j hij)
    trialityOrbit_pos (fun j => trialityOrbit_not_isRoot j) (d4factors_mem σ a b c d e f)
    (d4factors_mem σ a' b' c' d' e' f') h
  have h0 := congrFun hu 0
  have h1 := congrFun hu 1
  have h2 := congrFun hu 2
  have h3 := congrFun hu 3
  have h4 := congrFun hu 4
  have h5 := congrFun hu 5
  simp only [d4factors] at h0 h1 h2 h3 h4 h5
  exact ⟨trialityOrbitProd_injective' (Or.inl rfl) (Subtype.ext h0), pinnedX_injective _ _ _ h1,
    trialityOrbitProd_injective' (Or.inr (Or.inl rfl)) (Subtype.ext h2),
    trialityOrbitProd_injective' (Or.inr (Or.inr rfl)) (Subtype.ext h3),
    pinnedX_injective _ _ _ h4, pinnedX_injective _ _ _ h5⟩

theorem exists_d4coord
    [Finite K] (hσ3 : σ.toRingHom ^ 3 = 1) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :
    ∃ a b c d e f : K, σ b = b ∧ σ e = e ∧ σ f = f ∧ g = d4x₁ K σ a * d4v K σ b c d e f := by
  obtain ⟨-, -, -, -, -, -, hB, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨⟨a, b, c, d, e, f⟩, -, hp⟩ := hB.2.2 hg
  refine ⟨a, b, c, d, e, f, b.2, e.2, f.2, ?_⟩
  rw [← hp]
  simp only [Subgroup.coe_mul, d4v, mul_assoc]
  rfl

theorem trialityOrbit_subset_simpleComplementRoots
    (j : Fin 6) (hj : j ≠ 0) :
    (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊆
      simpleComplementRoots TwistTag.D4 ⟨0, by decide⟩ := by
  intro β hβ
  refine ⟨trialityOrbit_pos j β hβ, ?_⟩
  rintro ⟨i, hi, rfl⟩
  have key : ∀ j : Fin 6, j ≠ 0 → ∀ i : Fin TwistTag.D4.tag.rank,
      i ∈ TwistTag.D4.orbit ⟨0, by decide⟩ →
      (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∉ trialityOrbit j := by
    decide +kernel
  exact key j hj i hi hβ

theorem d4v_mem_d4Vr
    (hσ3 : σ.toRingHom ^ 3 = 1) {b c d e f : K} (hb : σ b = b)
    (he : σ e = e) (hf : σ f = f) : d4v K σ b c d e f ∈ d4Vr K σ := by
  have hlong : ∀ j : Fin 6, (j = 1 ∨ j = 4 ∨ j = 5) → ∀ x : K, σ x = x →
      pinnedX TwistTag.D4.tag K (trialityRoot j) x ∈ d4Vr K σ := fun j hj x hx => by
    have h := pinnedX_trialityRoot_mem (σ := σ.toRingHom) hj
      (⟨x, (mem_trialityFixedField).2 hx⟩ : trialityFixedField K _)
    refine Subgroup.mem_inf.2 ⟨rootSpan_mono (trialityOrbit_subset_simpleComplementRoots j
      (by rcases hj with rfl | rfl | rfl <;> decide)) (Subgroup.mem_inf.1 h).1,
      (Subgroup.mem_inf.1 h).2⟩
  have hshort : ∀ j : Fin 6, (j = 2 ∨ j = 3) → ∀ x : K,
      (trialityOrbitProd K σ.toRingHom (trialityRoot j) x : ModGL TwistTag.D4.tag K) ∈
        d4Vr K σ := fun j hj x => by
    have h := trialityOrbitProd_mem (Or.inr hj) hσ3 x
    refine Subgroup.mem_inf.2 ⟨rootSpan_mono (trialityOrbit_subset_simpleComplementRoots j
      (by rcases hj with rfl | rfl <;> decide)) (Subgroup.mem_inf.1 h).1,
      (Subgroup.mem_inf.1 h).2⟩
  exact mul_mem (mul_mem (mul_mem (mul_mem (hlong 1 (Or.inl rfl) b hb)
    (hshort 2 (Or.inl rfl) c)) (hshort 3 (Or.inr rfl) d)) (hlong 4 (Or.inr (Or.inl rfl)) e he))
    (hlong 5 (Or.inr (Or.inr rfl)) f hf)

omit [CharP K 2] in
theorem coe_orbitX_zero_d4
    (c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      d4x₁ K σ (c : K) := by
  rw [coe_orbitX, d4x₁, coe_trialityOrbitProd]
  have hc : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
  have hm : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have e0 : trialityRoot 0 = Pi.single ⟨0, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  have e1 : permLattice TwistTag.D4.perm (trialityRoot 0) = Pi.single ⟨1, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  have e2 : permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 0) = Pi.single ⟨3, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  rw [hc, e1, e2, e0, pinnedX_single, pinnedX_single, pinnedX_single]
  simp only [List.range_succ, List.range_zero, List.nil_append, hm, mul_assoc]
  rfl

theorem exists_d4v
    [Finite K] (hσ3 : σ.toRingHom ^ 3 = 1) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ d4Vr K σ) :
    ∃ b c d e f : K, σ b = b ∧ σ e = e ∧ σ f = f ∧ g = d4v K σ b c d e f := by
  obtain ⟨hle, -, -, -, -, -, huniq, -⟩ :=
    fixed_simple_positive_complement TwistTag.D4 K σ ⟨0, by decide⟩
  obtain ⟨a, b, c, d, e, f, hb, he, hf, hg'⟩ := exists_d4coord σ hσ3 (hle hg)
  have ha : a ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ := by
    rw [mem_orbitField, show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide]
    exact congrArg (fun φ : K →+* K => φ a) hσ3
  have hv := d4v_mem_d4Vr σ hσ3 (c := c) (d := d) hb he hf
  obtain ⟨-, h⟩ := huniq g hg _ hv 0 ⟨a, ha⟩ (by
    rw [orbitX_zero, Subgroup.coe_one, one_mul, coe_orbitX_zero_d4, ← hg'])
  exact ⟨b, c, d, e, f, hb, he, hf, h⟩

end Coord

end CFSG.ComponentClassification.RankTwoExceptional.D4
