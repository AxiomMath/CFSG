module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_surj_of_card {R K : Type*} [Group R] [Group K] [Finite R] [Finite K] (φ : R →* K)
    {c : ℕ} (hker : Nat.card φ.ker ≤ c) (hR : Nat.card K * c ≤ Nat.card R) :
    Function.Surjective φ := by
  have h := Subgroup.card_ker_mul_card_range φ
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hrange : Nat.card K ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card φ.ker * Nat.card φ.range < Nat.card φ.ker * Nat.card K :=
      Nat.mul_lt_mul_of_pos_left hlt hpos
    have h2 : Nat.card φ.ker * Nat.card K ≤ c * Nat.card K :=
      Nat.mul_le_mul_right _ hker
    rw [h] at h1
    rw [mul_comm c] at h2
    omega
  have hle : Nat.card φ.range ≤ Nat.card K :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (le_antisymm hle hrange)
  exact MonoidHom.range_eq_top.mp htop

theorem w4q_exists_psi
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    ∃ φ : ↥(ctxO t tau x₁ x₂) →* ↥(fourGrp x₁ x₂) × ↥(fourGrp x₁ x₂),
      (∀ g, ((φ g).1 : G) = (g : G) * t * (g : G)⁻¹ * t⁻¹) ∧
      (∀ g, ((φ g).2 : G) = (g : G) * tau * (g : G)⁻¹ * tau⁻¹) ∧
      ∀ g, φ g = 1 → (g : G) ∈ ctxX t tau x₁ x₂ := by
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := (hc.wreath.fourGrp_eq_omega).2.1.1
  have hV1 : ∀ g : ↥(ctxO t tau x₁ x₂), (g : G) * t * (g : G)⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ :=
    fun g => w4q_O_comm_X hc g.2 htX
  have hV2 : ∀ g : ↥(ctxO t tau x₁ x₂), (g : G) * tau * (g : G)⁻¹ * tau⁻¹ ∈ fourGrp x₁ x₂ :=
    fun g => w4q_O_comm_X hc g.2 htauX
  let f : ↥(ctxO t tau x₁ x₂) → ↥(fourGrp x₁ x₂) × ↥(fourGrp x₁ x₂) := fun g =>
    (⟨(g : G) * t * (g : G)⁻¹ * t⁻¹, hV1 g⟩, ⟨(g : G) * tau * (g : G)⁻¹ * tau⁻¹, hV2 g⟩)
  have hmul : ∀ g h : ↥(ctxO t tau x₁ x₂), f (g * h) = f g * f h := by
    intro g h
    apply Prod.ext
    · apply Subtype.ext
      have hfix : (g : G) * ((h : G) * t * (h : G)⁻¹ * t⁻¹) * (g : G)⁻¹ =
          (h : G) * t * (h : G)⁻¹ * t⁻¹ := w4q_V_central hc g.2 (hV1 h)
      show (g : G) * (h : G) * t * ((g : G) * (h : G))⁻¹ * t⁻¹ =
          ((g : G) * t * (g : G)⁻¹ * t⁻¹) * ((h : G) * t * (h : G)⁻¹ * t⁻¹)
      rw [show (g : G) * (h : G) * t * ((g : G) * (h : G))⁻¹ * t⁻¹ =
          ((g : G) * ((h : G) * t * (h : G)⁻¹ * t⁻¹) * (g : G)⁻¹) *
            ((g : G) * t * (g : G)⁻¹ * t⁻¹) by group, hfix]
      exact congrArg Subtype.val (mul_comm' (⟨_, hV1 h⟩ : ↥(fourGrp x₁ x₂)) ⟨_, hV1 g⟩)
    · apply Subtype.ext
      have hfix : (g : G) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹) * (g : G)⁻¹ =
          (h : G) * tau * (h : G)⁻¹ * tau⁻¹ := w4q_V_central hc g.2 (hV2 h)
      show (g : G) * (h : G) * tau * ((g : G) * (h : G))⁻¹ * tau⁻¹ =
          ((g : G) * tau * (g : G)⁻¹ * tau⁻¹) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹)
      rw [show (g : G) * (h : G) * tau * ((g : G) * (h : G))⁻¹ * tau⁻¹ =
          ((g : G) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹) * (g : G)⁻¹) *
            ((g : G) * tau * (g : G)⁻¹ * tau⁻¹) by group, hfix]
      exact congrArg Subtype.val (mul_comm' (⟨_, hV2 h⟩ : ↥(fourGrp x₁ x₂)) ⟨_, hV2 g⟩)
  refine ⟨MonoidHom.mk' f hmul, fun g => rfl, fun g => rfl, fun g hg1 => ?_⟩
  have hct1 : (⟨(g : G) * t * (g : G)⁻¹ * t⁻¹, hV1 g⟩ : ↥(fourGrp x₁ x₂)) = 1 := by
    exact congrArg Prod.fst hg1
  have hctau1 : (⟨(g : G) * tau * (g : G)⁻¹ * tau⁻¹, hV2 g⟩ : ↥(fourGrp x₁ x₂)) = 1 := by
    exact congrArg Prod.snd hg1
  have hgt : (g : G) * t * (g : G)⁻¹ * t⁻¹ = 1 := by simpa using congrArg Subtype.val hct1
  have hgtau : (g : G) * tau * (g : G)⁻¹ * tau⁻¹ = 1 := by
    simpa using congrArg Subtype.val hctau1
  exact w4_mem_X_of_mem_R hc.toCtx10.toCtx4
    (w4_O_le_R (w4q_toW4Ctxc hc).toW4Ctxb g.2) hgt hgtau

theorem w4q_comm_of_comm_eq_one {a b : G} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  have h1 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem w4q_psi_surj
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {v v' : G}
    (hv : v ∈ fourGrp x₁ x₂) (hv' : v' ∈ fourGrp x₁ x₂) :
    ∃ g ∈ ctxO t tau x₁ x₂, g * t * g⁻¹ * t⁻¹ = v ∧ g * tau * g⁻¹ * tau⁻¹ = v' := by
  obtain ⟨φ, h1, h2, hker⟩ := w4q_exists_psi hc
  have hX : Nat.card (ctxX t tau x₁ x₂) = 16 := (w4q_X_facts hc).2
  have hV : Nat.card (fourGrp x₁ x₂) = 4 := hc.wreath.fourGrp_eq_omega.2.2
  have hsurj : Function.Surjective φ := by
    refine w4q_surj_of_card φ (c := 16) ?_ ?_
    · have hle : φ.ker.map (ctxO t tau x₁ x₂).subtype ≤ ctxX t tau x₁ x₂ := by
        rintro _ ⟨k, hk, rfl⟩
        exact hker k hk
      have h := Subgroup.card_le_of_le hle
      rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hX] at h
    · rw [Nat.card_prod, hV, hc.card_O]
      norm_num
  obtain ⟨g, hg⟩ := hsurj (⟨v, hv⟩, ⟨v', hv'⟩)
  exact ⟨g, g.2, by rw [← h1 g, hg], by rw [← h2 g, hg]⟩

theorem w4q_exists_L
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {v : G}
    (hv : v ∈ fourGrp x₁ x₂) :
    ∃ l ∈ ctxO t tau x₁ x₂, l * tau = tau * l ∧ l * t * l⁻¹ * t⁻¹ = v := by
  obtain ⟨g, hg, h1, h2⟩ := w4q_psi_surj hc hv (one_mem _)
  exact ⟨g, hg, w4q_comm_of_comm_eq_one h2, h1⟩

theorem w4q_decomp
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxO t tau x₁ x₂) :
    ∃ l ∈ ctxO t tau x₁ x₂, ∃ d ∈ ctxO t tau x₁ x₂,
      l * tau = tau * l ∧ d * t = t * d ∧ g = l * d := by
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  obtain ⟨l, hlO, hlτ, hlt⟩ := w4q_exists_L hc (w4q_O_comm_X hc hg htX)
  have hconj : l * t * l⁻¹ = g * t * g⁻¹ := mul_right_cancel hlt
  refine ⟨l, hlO, l⁻¹ * g, mul_mem (inv_mem hlO) hg, hlτ, ?_, by group⟩
  calc l⁻¹ * g * t = l⁻¹ * (g * t * g⁻¹) * g := by group
    _ = l⁻¹ * (l * t * l⁻¹) * g := by rw [hconj]
    _ = t * (l⁻¹ * g) := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
