module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneSplitting

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

open scoped Pointwise

variable {Y : Type*} [Group Y]

def PlaneCaseTwo (U B C D : Subgroup Y) : Prop :=
  Nonempty (D ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
  (∀ d ∈ D, d ^ 2 = 1 ↔ d ∈ B) ∧
  ∃ u ∈ U, u ∉ B ∧ orderOf u = 2 ∧ D ⊔ Subgroup.zpowers u = C ∧ D ⊓ Subgroup.zpowers u = ⊥ ∧
    (∀ d ∈ D, u * d * u⁻¹ = d⁻¹) ∧
    ∀ x ∈ C, x ∉ D → orderOf x = 2 ∧
      Subgroup.centralizer {x} ⊓ C = B ⊔ Subgroup.zpowers x ∧ B ⊓ Subgroup.zpowers x = ⊥ ∧
      Nat.card (Subgroup.centralizer {x} ⊓ C : Subgroup Y) = 8 ∧
      {y | ∃ g ∈ C, g * x * g⁻¹ = y} = x • (B : Set Y)

theorem eight_linear_three_extension_plane_centralizer_dichotomy
    [Finite Y] {U : Subgroup Y} [U.Normal] [IsElementaryAbelian 2 U]
    (hU8 : Nat.card U = 8) (hcent : Subgroup.centralizer (U : Set Y) = U)
    (hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹)
    {B C N : Subgroup Y} (hBU : B ≤ U) (hB4 : Nat.card B = 4)
    (hC : C = Subgroup.centralizer (B : Set Y)) (hN : N = Subgroup.normalizer (B : Set Y)) :
    Nat.card Y = 1344 ∧ Nat.card C = 32 ∧ Nat.card N = 192 ∧ C ≤ N ∧
    (∃ _ : (C.subgroupOf N).Normal,
      Nonempty (N ⧸ C.subgroupOf N ≃* GL (Fin 2) (ZMod 2)) ∧
      Nonempty (N ⧸ C.subgroupOf N ≃* Equiv.Perm (Fin 3))) ∧
    (Subgroup.center C).map C.subtype = B ∧ ⁅C, C⁆ = B ∧ B ≤ C ∧
    (∃ _ : (B.subgroupOf C).Normal,
      IsElementaryAbelian 2 (C ⧸ B.subgroupOf C) ∧ Nat.card (C ⧸ B.subgroupOf C) = 8) ∧
    ∃ D : Subgroup Y, D ≤ C ∧ IsMulCommutative D ∧ Nat.card D = 16 ∧
      (∀ A : Subgroup Y, A ≤ C → IsMulCommutative A → Nat.card A = 16 → A = D) ∧
      (D.subgroupOf C).Characteristic ∧ D ≤ N ∧ (D.subgroupOf N).Normal ∧
      D ⊓ U = B ∧ D ⊔ U = C ∧
      Xor (IsElementaryAbelian 2 D ∧ ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤)
        (PlaneCaseTwo U B C D) ∧
      ((¬ ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤) → PlaneCaseTwo U B C D) := by
  classical
  subst hC hN
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB4]; omega)
  obtain ⟨β₁, hβ₁⟩ := exists_not_mem_finset_of_card_lt ({1} : Finset B) (by
    rw [hB4, Finset.card_singleton]; omega)
  obtain ⟨β₂, hβ₂⟩ := exists_not_mem_finset_of_card_lt ({1, β₁} : Finset B) (by
    rw [hB4]; exact (Finset.card_le_two).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hβ₁ hβ₂
  have hu₀ : ∃ u₀ ∈ U, u₀ ∉ B := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ B := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    rw [hU8, hB4] at this
    omega
  obtain ⟨u₀, hu₀U, hu₀B⟩ := hu₀
  have h : PlaneHyp U B β₁ β₂ u₀ :=
    { card_U := hU8
      centralizer_U := hcent
      full := hfull
      le := hBU
      card_B := hB4
      b₁_mem := β₁.2
      b₂_mem := β₂.2
      b₁_ne_one := fun e => hβ₁ (Subtype.ext e)
      b₂_ne_one := fun e => hβ₂.1 (Subtype.ext e)
      b₂_ne_b₁ := fun e => hβ₂.2 (Subtype.ext e)
      u₀_mem := hu₀U
      u₀_not_mem := hu₀B }
  obtain ⟨c₁, hc₁, c₂, hc₂, hτ₁, hτ₂, hcc⟩ := h.exists_commuting_lifts
  have hl : PlaneLifts B β₁ β₂ u₀ c₁ c₂ := ⟨hc₁, hc₂, hτ₁, hτ₂, hcc⟩
  have hNormal : ((Subgroup.centralizer (B : Set Y)).subgroupOf
      (Subgroup.normalizer (B : Set Y))).Normal := by
    rw [← PlaneHyp.restriction_ker]
    exact MonoidHom.normal_ker _
  have _ := h.isElementaryAbelian_B
  have _ := h.isKleinFour_B
  obtain ⟨eGL⟩ := nonempty_mulAut_mulEquiv_GL (A := B) (n := 2) (by rw [hB4]; norm_num)
  refine ⟨h.card_Y, h.card_C, h.card_N, PlaneHyp.centralizer_le_normalizer,
    ⟨hNormal, ⟨h.normalizerQuotientEquiv.trans eGL⟩,
      ⟨h.normalizerQuotientEquiv.trans
        (CFSG.GorensteinWalter.kleinFourAutSymmetricThreeEquiv B)⟩⟩,
    h.center_centralizer_eq, h.commutator_centralizer_eq, PlaneHyp.le_centralizer_of_le hBU,
    h.quotient_B_spec, planeD B c₁ c₂, planeD_le_centralizer B c₁ c₂,
    h.isMulCommutative_planeD hl, h.card_planeD hl,
    fun A hAC hA hA16 => h.eq_planeD_of_abelian hl hAC hA hA16,
    h.characteristic_planeD hl, PlaneHyp.planeD_le_normalizer,
    h.normal_planeD_subgroupOf_normalizer hl, h.planeD_inf_U hl, h.planeD_sup_U hl, ?_⟩
  have hcaseTwo : (∀ d ∈ planeD B c₁ c₂, d * d = planeTau u₀ d) →
      PlaneCaseTwo U B (Subgroup.centralizer (B : Set Y)) (planeD B c₁ c₂) := by
    intro hsq
    refine ⟨h.nonempty_planeD_mulEquiv hl hsq, fun d hd => ?_, u₀, hu₀U, hu₀B, h.orderOf_u₀,
      h.planeD_sup_zpowers hl, h.planeD_inf_zpowers hl, fun d hd => h.u₀_inverts hsq hd,
      fun x hxC hxD => ⟨h.outside_orderOf hl hsq hxC hxD, h.outside_centralizer hl hxC hxD,
        h.outside_inf hl hsq hxC hxD, h.outside_card hl hsq hxC hxD,
        h.outside_class hl hxC hxD⟩⟩
    rw [pow_two]
    exact h.mul_self_eq_one_iff_of_sq hl hsq hd
  rcases h.sq_dichotomy hl with hel | hsq
  · have hEA : IsElementaryAbelian 2 (planeD B c₁ c₂) :=
      { toIsMulCommutative := h.isMulCommutative_planeD hl
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun d => Subtype.ext (by
          rw [Subgroup.coe_pow, pow_two, OneMemClass.coe_one]
          exact hel d d.2) }
    have hsplit := h.exists_complement_of_elementary hl hel
    have hnot : ¬ PlaneCaseTwo U B (Subgroup.centralizer (B : Set Y)) (planeD B c₁ c₂) := by
      rintro ⟨-, hsqB, -⟩
      have hle : planeD B c₁ c₂ ≤ B := fun d hd => (hsqB d hd).mp (by rw [pow_two]; exact hel d hd)
      have := Subgroup.card_le_of_le hle
      rw [h.card_planeD hl, hB4] at this
      omega
    exact ⟨Or.inl ⟨⟨hEA, hsplit⟩, hnot⟩, fun hns => absurd hsplit hns⟩
  · have hnot : ¬ (IsElementaryAbelian 2 (planeD B c₁ c₂) ∧
        ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤) := by
      rintro ⟨hEA, -⟩
      have h1 : c₁ * c₁ = 1 := by
        have := congrArg Subtype.val (sq_eq_one_of_isElementaryAbelian
          (⟨c₁, PlaneHyp.c₁_mem_planeD hl⟩ : planeD B c₁ c₂))
        simpa [pow_two] using this
      rw [hsq c₁ (PlaneHyp.c₁_mem_planeD hl), hτ₁] at h1
      exact h.b₁_ne_one h1
    exact ⟨Or.inr ⟨hcaseTwo hsq, hnot⟩, fun _ => hcaseTwo hsq⟩

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
