module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviNoInv

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup

variable {G : Type} [Group G] {A : Subgroup G} {P : Type} [Group P] {θ : ↥A →* P}

theorem exists_inner_levLift_of (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    {S : Subgroup P} (hperf : ⁅S, S⁆ = S) (σ : MulAut ↥A) {α : MulAut P}
    (hα : ∀ a, α (θ a) = θ (σ a)) {lb : P} (hlb : lb ∈ S)
    (hinner : ∀ x ∈ S, α x = lb * x * lb⁻¹) :
    ∃ l ∈ levLift θ S, ∀ z : ↥A, (z : G) ∈ levLift θ S → ((σ z : ↥A) : G) = l * z * l⁻¹ := by
  obtain ⟨l, hl, hlθ⟩ := exists_mem_levLift hθ hperf hlb
  refine ⟨l, hl, ?_⟩
  have hlA : l ∈ A := levLift_le hl
  have hperfL : Group.IsPerfect ↥(levLift θ S) :=
    (Subgroup.isPerfect_iff).mpr (commutator_levLift hker hθ hperf)
  let f : ↥(levLift θ S) →* ↥A := (MulAut.conj (⟨l, hlA⟩ : ↥A)).toMonoidHom.comp
    (Subgroup.inclusion (levLift_le (θ := θ) (S := S)))
  let g : ↥(levLift θ S) →* ↥A := σ.toMonoidHom.comp
    (Subgroup.inclusion (levLift_le (θ := θ) (S := S)))
  have hfg := eq_of_inv_mul_mem_center f g fun z => by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    change (θ (⟨l, hlA⟩ * ⟨z, levLift_le z.2⟩ * (⟨l, hlA⟩ : ↥A)⁻¹))⁻¹ *
      θ (σ ⟨z, levLift_le z.2⟩) = 1
    rw [← hα, hinner _ (theta_mem_of_mem_levLift z.2), map_mul, map_mul, map_inv, hlθ,
      inv_mul_cancel]
  intro z hz
  have := congrArg (fun F : ↥(levLift θ S) →* ↥A => ((F ⟨z, hz⟩ : ↥A) : G)) hfg
  exact this.symm

theorem exists_mem_levLift_orderOf [Finite G] {K : Type} [Field K] [Finite K] {f : ℕ}
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (hZ : Odd (Nat.card (center ↥A)))
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {S : Subgroup P} (hperf : ⁅S, S⁆ = S)
    (eS : Matrix.SpecialLinearGroup (Fin 2) K ≃* S) {s : P} (hs : s ∈ S) {r : ℕ} [Fact r.Prime]
    (hsr : s ^ r = 1) (hs1 : s ≠ 1) :
    ∃ x ∈ levLift θ S, ∃ hxA : x ∈ A, θ ⟨x, hxA⟩ = s ∧ orderOf x = r := by
  have : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨x, hx, hxθ⟩ := exists_mem_levLift hθ hperf hs
  refine ⟨x, hx, levLift_le hx, hxθ, ?_⟩
  obtain ⟨e⟩ := nonempty_levLift_equiv_SL2 hker hθ hZ hf hK hperf eS
  have hcen : center ↥(levLift θ S) = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [card_center_congr e, center_SL2_eq_bot', Subgroup.card_bot]
  set xL : ↥(levLift θ S) := ⟨x, hx⟩
  have hxr : xL ^ r = 1 := by
    have hc : xL ^ r ∈ center ↥(levLift θ S) := by
      refine mem_center_levLift_of hker ?_
      have h1 : levLiftHom θ S (xL ^ r) = 1 := by
        apply Subtype.ext
        rw [map_pow, Subgroup.coe_pow, levLiftHom_apply, Subgroup.coe_one]
        change (θ ⟨x, levLift_le hx⟩) ^ r = 1
        rw [hxθ, hsr]
      rw [h1]
      exact one_mem _
    rw [hcen, mem_bot] at hc
    exact hc
  have hxr' : x ^ r = 1 := by
    have := congrArg Subtype.val hxr
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  refine orderOf_eq_prime hxr' fun h1 => hs1 ?_
  rw [← hxθ, show (⟨x, levLift_le hx⟩ : ↥A) = 1 from Subtype.ext h1, map_one]

end CFSG.ComponentClassification.RankTwoClassical
