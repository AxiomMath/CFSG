module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open scoped commutatorElement

section Abstract

variable {G X P : Type*} [Group G] [Group X] [Group P]

theorem hom_eq_of_central_ker_perfect [Group.IsPerfect G] {θ : X →* P}
    (hker : θ.ker ≤ Subgroup.center X) (a b : G →* X) (hab : ∀ x, θ (a x) = θ (b x)) :
    a = b := by
  have hmem : ∀ x, (b x)⁻¹ * a x ∈ Subgroup.center X := fun x => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab x, inv_mul_cancel]
  let z : G →* Subgroup.center X :=
    { toFun := fun x => ⟨(b x)⁻¹ * a x, hmem x⟩
      map_one' := by simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hmem x)
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        calc (b y)⁻¹ * (b x)⁻¹ * (a x * a y)
            = (b y)⁻¹ * ((b x)⁻¹ * a x) * a y := by group
          _ = ((b x)⁻¹ * a x) * (b y)⁻¹ * a y := by rw [hc ((b y)⁻¹)]
          _ = ((b x)⁻¹ * a x) * ((b y)⁻¹ * a y) := by group }
  have hz : ∀ x, z x = 1 := fun x => by
    have h1 : x ∈ z.ker := Abelianization.commutator_subset_ker z
      (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top x)
    exact MonoidHom.mem_ker.mp h1
  refine MonoidHom.ext fun x => ?_
  have := congrArg (fun w : Subgroup.center X => (w : X)) (hz x)
  simp only [z, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at this
  exact (inv_mul_eq_one.mp this).symm

theorem mem_center_of_commutator_mem_center [Group.IsPerfect G] {g : G}
    (h : ∀ y, ⁅g, y⁆ ∈ Subgroup.center G) : g ∈ Subgroup.center G := by
  have h2 : g ∈ Subgroup.upperCentralSeries G 2 := by
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    exact h y
  rwa [Group.IsPerfect.upperCentralSeries_eq_center G (by norm_num)] at h2

theorem center_le_map_center_of_perfect [Group.IsPerfect G] {θ : G →* X}
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center G) :
    Subgroup.center X ≤ (Subgroup.center G).map θ := by
  intro c hc
  obtain ⟨g, rfl⟩ := hθ c
  refine ⟨g, mem_center_of_commutator_mem_center fun y => hker ?_, rfl⟩
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact (commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hc (θ y)).symm))

theorem map_center_eq_center_of_perfect [Group.IsPerfect G] {θ : G →* X}
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center G) :
    (Subgroup.center G).map θ = Subgroup.center X :=
  le_antisymm (Subgroup.map_center_le_center hθ) (center_le_map_center_of_perfect hθ hker)

theorem exists_mulEquiv_of_central_cover [Group.IsPerfect G] {π : G →* P}
    (hπ : Function.Surjective π) (hπker : π.ker = Subgroup.center G) {θ : G →* X}
    (hθ : Function.Surjective θ) (hθker : θ.ker ≤ Subgroup.center G) (σ : X ≃* X) :
    ∃ β : P ≃* P, (∀ α : G →* G, (∀ x, π (α x) = β (π x)) → ∀ x, θ (α x) = σ (θ x)) ∧
      ((∀ x, σ (σ x) = x) → ∀ y, β (β y) = y) := by
  obtain ⟨θ', hθ'⟩ : ∃ θ' : X →* P, ∀ g, θ' (θ g) = π g :=
    ⟨(θ.liftOfSurjective hθ) ⟨π, hπker ▸ hθker⟩, fun g =>
      MonoidHom.liftOfRightInverse_comp_apply θ _ (Function.rightInverse_surjInv hθ) _ g⟩
  have hθ'surj : Function.Surjective θ' := by
    intro y
    obtain ⟨g, rfl⟩ := hπ y
    exact ⟨θ g, hθ' g⟩
  have hker' : θ'.ker = Subgroup.center X := by
    rw [← map_center_eq_center_of_perfect hθ hθker]
    ext c
    obtain ⟨g, rfl⟩ := hθ c
    rw [MonoidHom.mem_ker, hθ', ← MonoidHom.mem_ker, hπker]
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨z, hz, hzg⟩
      have : z⁻¹ * g ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzg, inv_mul_cancel]
      have h1 : z⁻¹ * g ∈ Subgroup.center G := hθker this
      have h2 := Subgroup.mul_mem _ hz h1
      rwa [mul_inv_cancel_left] at h2
  have hσker : ∀ c, θ' c = 1 → θ' (σ c) = 1 := fun c hc => by
    have hc' : c ∈ Subgroup.center X := hker' ▸ hc
    have : σ c ∈ Subgroup.center X := by
      rw [← Subgroup.map_center_eq σ]
      exact ⟨c, hc', rfl⟩
    rw [← MonoidHom.mem_ker, hker']
    exact this
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : P →* P, ∀ c, β₀ (θ' c) = θ' (σ c) :=
    ⟨(θ'.liftOfSurjective hθ'surj) ⟨θ'.comp σ.toMonoidHom, fun c hc => hσker c hc⟩, fun c =>
      MonoidHom.liftOfRightInverse_comp_apply θ' _ (Function.rightInverse_surjInv hθ'surj) _ c⟩
  have hσker' : ∀ c, θ' c = 1 → θ' (σ.symm c) = 1 := fun c hc => by
    have hc' : c ∈ Subgroup.center X := hker' ▸ hc
    have : σ.symm c ∈ Subgroup.center X := by
      rw [← Subgroup.map_center_eq σ.symm]
      exact ⟨c, hc', rfl⟩
    rw [← MonoidHom.mem_ker, hker']
    exact this
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : P →* P, ∀ c, β₁ (θ' c) = θ' (σ.symm c) :=
    ⟨(θ'.liftOfSurjective hθ'surj) ⟨θ'.comp σ.symm.toMonoidHom, fun c hc => hσker' c hc⟩, fun c =>
      MonoidHom.liftOfRightInverse_comp_apply θ' _ (Function.rightInverse_surjInv hθ'surj) _ c⟩
  have h01 : ∀ y, β₀ (β₁ y) = y := fun y => by
    obtain ⟨c, rfl⟩ := hθ'surj y
    rw [hβ₁, hβ₀, MulEquiv.apply_symm_apply]
  have h10 : ∀ y, β₁ (β₀ y) = y := fun y => by
    obtain ⟨c, rfl⟩ := hθ'surj y
    rw [hβ₀, hβ₁, MulEquiv.symm_apply_apply]
  obtain ⟨β, hβ⟩ : ∃ β : P ≃* P, ∀ c, β (θ' c) = θ' (σ c) :=
    ⟨{ toFun := β₀
       invFun := β₁
       left_inv := h10
       right_inv := h01
       map_mul' := β₀.map_mul }, hβ₀⟩
  refine ⟨β, fun α hα x => ?_, fun hσ y => ?_⟩
  · have key := DFunLike.congr_fun
      (hom_eq_of_central_ker_perfect (θ := θ') hker'.le
        (θ.comp α) (σ.toMonoidHom.comp θ) (fun y => by
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
          rw [hθ', hα, ← hθ', hβ]))
      x
    simpa using key
  · obtain ⟨c, rfl⟩ := hθ'surj y
    rw [hβ, hβ, hσ]

theorem lift_comp_eq_of_fixed {L : Type*} [Group L] [Group.IsPerfect L] {θ : G →* X}
    (hθker : θ.ker ≤ Subgroup.center G) {σ : X ≃* X} {α : G →* G}
    (hα : ∀ x, θ (α x) = σ (θ x)) (B : L →* G) (hB : ∀ x, σ (θ (B x)) = θ (B x)) :
    α.comp B = B :=
  hom_eq_of_central_ker_perfect hθker _ _ fun x => by
    rw [MonoidHom.comp_apply, hα, hB]

theorem lift_comp_self_eq_id [Group.IsPerfect G] {θ : G →* X}
    (hθker : θ.ker ≤ Subgroup.center G) {σ : X ≃* X} (hσ : ∀ x, σ (σ x) = x) {α : G →* G}
    (hα : ∀ x, θ (α x) = σ (θ x)) : α.comp α = MonoidHom.id G :=
  hom_eq_of_central_ker_perfect hθker _ _ fun x => by
    rw [MonoidHom.comp_apply, hα, hα, hσ, MonoidHom.id_apply]

end Abstract

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
