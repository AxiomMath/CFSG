module

public import CFSG.GroupActions.SubgroupStabilizerOuterBound

public section

namespace CFSG.GroupActions

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] noncomputable def stabAutPointFun [IsPretransitive G Ω] (x : Ω) (α : MulAut G)
    (y : Ω) : Ω :=
  α (Classical.choose (exists_smul_eq G x y)) • x

theorem stabAutPointFun_smul [IsPretransitive G Ω] (x : Ω) {α : MulAut G}
    (hα : α ∈ subgroupStabAut (stabilizer G x)) (g : G) :
    stabAutPointFun x α (g • x) = α g • x := by
  have hc := Classical.choose_spec (exists_smul_eq G x (g • x))
  set c := Classical.choose (exists_smul_eq G x (g • x))
  have hmem : g⁻¹ * c ∈ stabilizer G x := by
    rw [mem_stabilizer_iff, mul_smul, hc, inv_smul_smul]
  have hα' := apply_mem_of_mem_subgroupStabAut hα hmem
  rw [mem_stabilizer_iff, map_mul, map_inv, mul_smul, inv_smul_eq_iff] at hα'
  exact hα'

theorem stabAutPointFun_smul' [IsPretransitive G Ω] (x : Ω)
    (α : subgroupStabAut (stabilizer G x)) (g : G) :
    stabAutPointFun x (α : MulAut G) (g • x) = (α : MulAut G) g • x :=
  stabAutPointFun_smul x α.2 g

@[expose] noncomputable def stabAutPoint [IsPretransitive G Ω] (x : Ω) :
    subgroupStabAut (stabilizer G x) →* Equiv.Perm Ω where
  toFun α :=
    { toFun := stabAutPointFun x (α : MulAut G)
      invFun := stabAutPointFun x ((α⁻¹ : subgroupStabAut (stabilizer G x)) : MulAut G)
      left_inv := fun y => by
        obtain ⟨g, rfl⟩ := exists_smul_eq G x y
        rw [stabAutPointFun_smul' x α, stabAutPointFun_smul' x α⁻¹]
        change (α : MulAut G)⁻¹ ((α : MulAut G) g) • x = g • x
        rw [MulAut.inv_apply_self]
      right_inv := fun y => by
        obtain ⟨g, rfl⟩ := exists_smul_eq G x y
        rw [stabAutPointFun_smul' x α⁻¹, stabAutPointFun_smul' x α]
        change (α : MulAut G) ((α : MulAut G)⁻¹ g) • x = g • x
        rw [MulAut.apply_inv_self] }
  map_one' := by
    ext y
    obtain ⟨g, rfl⟩ := exists_smul_eq G x y
    change stabAutPointFun x ((1 : subgroupStabAut (stabilizer G x)) : MulAut G) (g • x) = g • x
    rw [stabAutPointFun_smul' x 1]
    rfl
  map_mul' α β := by
    ext y
    obtain ⟨g, rfl⟩ := exists_smul_eq G x y
    change stabAutPointFun x ((α * β : subgroupStabAut (stabilizer G x)) : MulAut G) (g • x) =
      stabAutPointFun x (α : MulAut G) (stabAutPointFun x (β : MulAut G) (g • x))
    rw [stabAutPointFun_smul' x (α * β), stabAutPointFun_smul' x β, stabAutPointFun_smul' x α]
    rfl

theorem stabAutPoint_smul [IsPretransitive G Ω] (x : Ω) (α : subgroupStabAut (stabilizer G x))
    (g : G) : stabAutPoint x α (g • x) = (α : MulAut G) g • x :=
  stabAutPointFun_smul' x α g

theorem faithful_transitive_action_automorphism_stabilizer [Finite G] [Finite Ω]
    [IsPretransitive G Ω] [FaithfulSMul G Ω] (x : Ω)
    (H' : Type*) [Group H'] [Finite H'] [MulAction H' Ω] :
    ((∀ (α : subgroupStabAut (stabilizer G x)) (g : G),
        stabAutPoint x α (g • x) = (α : MulAut G) g • x) ∧
      (∀ α : subgroupStabAut (stabilizer G x), stabAutPoint x α x = x) ∧
      Function.Injective (stabAutPoint (G := G) x) ∧
      (∀ (α : subgroupStabAut (stabilizer G x)) (g : G) (y : Ω),
        stabAutPoint x α (g • (stabAutPoint x α)⁻¹ y) = (α : MulAut G) g • y) ∧
      (∀ α : subgroupStabAut (stabilizer G x), (∀ h ∈ stabilizer G x, (α : MulAut G) h = h) →
        ∀ h ∈ stabilizer G x, ∀ y, stabAutPoint x α (h • y) = h • stabAutPoint x α y)) ∧
    ∀ τ : Equiv.Perm Ω, (∀ (h : H') y, τ (h • y) = h • τ y) →
      (∀ y, τ '' orbit H' y = orbit H' (τ y) ∧
        Nat.card (orbit H' (τ y)) = Nat.card (orbit H' y)) ∧
      (∀ y, τ '' orbit H' y = orbit H' y →
        τ y ∈ orbit H' y ∧ ∀ h ∈ stabilizer H' y, h • τ y = τ y) ∧
      (∀ τ' : Equiv.Perm Ω, (∀ (h : H') z, τ' (h • z) = h • τ' z) →
        ∀ y, τ y = τ' y → ∀ z ∈ orbit H' y, τ z = τ' z) := by
  have hconj : ∀ (α : subgroupStabAut (stabilizer G x)) (g : G) (y : Ω),
      stabAutPoint x α (g • (stabAutPoint x α)⁻¹ y) = (α : MulAut G) g • y := by
    intro α g y
    obtain ⟨k, rfl⟩ := exists_smul_eq G x y
    have hinv : (stabAutPoint x α)⁻¹ (k • x) = (α : MulAut G)⁻¹ k • x := by
      rw [← map_inv, stabAutPoint_smul]
      rfl
    rw [hinv, ← mul_smul, stabAutPoint_smul, map_mul, MulAut.apply_inv_self, mul_smul]
  refine ⟨⟨fun α g => stabAutPoint_smul x α g, fun α => ?_, ?_, hconj, ?_⟩, ?_⟩
  · have := stabAutPoint_smul x α 1
    rwa [one_smul, map_one, one_smul] at this
  ·
    rw [injective_iff_map_eq_one]
    intro α hα
    have hfix : ∀ g : G, (α : MulAut G) g • x = g • x := fun g => by
      rw [← stabAutPoint_smul, hα]
      rfl
    refine Subtype.ext (MulEquiv.ext fun g => ?_)
    refine eq_of_smul_eq_smul (α := Ω) fun y => ?_
    obtain ⟨k, rfl⟩ := exists_smul_eq G x y
    change (α : MulAut G) g • (k • x) = g • (k • x)
    calc (α : MulAut G) g • (k • x) = (α : MulAut G) g • ((α : MulAut G) k • x) := by
          rw [hfix k]
      _ = (α : MulAut G) (g * k) • x := by rw [map_mul, mul_smul]
      _ = (g * k) • x := hfix (g * k)
      _ = g • (k • x) := mul_smul g k x
  · intro α hα h hh y
    have h1 := hconj α h (stabAutPoint x α y)
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply, hα h hh] at h1
    exact h1
  · intro τ hτ
    have himg : ∀ y, τ '' orbit H' y = orbit H' (τ y) := by
      intro y
      ext z
      constructor
      · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
        exact ⟨h, (hτ h y).symm⟩
      · rintro ⟨h, rfl⟩
        exact ⟨h • y, ⟨h, rfl⟩, hτ h y⟩
    refine ⟨fun y => ⟨himg y, ?_⟩, fun y hO => ?_, fun τ' hτ' y hy z hz => ?_⟩
    · rw [← himg y]
      exact Nat.card_image_of_injective τ.injective _
    · refine ⟨?_, fun h hh => ?_⟩
      · rw [← hO]
        exact Set.mem_image_of_mem τ (mem_orbit_self y)
      · rw [← hτ h y, mem_stabilizer_iff.1 hh]
    · obtain ⟨h, rfl⟩ := hz
      change τ (h • y) = τ' (h • y)
      rw [hτ, hτ', hy]

end CFSG.GroupActions
