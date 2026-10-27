module

public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open scoped Pointwise

section FixedPoints

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem smul_mem_fixedSet_of_mem_centralizer {z g : G} (hg : g ∈ Subgroup.centralizer {z})
    {x : Ω} (hx : z • x = x) : z • g • x = g • x := by
  have hc : z * g = g * z := Subgroup.mem_centralizer_iff.1 hg z rfl
  rw [smul_smul, hc, mul_smul, hx]

theorem smul_fixedSet_of_mem_centralizer {z g : G} (hg : g ∈ Subgroup.centralizer {z}) :
    g • {x : Ω | z • x = x} = {x : Ω | z • x = x} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_fixedSet_of_mem_centralizer hg hy
  · intro hx
    exact ⟨g⁻¹ • x, smul_mem_fixedSet_of_mem_centralizer (inv_mem hg) hx, smul_inv_smul g x⟩

theorem fixed_point_set_orbit_centralizer_bound [Finite G] [Finite Ω] (z : G) (H : Subgroup G)
    (hH : H ≤ Subgroup.centralizer {z})
    (horb : H.index ≤ (Set.range fun g : G => g • {x : Ω | z • x = x}).ncard) :
    H = Subgroup.centralizer {z} ∧
      ∀ g : G, g ∈ Subgroup.centralizer {z} ↔ g • {x : Ω | z • x = x} = {x : Ω | z • x = x} := by
  set Δ : Set Ω := {x | z • x = x} with hΔ
  have hCS : Subgroup.centralizer {z} ≤ MulAction.stabilizer G Δ := fun g hg =>
    MulAction.mem_stabilizer_iff.2 (smul_fixedSet_of_mem_centralizer hg)
  have hHS : H ≤ MulAction.stabilizer G Δ := hH.trans hCS
  have hidx : H.index ≤ (MulAction.stabilizer G Δ).index := by
    rw [MulAction.index_stabilizer]
    exact horb
  have hSH : MulAction.stabilizer G Δ ≤ H := by
    have h1 := Subgroup.relIndex_mul_index hHS
    have hS0 : (MulAction.stabilizer G Δ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hH0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hR1 : H.relIndex (MulAction.stabilizer G Δ) = 1 := by
      rcases Nat.lt_or_ge (H.relIndex (MulAction.stabilizer G Δ)) 2 with h | h
      · rcases Nat.lt_or_ge (H.relIndex (MulAction.stabilizer G Δ)) 1 with h' | h'
        · have h0 : H.relIndex (MulAction.stabilizer G Δ) = 0 := by omega
          rw [h0, zero_mul] at h1
          exact absurd h1.symm hH0
        · omega
      · have : 2 * (MulAction.stabilizer G Δ).index ≤ H.index := by
          rw [← h1]
          exact Nat.mul_le_mul_right _ h
        omega
    exact Subgroup.relIndex_eq_one.1 hR1
  refine ⟨le_antisymm hH (hCS.trans hSH), fun g => ⟨fun hg => hCS hg, fun hg => hH (hSH hg)⟩⟩

end FixedPoints

section Sylow

variable {Ω : Type*} {G : Subgroup (Equiv.Perm Ω)} {p : ℕ}

theorem mulAut_smul_smul_sylow (α : MulAut G) (g : G) (P : Sylow p G) :
    α • (g • P) = (α g) • (α • P) := by
  refine Sylow.ext (Subgroup.ext fun x => ?_)
  rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
    Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists,
    Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    refine ⟨α w, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨w, hw, rfl⟩, ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, map_mul, map_inv]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    refine ⟨g * w * g⁻¹, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨w, hw, rfl⟩, ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, map_mul, map_inv]

variable (β : Ω ≃ Sylow p G)

@[expose] def sylowRealization (α : MulAut G) : Equiv.Perm Ω :=
  (β.trans (MulAction.toPerm α)).trans β.symm

theorem apply_sylowRealization (α : MulAut G) (ω : Ω) :
    β (sylowRealization β α ω) = α • β ω := by
  simp [sylowRealization]

variable {β}

theorem sylowRealization_mul_mul_inv
    (hβ : ∀ (g : G) (ω : Ω), β ((g : Equiv.Perm Ω) ω) = g • β ω) (α : MulAut G) (g : G) :
    sylowRealization β α * (g : Equiv.Perm Ω) * (sylowRealization β α)⁻¹ =
      ((α g : G) : Equiv.Perm Ω) := by
  refine Equiv.ext fun ω => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  set y := (sylowRealization β α)⁻¹ ω with hy
  have hπy : sylowRealization β α y = ω := by
    rw [hy, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  apply β.injective
  rw [hβ (α g) ω, apply_sylowRealization, hβ g y, mulAut_smul_smul_sylow,
    ← apply_sylowRealization, hπy]

theorem sylowRealization_mem_normalizer
    (hβ : ∀ (g : G) (ω : Ω), β ((g : Equiv.Perm Ω) ω) = g • β ω) (α : MulAut G) :
    sylowRealization β α ∈ Subgroup.normalizer (G : Set (Equiv.Perm Ω)) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · have := sylowRealization_mul_mul_inv hβ α ⟨h, hh⟩
    change sylowRealization β α * ((⟨h, hh⟩ : G) : Equiv.Perm Ω) *
      (sylowRealization β α)⁻¹ ∈ G
    rw [this]
    exact (α ⟨h, hh⟩).2
  · set k : G := ⟨_, hh⟩
    have h1 := sylowRealization_mul_mul_inv hβ α (α⁻¹ k)
    rw [show α (α⁻¹ k) = k from α.apply_symm_apply k] at h1
    have h2 : h = ((α⁻¹ k : G) : Equiv.Perm Ω) :=
      mul_left_cancel (mul_right_cancel (h1.trans rfl).symm)
    rw [h2]
    exact (α⁻¹ k).2

theorem sylow_action_automorphism_realization [Finite G] [Fact p.Prime] (β : Ω ≃ Sylow p G)
    (hβ : ∀ (g : G) (ω : Ω), β ((g : Equiv.Perm Ω) ω) = g • β ω) :
    (∀ (α : MulAut G) (g : G), sylowRealization β α * (g : Equiv.Perm Ω) *
        (sylowRealization β α)⁻¹ = ((α g : G) : Equiv.Perm Ω)) ∧
      (∀ α : MulAut G, sylowRealization β α ∈ Subgroup.normalizer (G : Set (Equiv.Perm Ω))) ∧
      ∀ α : MulAut G, ∃ n ∈ Subgroup.normalizer (G : Set (Equiv.Perm Ω)),
        ∀ g : G, n * (g : Equiv.Perm Ω) * n⁻¹ = ((α g : G) : Equiv.Perm Ω) :=
  ⟨sylowRealization_mul_mul_inv hβ, sylowRealization_mem_normalizer hβ,
    fun α => ⟨_, sylowRealization_mem_normalizer hβ α, sylowRealization_mul_mul_inv hβ α⟩⟩

end Sylow

section Involutions

variable {G : Type*} [Group G]

theorem card_centralizer_singleton_map (φ : MulAut G) (y : G) :
    Nat.card (Subgroup.centralizer {φ y}) = Nat.card (Subgroup.centralizer {y}) := by
  rw [← map_centralizer_singleton, Subgroup.card_map_of_injective φ.injective]

theorem involution_class_centralizer_recovery [Finite G] {z : G} (hz : orderOf z = 2) {r : ℕ}
    (x : Fin r → G) (_hx : ∀ i, orderOf (x i) = 2)
    (hcl : ∀ y : G, orderOf y = 2 → IsConj z y ∨ ∃ i, IsConj (x i) y)
    (hcard : ∀ i, Nat.card (Subgroup.centralizer {x i}) < Nat.card (Subgroup.centralizer {z}))
    (α : MulAut G) :
    IsConj z (α z) ∧ ∃ g : G, (Subgroup.centralizer {z}).map α.toMonoidHom =
      (Subgroup.centralizer {z}).map (MulAut.conj g).toMonoidHom := by
  have hαz : orderOf (α z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  rcases hcl (α z) hαz with hconj | ⟨i, hi⟩
  · obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    refine ⟨hconj, g, ?_⟩
    rw [map_centralizer_singleton, map_centralizer_singleton, MulAut.conj_apply, hg]
  · exfalso
    obtain ⟨g, hg⟩ := isConj_iff.1 hi
    have h1 := card_centralizer_singleton_map (MulAut.conj g) (x i)
    rw [MulAut.conj_apply, hg, card_centralizer_singleton_map] at h1
    have := hcard i
    omega

end Involutions

end CFSG.LocalAnalysis.ComponentInitial
