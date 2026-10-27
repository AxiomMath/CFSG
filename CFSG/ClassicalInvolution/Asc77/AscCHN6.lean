module

public import CFSG.ClassicalInvolution.Asc77.AscCHN4

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

open Matrix CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F] {G : Type} [Group G]

@[expose] def node (ψ : SL(4, F) →* G) : Subgroup G := (blk F 1).range.map ψ

theorem mem_node_iff (ψ : SL(4, F) →* G) (k : G) :
    k ∈ node ψ ↔ ∃ s : SL(2, F), ψ (blk F 1 s) = k := by
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, ⟨s, rfl⟩, rfl⟩

theorem t_conj_node (ψ : SL(4, F) →* G) (s : SL(2, F)) :
    ψ (blk F 2 (-1)) * ψ (blk F 1 s) * (ψ (blk F 2 (-1)))⁻¹ =
      ψ (blk F 1 (diagConj2 1 (-1) s)) := by
  rw [← map_inv, ← map_mul, ← map_mul, blk2_neg_one_conj_blk1]

theorem e_conj_blk1 (ψ : SL(4, F) →* G) {u : G} (hu : ∀ x ∈ ψ.range, u * x = x * u)
    (s : SL(2, F)) :
    (u * ψ (blk F 2 (-1))) * ψ (blk F 1 s) * (u * ψ (blk F 2 (-1)))⁻¹ =
      ψ (blk F 1 (diagConj2 1 (-1) s)) := by
  have hc := hu _ ⟨blk F 2 (-1) * blk F 1 s * (blk F 2 (-1))⁻¹, rfl⟩
  rw [← t_conj_node ψ s, _root_.mul_inv_rev]
  calc u * ψ (blk F 2 (-1)) * ψ (blk F 1 s) * ((ψ (blk F 2 (-1)))⁻¹ * u⁻¹)
      = u * (ψ (blk F 2 (-1)) * ψ (blk F 1 s) * (ψ (blk F 2 (-1)))⁻¹) * u⁻¹ := by group
    _ = ψ (blk F 2 (-1)) * ψ (blk F 1 s) * (ψ (blk F 2 (-1)))⁻¹ := by
      have hc' : u * (ψ (blk F 2 (-1)) * ψ (blk F 1 s) * (ψ (blk F 2 (-1)))⁻¹) =
          (ψ (blk F 2 (-1)) * ψ (blk F 1 s) * (ψ (blk F 2 (-1)))⁻¹) * u := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact hc
      rw [hc']
      group

theorem conj_node_le (ψ : SL(4, F) →* G) {u : G} (hu : ∀ x ∈ ψ.range, u * x = x * u) :
    ∀ k ∈ node ψ, (u * ψ (blk F 2 (-1))) * k * (u * ψ (blk F 2 (-1)))⁻¹ ∈ node ψ := by
  intro k hk
  obtain ⟨s, rfl⟩ := (mem_node_iff ψ k).mp hk
  rw [e_conj_blk1 ψ hu s]
  exact (mem_node_iff ψ _).mpr ⟨_, rfl⟩

theorem mem_normalizer_node (ψ : SL(4, F) →* G) {u : G} (hu : ∀ x ∈ ψ.range, u * x = x * u)
    (hu2 : u * u = 1) :
    u * ψ (blk F 2 (-1)) ∈ Subgroup.normalizer (node ψ : Set G) := by
  have ht : ψ (blk F 2 (-1)) * ψ (blk F 2 (-1)) = 1 := by
    rw [← map_mul]
    have : blk F 2 (-1) * blk F 2 (-1) = 1 := by rw [← map_mul]; simp
    rw [this, map_one]
  have hut : u * ψ (blk F 2 (-1)) = ψ (blk F 2 (-1)) * u := hu _ ⟨_, rfl⟩
  have hee : (u * ψ (blk F 2 (-1))) * (u * ψ (blk F 2 (-1))) = 1 := by
    calc (u * ψ (blk F 2 (-1))) * (u * ψ (blk F 2 (-1)))
        = u * (ψ (blk F 2 (-1)) * u) * ψ (blk F 2 (-1)) := by group
      _ = u * (u * ψ (blk F 2 (-1))) * ψ (blk F 2 (-1)) := by rw [hut]
      _ = (u * u) * (ψ (blk F 2 (-1)) * ψ (blk F 2 (-1))) := by group
      _ = 1 := by rw [hu2, ht, one_mul]
  have hinv : (u * ψ (blk F 2 (-1)))⁻¹ = u * ψ (blk F 2 (-1)) := inv_eq_of_mul_eq_one_right hee
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_node_le ψ hu h hh
  · intro hh
    have := conj_node_le ψ hu _ hh
    have e1 : (u * ψ (blk F 2 (-1))) * ((u * ψ (blk F 2 (-1))) * h *
        (u * ψ (blk F 2 (-1)))⁻¹) * (u * ψ (blk F 2 (-1)))⁻¹ = h := by
      rw [hinv]
      calc (u * ψ (blk F 2 (-1))) * ((u * ψ (blk F 2 (-1))) * h * (u * ψ (blk F 2 (-1))))
            * (u * ψ (blk F 2 (-1)))
          = ((u * ψ (blk F 2 (-1))) * (u * ψ (blk F 2 (-1)))) * h *
            ((u * ψ (blk F 2 (-1))) * (u * ψ (blk F 2 (-1)))) := by group
        _ = h := by rw [hee, one_mul, mul_one]
    rwa [e1] at this

theorem commute_of_fixed_node (h2 : (2 : F) ≠ 0) (ψ : SL(4, F) →* G)
    (hker : ψ.ker ≤ Subgroup.center SL(4, F)) {u : G} (hu : ∀ x ∈ ψ.range, u * x = x * u)
    {k k' : G} (hk : k ∈ node ψ) (hk' : k' ∈ node ψ)
    (hek : (u * ψ (blk F 2 (-1))) * k * (u * ψ (blk F 2 (-1)))⁻¹ = k)
    (hek' : (u * ψ (blk F 2 (-1))) * k' * (u * ψ (blk F 2 (-1)))⁻¹ = k') :
    k * k' = k' * k := by
  have key : ∀ s : SL(2, F), (u * ψ (blk F 2 (-1))) * ψ (blk F 1 s) *
      (u * ψ (blk F 2 (-1)))⁻¹ = ψ (blk F 1 s) →
      (s : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro s hs
    have h1 := e_conj_blk1 ψ hu s
    rw [h1] at hs
    have h3 : ψ (blk F 1 (diagConj2 1 (-1) s) * (blk F 1 s)⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    have h4 : blk F 1 (diagConj2 1 (-1) s) * (blk F 1 s)⁻¹ ∈ Subgroup.center SL(4, F) :=
      hker (MonoidHom.mem_ker.mpr h3)
    rw [← map_inv, ← map_mul] at h4
    have h5 := eq_one_of_blk_mem_center 1 _ h4
    exact (diagConj2_one_neg_one_eq_self_iff h2 s).mp (mul_inv_eq_one.mp h5)
  obtain ⟨s, rfl⟩ := (mem_node_iff ψ k).mp hk
  obtain ⟨s', rfl⟩ := (mem_node_iff ψ k').mp hk'
  obtain ⟨h01, h10⟩ := key s hek
  obtain ⟨h01', h10'⟩ := key s' hek'
  calc ψ (blk F 1 s) * ψ (blk F 1 s') = ψ (blk F 1 (s * s')) := by rw [map_mul, map_mul]
    _ = ψ (blk F 1 (s' * s)) := by rw [sl2_commute_of_diagonal s s' h01 h10 h01' h10']
    _ = ψ (blk F 1 s') * ψ (blk F 1 s) := by rw [map_mul, map_mul]

theorem z₁_comm_e (ψ : SL(4, F) →* G) {u : G} (hu : ∀ x ∈ ψ.range, u * x = x * u) :
    ψ (blk F 1 (-1)) * (u * ψ (blk F 2 (-1))) = (u * ψ (blk F 2 (-1))) * ψ (blk F 1 (-1)) := by
  have h1 : ψ (blk F 1 (-1)) * u = u * ψ (blk F 1 (-1)) := (hu _ ⟨_, rfl⟩).symm
  have h2 : ψ (blk F 1 (-1)) * ψ (blk F 2 (-1)) = ψ (blk F 2 (-1)) * ψ (blk F 1 (-1)) := by
    rw [← map_mul, ← map_mul, blk2_neg_one_comm_blk1_neg_one.symm]
  calc ψ (blk F 1 (-1)) * (u * ψ (blk F 2 (-1)))
      = (ψ (blk F 1 (-1)) * u) * ψ (blk F 2 (-1)) := by group
    _ = u * (ψ (blk F 1 (-1)) * ψ (blk F 2 (-1))) := by rw [h1]; group
    _ = u * (ψ (blk F 2 (-1)) * ψ (blk F 1 (-1))) := by rw [h2]
    _ = (u * ψ (blk F 2 (-1))) * ψ (blk F 1 (-1)) := by group

theorem chart_node (ψ : SL(4, F) →* G) (s : SL(2, F)) :
    ψ (blk F 1 (-1)) * ψ (blk F 2 s) * (ψ (blk F 1 (-1)))⁻¹ =
      ψ (blk F 2 (diagConj2 (-1) 1 s)) := by
  rw [← map_inv, ← map_mul, ← map_mul, blk1_neg_one_conj_blk2]

theorem range_eq_sup_nodes (ψ : SL(4, F) →* G) :
    ψ.range = (blk F 0).range.map ψ ⊔ node ψ ⊔ (blk F 2).range.map ψ := by
  rw [MonoidHom.range_eq_map, ← blk_sup_eq_top (F := F), Subgroup.map_sup, Subgroup.map_sup]
  rfl

end CHN

end CFSG.ClassicalInvolution.Asc77
