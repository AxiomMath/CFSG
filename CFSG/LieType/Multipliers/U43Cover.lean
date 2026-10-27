module

public import Certificates.Certificate10013
public import CFSG.LieType.Multipliers.KernelStructure

public section

namespace CFSG.LieType.Multipliers.U43

open CFSG.CosetTable Subgroup

theorem kernel_relations :
    zk 5 ^ 3 = 1 ∧ zk 6 ^ 12 = 1 ∧ zk 0 = zk 6 ^ 6 ∧ zk 1 = 1 ∧ zk 2 = 1 ∧ zk 3 = zk 6 ^ 6 ∧
      zk 4 = zk 6 ^ 3 :=
  Certificates.certificate10013

theorem mem_comm_rels (i : Fin 2) {k : ℕ} (hk : k < 7) :
    commWord [(i, true)] (rels.getD k []) ∈ coverWs := by
  revert i k
  decide

theorem zk_mem_center {k : ℕ} (hk : k < 7) : zk k ∈ center (PG 2 coverWs) := by
  rw [← centralizer_univ, ← coe_top, ← PresentedGroup.closure_range_of, centralizer_closure,
    mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}
      (FreeGroup.mk (commWord [(i, true)] (rels.getD k []))) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_comm_rels i hk))
  rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

noncomputable def zkHom :
    Multiplicative (ZMod 3) × Multiplicative (ZMod 12) →* PG 2 coverWs :=
  MonoidHom.noncommCoprod (powHom (zk 5) 3 kernel_relations.1) (powHom (zk 6) 12 kernel_relations.2.1)
    fun a b => Commute.pow_pow
      (Commute.symm (Subgroup.mem_center_iff.mp (zk_mem_center (k := 5) (by omega)) (zk 6))) _ _

theorem zk5_mem : zk 5 ∈ (zkHom).range :=
  ⟨(Multiplicative.ofAdd 1, 1), by
    simp only [zkHom, powHom, MonoidHom.noncommCoprod_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero, mul_one]
    exact pow_one (zk 5)⟩

theorem zk6_mem : zk 6 ∈ (zkHom).range :=
  ⟨(1, Multiplicative.ofAdd 1), by
    simp only [zkHom, powHom, MonoidHom.noncommCoprod_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero, one_mul]
    exact pow_one (zk 6)⟩

theorem closure_zk_le {S : Set (PG 2 coverWs)}
    (hS : ∀ x ∈ S, ∃ k < 7, x = zk k) : closure S ≤ (zkHom).range := by
  rw [closure_le]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := hS x hx
  obtain ⟨h5, -, h0, h1, h2, h3, h4⟩ := kernel_relations
  have p6 : ∀ n : ℕ, zk 6 ^ n ∈ (zkHom).range := fun n => pow_mem zk6_mem n
  interval_cases k
  · rw [h0]; exact p6 6
  · rw [h1]; exact one_mem _
  · rw [h2]; exact one_mem _
  · rw [h3]; exact p6 6
  · rw [h4]; exact p6 3
  · exact zk5_mem
  · exact zk6_mem

theorem card_closure_zk {S : Set (PG 2 coverWs)}
    (hS : ∀ x ∈ S, ∃ k < 7, x = zk k) : Finite (closure S) ∧ Nat.card (closure S) ≤ 36 := by
  have hle := closure_zk_le hS
  have hfin : Finite (zkHom).range := Set.finite_range _ |>.to_subtype
  refine ⟨Finite.of_injective _ (Subgroup.inclusion_injective hle), ?_⟩
  calc Nat.card (closure S) ≤ Nat.card (zkHom).range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (Multiplicative (ZMod 3) × Multiplicative (ZMod 12)) :=
        Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    _ = 36 := by simp [Nat.card_eq_fintype_card]

end CFSG.LieType.Multipliers.U43
