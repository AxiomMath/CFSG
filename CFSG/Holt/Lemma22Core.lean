module

public import CFSG.Assembly.Defs
public import CFSG.Holt.Centralizer

public section

namespace CFSG.Holt

open MulAction Equiv Equiv.Perm CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem exists_odd_complement_of_commute {K Z : Subgroup G} (hZ : fusionIsSylowIn 2 Z K)
    (hcomm : ∀ k ∈ K, ∀ z ∈ Z, z * k = k * z) :
    ∃ O : Subgroup G, O ≤ K ∧ Odd (Nat.card O) ∧ (∀ k ∈ K, ∃ z ∈ Z, ∃ o ∈ O, k = z * o) ∧
      ∀ k ∈ K, Odd (orderOf k) → k ∈ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_eq_subgroupOf_of_fusionIsSylowIn hZ
  have hPZ : ∀ z : K, z ∈ (P : Subgroup K) ↔ (z : G) ∈ Z := fun z => by
    rw [hP, Subgroup.mem_subgroupOf]
  have hPc : Subgroup.normalizer (P : Set K) ≤ Subgroup.centralizer (P : Set K) := fun n _ =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      Subtype.ext (hcomm n n.2 z ((hPZ z).mp hz))
  have hdvd := MonoidHom.not_dvd_card_ker_transferSylow P hPc
  set τ := MonoidHom.transferSylow P hPc
  refine ⟨τ.ker.map K.subtype, Subgroup.map_subtype_le _, ?_, fun k hk => ?_, fun k hk hodd => ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, Nat.odd_iff]
    omega
  · obtain ⟨⟨o, z⟩, hoz, -⟩ :=
      (MonoidHom.ker_transferSylow_isComplement' P hPc).existsUnique ⟨k, hk⟩
    have hz : ((z : K) : G) ∈ Z := (hPZ z).mp z.2
    refine ⟨z, hz, o, ⟨o, o.2, rfl⟩, ?_⟩
    have h := congrArg Subtype.val hoz
    simp only [Subgroup.coe_mul] at h
    rw [← h]
    exact (hcomm _ (o : K).2 _ hz).symm
  · refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hodd' : Nat.Coprime 2 (orderOf (⟨k, hk⟩ : K)) := by
      rw [Nat.coprime_two_left, Subgroup.orderOf_mk]
      exact hodd
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (P.isPGroup'.orderOf_coprime hodd' _)
      (orderOf_map_dvd τ _))

end CFSG.Holt
