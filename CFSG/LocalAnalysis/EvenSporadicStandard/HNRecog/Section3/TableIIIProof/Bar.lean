module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

@[expose] def tableIIIBar (z : G) (K : Subgroup G) : Subgroup (Gbar z) :=
  (K.subgroupOf (Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z)))

theorem tableIII_card_eq_card_inf_mul_card_bar [Finite G] {z : G} {K : Subgroup G}
    (hK : K ≤ Gx z) :
    Nat.card ↥K = Nat.card ↥(K ⊓ Qz z) * Nat.card ↥(tableIIIBar z K) := by
  set N := CFSG.pCore 2 ↥(Gx z)
  set K' := K.subgroupOf (Gx z)
  have hbar : Nat.card ↥(tableIIIBar z K) = N.relIndex K' := by
    rw [tableIIIBar, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have hKK' : Nat.card ↥K' = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hmapK : K'.map (Gx z).subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hK]
  have hQ : N.map (Gx z).subtype = Qz z := rfl
  have hinf : Nat.card ↥(N.subgroupOf K') = Nat.card ↥(K ⊓ Qz z) := by
    rw [← Subgroup.card_map_of_injective K'.subtype_injective, Subgroup.subgroupOf_map_subtype,
      ← Subgroup.card_map_of_injective (Gx z).subtype_injective,
      Subgroup.map_inf_eq _ _ _ (Gx z).subtype_injective, hmapK, hQ, inf_comm]
  rw [← hKK', hbar, ← hinf]
  exact (Subgroup.card_mul_index (N.subgroupOf K')).symm

theorem tableIII_bar_mono {z : G} {K L : Subgroup G} (h : K ≤ L) :
    tableIIIBar z K ≤ tableIIIBar z L :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem tableIII_barOf_mem_bar {z : G} {K : Subgroup G} (x : ↥(Gx z)) (hx : (x : G) ∈ K) :
    barOf z x ∈ tableIIIBar z K :=
  ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem tableIII_exists_of_mem_bar {z : G} {K : Subgroup G} {y : Gbar z}
    (hy : y ∈ tableIIIBar z K) : ∃ x : ↥(Gx z), (x : G) ∈ K ∧ barOf z x = y := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
