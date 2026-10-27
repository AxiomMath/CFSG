module

public import CFSG.Holt.H78.Defs

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section LongInv

theorem smul_eq_iff_of_mem_longInvAt {t : G} {α : Ω} (ht : t ∈ longInvAt G Ω α) (ω : Ω) :
    t • ω = ω ↔ ω = α := by
  obtain ⟨⟨-, β, -, hβ⟩, htα⟩ := ht
  exact ⟨fun h => (hβ ω h).trans (hβ α htα).symm, fun h => h ▸ htα⟩

theorem mul_self_eq_one_of_mem_longInv {t : G} (ht : t ∈ longInv G Ω) : t * t = 1 := by
  rw [← sq, ← ht.1, pow_orderOf_eq_one]

theorem inv_eq_self_of_mem_longInv {t : G} (ht : t ∈ longInv G Ω) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_longInv ht)

theorem longInvAt_subset_longInv (α : Ω) : longInvAt G Ω α ⊆ longInv G Ω := fun _ ht => ht.1

theorem longInvSwap_subset_longInv (α β : Ω) : longInvSwap G Ω α β ⊆ longInv G Ω :=
  fun _ ht => ht.1

@[simp] theorem longInvSwap_self (α : Ω) : longInvSwap G Ω α α = longInvAt G Ω α := rfl

theorem exists_mem_longInvAt {t : G} (ht : t ∈ longInv G Ω) : ∃ α : Ω, t ∈ longInvAt G Ω α :=
  let ⟨α, hα, _⟩ := ht.2
  ⟨α, ht, hα⟩

theorem eq_of_mem_longInvAt {t : G} {α β : Ω} (hα : t ∈ longInvAt G Ω α)
    (hβ : t ∈ longInvAt G Ω β) : α = β :=
  (smul_eq_iff_of_mem_longInvAt hβ α).mp hα.2

theorem iUnion_longInvAt : ⋃ α : Ω, longInvAt G Ω α = longInv G Ω :=
  Set.Subset.antisymm (Set.iUnion_subset longInvAt_subset_longInv) fun _ ht =>
    Set.mem_iUnion.mpr (exists_mem_longInvAt ht)

theorem pairwise_disjoint_longInvAt : Pairwise (Function.onFun Disjoint (longInvAt G Ω)) :=
  fun _ _ h => Set.disjoint_left.mpr fun _ hα hβ => h (eq_of_mem_longInvAt hα hβ)

theorem smul_eq_of_mem_longInvSwap {t : G} {α β : Ω} (ht : t ∈ longInvSwap G Ω α β) :
    t • β = α := by
  rw [← ht.2, ← mul_smul, mul_self_eq_one_of_mem_longInv ht.1, one_smul]

theorem longInvSwap_comm (α β : Ω) : longInvSwap G Ω α β = longInvSwap G Ω β α :=
  Set.ext fun _ => ⟨fun ht => ⟨ht.1, smul_eq_of_mem_longInvSwap ht⟩,
    fun ht => ⟨ht.1, smul_eq_of_mem_longInvSwap ht⟩⟩

theorem conj_mem_longInv {t : G} (ht : t ∈ longInv G Ω) (g : G) :
    g * t * g⁻¹ ∈ longInv G Ω :=
  ⟨(orderOf_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)).symm.trans ht.1,
    existsUnique_fixed_of_isConj ht.2 (isConj_iff.mpr ⟨g, rfl⟩)⟩

theorem conj_mem_longInv_iff {t : G} (g : G) : g * t * g⁻¹ ∈ longInv G Ω ↔ t ∈ longInv G Ω :=
  ⟨fun h => by simpa [mul_assoc] using conj_mem_longInv h g⁻¹, fun h => conj_mem_longInv h g⟩

theorem conj_mem_longInvAt {t : G} {α : Ω} (ht : t ∈ longInvAt G Ω α) (g : G) :
    g * t * g⁻¹ ∈ longInvAt G Ω (g • α) :=
  ⟨conj_mem_longInv ht.1 g, by rw [mul_smul, mul_smul, inv_smul_smul, ht.2]⟩

theorem conj_mem_longInvSwap {t : G} {α β : Ω} (ht : t ∈ longInvSwap G Ω α β) (g : G) :
    g * t * g⁻¹ ∈ longInvSwap G Ω (g • α) (g • β) :=
  ⟨conj_mem_longInv ht.1 g, by rw [mul_smul, mul_smul, inv_smul_smul, ht.2]⟩

theorem conj_longInvAt (g : G) (α : Ω) :
    (fun t => g * t * g⁻¹) '' longInvAt G Ω α = longInvAt G Ω (g • α) := by
  refine Set.Subset.antisymm (Set.image_subset_iff.mpr fun t ht => conj_mem_longInvAt ht g)
    fun s hs => ⟨g⁻¹ * s * g⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
  have h := conj_mem_longInvAt hs g⁻¹
  rwa [inv_smul_smul] at h

theorem conj_longInvSwap (g : G) (α β : Ω) :
    (fun t => g * t * g⁻¹) '' longInvSwap G Ω α β = longInvSwap G Ω (g • α) (g • β) := by
  refine Set.Subset.antisymm (Set.image_subset_iff.mpr fun t ht => conj_mem_longInvSwap ht g)
    fun s hs => ⟨g⁻¹ * s * g⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
  have h := conj_mem_longInvSwap hs g⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h

end LongInv

section Fixed

theorem IsStarGroup.longInvAt_nonempty (hG : IsStarGroup G Ω) (α : Ω) :
    (longInvAt G Ω α).Nonempty := by
  obtain ⟨t, ht, -⟩ := hG.star α ⊥ IsPGroup.of_bot bot_le
    (by rw [fixSet_bot, Nat.card_univ]; exact hG.three_le_card)
  exact ⟨t, ht⟩

theorem IsStarGroup.longInv_nonempty (hG : IsStarGroup G Ω) : (longInv G Ω).Nonempty := by
  have : Nonempty Ω := (Nat.card_pos_iff.mp (by have := hG.three_le_card; omega)).1
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty (Classical.arbitrary Ω)
  exact ⟨t, ht.1⟩

variable [Finite Ω]

theorem IsStarGroup.odd_card_fixSet (hG : IsStarGroup G Ω) {S : Subgroup G}
    (hS : IsPGroup 2 S) : Odd (Nat.card (fixSet Ω S)) :=
  odd_card_fixSet_of_odd hG.odd_card hS

theorem IsStarGroup.fixSet_nonempty (hG : IsStarGroup G Ω) {S : Subgroup G}
    (hS : IsPGroup 2 S) : (fixSet Ω S).Nonempty :=
  fixSet_nonempty_of_odd hG.odd_card hS

theorem three_le_card_fixSet_iff (hΩ : Odd (Nat.card Ω)) {S : Subgroup G} (hS : IsPGroup 2 S) :
    3 ≤ Nat.card (fixSet Ω S) ↔ 1 < Nat.card (fixSet Ω S) := by
  obtain ⟨k, hk⟩ := odd_card_fixSet_of_odd hΩ hS
  omega

end Fixed

section Hull

theorem jHull_le_iff {K : Subgroup G} : jHull G Ω ≤ K ↔ longInv G Ω ⊆ K :=
  Subgroup.closure_le K

instance jHull_normal : (jHull G Ω).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : jHull G Ω ≤ (jHull G Ω).comap (MulAut.conj g).toMonoidHom :=
    jHull_le_iff.mpr fun t ht => longInv_subset_jHull (conj_mem_longInv ht g)
  exact h hn

instance jOddCore_normal : (jOddCore G Ω).Normal :=
  ConjAct.normal_of_characteristic_of_normal

theorem mem_jOrbitKernel_iff {h : G} :
    h ∈ jOrbitKernel G Ω ↔ h ∈ jHull G Ω ∧ ∀ ω : Ω, h • ω ∈ orbit (jOddCore G Ω) ω := by
  rw [mem_jOrbitKernel]
  refine and_congr_right fun _ => forall_congr' fun ω => ?_
  rw [smul_orbit_eq_orbit_smul, orbit_eq_iff]

theorem jOddCore_le_jOrbitKernel : jOddCore G Ω ≤ jOrbitKernel G Ω := fun h hh =>
  mem_jOrbitKernel_iff.mpr ⟨jOddCore_le_jHull hh, fun _ => ⟨⟨h, hh⟩, rfl⟩⟩

instance jOrbitKernel_normal : (jOrbitKernel G Ω).Normal := by
  refine ⟨fun h hh g => mem_jOrbitKernel_iff.mpr
    ⟨(jHull_normal).conj_mem h (mem_jOrbitKernel_iff.mp hh).1 g, fun ω => ?_⟩⟩
  have h2 : g • h • g⁻¹ • ω ∈ g • orbit (jOddCore G Ω) (g⁻¹ • ω) :=
    Set.smul_mem_smul_set ((mem_jOrbitKernel_iff.mp hh).2 (g⁻¹ • ω))
  rw [smul_orbit_eq_orbit_smul, smul_inv_smul] at h2
  simpa only [mul_smul] using h2

variable [Finite G]

theorem odd_card_jOddCore : Odd (Nat.card (jOddCore G Ω)) := by
  rw [jOddCore, oddCoreOf, Subgroup.card_map_of_injective (jHull G Ω).subtype_injective,
    ← Nat.coprime_two_left]
  exact CFSG.pPrimeCore_coprime_card

theorem jOddCore_le_pPrimeCore : jOddCore G Ω ≤ CFSG.pPrimeCore 2 G :=
  le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr odd_card_jOddCore⟩

theorem jOddCore_eq_jHull_inf_pPrimeCore :
    jOddCore G Ω = jHull G Ω ⊓ CFSG.pPrimeCore 2 G := by
  refine le_antisymm (le_inf jOddCore_le_jHull jOddCore_le_pPrimeCore) ?_
  have hcop : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 G).subgroupOf (jHull G Ω))) := by
    rw [← Subgroup.card_map_of_injective (jHull G Ω).subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      CFSG.pPrimeCore_coprime_card
  have hle : (CFSG.pPrimeCore 2 G).subgroupOf (jHull G Ω) ≤ CFSG.pPrimeCore 2 (jHull G Ω) :=
    le_sSup ⟨CFSG.pPrimeCore_normal.subgroupOf _, hcop⟩
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype]
  exact Subgroup.map_mono hle

end Hull

end CFSG.Holt.H78
