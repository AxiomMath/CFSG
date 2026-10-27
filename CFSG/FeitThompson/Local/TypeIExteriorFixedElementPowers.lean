module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.OddOrder.InvariantHallComplement

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem subgroupOf_hallCoreIn (M : Subgroup G) :
    (hallCoreIn M).subgroupOf M = hallCore M := by
  rw [hallCoreIn_def, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem relIndex_hallCoreIn (M : Subgroup G) :
    (hallCoreIn M).relIndex M = (hallCore M).index := by
  rw [Subgroup.relIndex, subgroupOf_hallCoreIn]

theorem hallCoreIn_eq_self_of_index_eq_one {M : Subgroup G}
    (h : (hallCore M).index = 1) : hallCoreIn M = M := by
  rw [hallCoreIn_def, Subgroup.index_eq_one.1 h, ← MonoidHom.range_eq_map, range_subtype]

theorem mem_hallCoreIn_of_orderOf_dvd [Finite G] {M : Subgroup G} {x : G} (hx : x ∈ M)
    (hord : orderOf x ∣ Nat.card (hallCore M)) : x ∈ hallCoreIn M := by
  have hcrit := (isHallSubgroup_hallCore (X := ↥M)).isHallPiSubgroup.mem_iff (⟨x, hx⟩ : M)
  have hmem : (⟨x, hx⟩ : M) ∈ hallCore M := by
    refine hcrit.2 fun p hp => ?_
    rw [(Subgroup.orderOf_coe (⟨x, hx⟩ : M)).symm] at hp
    exact dvd_trans (Nat.dvd_of_mem_primeFactors hp) hord
  exact ⟨⟨x, hx⟩, hmem, rfl⟩

theorem isComplementTo_map_subtype {M : Subgroup G} {K L : Subgroup M}
    (h : K.IsComplement' L) : IsComplementTo M (K.map M.subtype) (L.map M.subtype) := by
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hset : ((K : Set M)) * (L : Set M) = Set.univ := h.mul_eq
    have h2 := congrArg (fun s : Set M => (M.subtype : M →* G) '' s) hset
    rw [Set.image_mul] at h2
    simpa [Subgroup.coe_map, Set.image_univ, Subtype.range_coe] using h2
  · rw [← Subgroup.map_inf _ _ _ M.subtype_injective, h.disjoint.eq_bot, Subgroup.map_bot]

theorem FTS_type_I_exterior_power_centralizer
    (h₁ : Statements.FTS_type_I_complement_structure.{u})
    (_h₂ : Statements.FTS_type_I_core_kappa_identity.{u}) :
    Statements.FTS_type_I_exterior_power_centralizer.{u} := by
  intro G _ _ hG M hM hMI k hak hk y hy
  obtain ⟨hyM, hyH, hyc⟩ := hy
  rw [hallCoreIn_def, Subgroup.card_subtype] at hak
  rw [relIndex_hallCoreIn] at hk ⊢
  set a := Nat.card (hallCore ↥M) with ha
  set b := (hallCore ↥M).index with hb
  have hab : a.Coprime b := isGreatest_hallCore.1.2.2
  have hb1 : b ≠ 1 := fun h => hyH (by rw [hallCoreIn_eq_self_of_index_eq_one h]; exact hyM)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (Nat.dvd_one.1 ((Nat.modEq_iff_dvd' (by norm_num : (0 : ℕ) ≤ 1)).1 hk)) hb1
    · exact h
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hk1).1 hk.symm
  have hkm : k = b * m + 1 := by omega
  have hyord : orderOf y ∣ a * b := by
    rw [ha, hb, Subgroup.card_mul_index]
    exact M.orderOf_dvd_natCard hyM
  have huord : orderOf (y ^ k) ∣ b :=
    orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.1 (hyord.trans (mul_dvd_mul_right hak b)))
  have huM : y ^ k ∈ M := M.pow_mem hyM k
  have hvM : y * (y ^ k)⁻¹ ∈ M := M.mul_mem hyM (M.inv_mem huM)
  have hvord : orderOf (y * (y ^ k)⁻¹) ∣ a :=
    orderOf_dvd_of_pow_eq_one (by
      have hv : y * (y ^ k)⁻¹ = (y ^ (b * m))⁻¹ := by rw [hkm, pow_succ]; group
      rw [hv, inv_pow, ← pow_mul]
      exact inv_eq_one.2 (orderOf_dvd_iff_pow_eq_one.1 (hyord.trans ⟨m, by ring⟩)))
  have hvH : y * (y ^ k)⁻¹ ∈ hallCoreIn M := mem_hallCoreIn_of_orderOf_dvd hvM hvord
  have hu1 : y ^ k ≠ 1 := by
    intro h
    rw [h, inv_one, mul_one] at hvH
    exact hyH hvH
  obtain ⟨x, hx, hx1⟩ :=
    (centIn (hallCoreIn M) {y}).nontrivial_iff_exists_ne_one.1
      ((centIn (hallCoreIn M) {y}).nontrivial_iff_ne_bot.2 hyc)
  have hxu : x ∈ centIn (hallCoreIn M) {y ^ k} := by
    refine mem_centIn.2 ⟨(mem_centIn.1 hx).1, ?_⟩
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hcom : Commute y x := (mem_centIn.1 hx).2 y rfl
    exact hcom.pow_left k
  have hcu : centIn (hallCoreIn M) {y ^ k} ≠ ⊥ :=
    (centIn (hallCoreIn M) {y ^ k}).nontrivial_iff_ne_bot.1
      ((centIn (hallCoreIn M) {y ^ k}).nontrivial_iff_exists_ne_one.2 ⟨x, hxu, hx1⟩)
  refine ⟨hu1, huord, hcu, ?_⟩
  have hsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hcop : a.Coprime (Nat.card (zpowers (⟨y ^ k, huM⟩ : M))) := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨y ^ k, huM⟩ : M)]
    exact Nat.Coprime.coprime_dvd_right huord hab
  obtain ⟨L, hKL, hcompl⟩ :=
    exists_isComplement'_le_of_coprime (H := hallCore ↥M)
      (K := zpowers (⟨y ^ k, huM⟩ : M)) hab hcop
  set U : Subgroup G := L.map M.subtype with hU
  have hUcompl : IsComplementTo M (hallCoreIn M) U := by
    rw [hallCoreIn_def, hU]
    exact isComplementTo_map_subtype hcompl
  have hXU : (zpowers (y ^ k) : Subgroup G) ≤ U := by
    rw [Subgroup.zpowers_le, hU]
    exact ⟨⟨y ^ k, huM⟩, hKL (Subgroup.mem_zpowers _), rfl⟩
  have hXbot : (zpowers (y ^ k) : Subgroup G) ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
  have hcX : centIn (hallCoreIn M) ((zpowers (y ^ k) : Subgroup G) : Set G) ≠ ⊥ := by
    rw [centIn_def, centralizer_coe_zpowers]
    exact hcu
  obtain ⟨hle, huniq⟩ := (h₁ G hG M hM hMI U hUcompl).2 _ hXU hXbot hcX
  rw [centralizer_coe_zpowers] at hle huniq
  exact ⟨hM, hle, fun N hN hNle => huniq N hN hNle⟩

end

end CFSG.FeitThompson.Proofs
