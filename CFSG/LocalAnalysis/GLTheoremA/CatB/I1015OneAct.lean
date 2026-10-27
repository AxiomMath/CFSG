module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneAct

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA

variable {G : Type} [Group G] [Finite G]

noncomputable def i1015oneAct {L B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    ↥B →* MulAut (PSimple 3 L) :=
  (chevAut 3 L).comp (Subgroup.inclusion hBN)

noncomputable def i1015oneImage {L T : Subgroup G} (hTL : T ≤ L) : Subgroup (PSimple 3 L) :=
  (T.subgroupOf L).map (chevQuotHom 3 L)

theorem i1015oneAct_apply_eq_one_iff {X L B : Subgroup G} (hL : GLAPComponent 3 X L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (x : ↥B) :
    i1015oneAct hBN x = 1 ↔ (x : G) ∈ centModSubgroup 3 L := by
  rw [← centMod_iff]
  exact chevAut_eq_one_iff Nat.prime_three hL (hBN x.2)

theorem i1015oneAct_ker {X L B : Subgroup G} (hL : GLAPComponent 3 X L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    (i1015oneAct hBN).ker = (B ⊓ centModSubgroup 3 L).subgroupOf B := by
  ext x
  rw [MonoidHom.mem_ker, i1015oneAct_apply_eq_one_iff hL hBN, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem i1015oneAct_card_mul {X L B : Subgroup G} (hL : GLAPComponent 3 X L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(B ⊓ centModSubgroup 3 L) * Nat.card ↥(i1015oneAct hBN).range = Nat.card ↥B := by
  have hker : Nat.card ↥(i1015oneAct hBN).ker = Nat.card ↥(B ⊓ centModSubgroup 3 L) := by
    rw [i1015oneAct_ker hL hBN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 := Subgroup.card_mul_index (i1015oneAct hBN).ker
  rw [Subgroup.index_ker, hker] at h1
  exact h1

theorem i1015oneAct_range_isElemAbelian {L B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hB : IsElemAbelian 3 B) :
    IsElemAbelian 3 (i1015oneAct hBN).range := by
  unfold IsElemAbelian at hB ⊢
  obtain ⟨hcomm, hexp⟩ := hB
  refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
  · rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, isMulCommutative_iff.1 hcomm x y]
  · rintro a ⟨x, rfl⟩
    have hx : x ^ 3 = 1 := Subtype.ext (by simpa using hexp (x : G) x.2)
    rw [← map_pow, hx, map_one]

theorem i1015oneAct_card_ge {X L B : Subgroup G} (hL : GLAPComponent 3 X L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hcard : 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 L) ≤ Nat.card ↥B) :
    27 ≤ Nat.card ↥(i1015oneAct hBN).range := by
  have hk : 0 < Nat.card ↥(B ⊓ centModSubgroup 3 L) := Nat.card_pos
  have h := i1015oneAct_card_mul hL hBN
  refine Nat.le_of_mul_le_mul_left ?_ hk
  calc Nat.card ↥(B ⊓ centModSubgroup 3 L) * 27
      = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 L) := by ring
    _ ≤ Nat.card ↥B := hcard
    _ = Nat.card ↥(B ⊓ centModSubgroup 3 L) * Nat.card ↥(i1015oneAct hBN).range := h.symm

theorem i1015oneImage_isPGroup {L T : Subgroup G} (hTL : T ≤ L) (hT2 : IsPGroup 2 T) :
    IsPGroup 2 (i1015oneImage hTL) := by
  have hTm : IsPGroup 2 (T.subgroupOf L) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  exact hTm.map (chevQuotHom 3 L)

theorem i1015oneImage_ne_bot {X L T : Subgroup G} (hL : GLAPComponent 3 X L) (hTL : T ≤ L)
    (hT2 : IsPGroup 2 T) (hTn : ¬ T ≤ GLAPPrimeCoreOf 3 L) : i1015oneImage hTL ≠ ⊥ := by
  intro hbot
  apply hTn
  intro t ht
  have htL : t ∈ L := hTL ht
  have hmem : chevQuotHom 3 L ⟨t, htL⟩ ∈ i1015oneImage hTL :=
    Subgroup.mem_map_of_mem _ ((Subgroup.mem_subgroupOf).2 ht)
  rw [hbot, Subgroup.mem_bot] at hmem
  have hzc : pQuotHom 3 L ⟨t, htL⟩ ∈ Subgroup.center (PQuot 3 L) :=
    (QuotientGroup.eq_one_iff (pQuotHom 3 L ⟨t, htL⟩)).1 hmem
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hzk : pQuotHom 3 L ⟨t, htL⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have h2 : (⟨t, htL⟩ : ↥L) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [h2, map_one]
  set z := pQuotHom 3 L ⟨t, htL⟩ with hz
  have hN : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g z := Subgroup.mem_center_iff.1 hzc g
    rw [(hc.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact zpow_mem (Subgroup.mem_zpowers z) m
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hzk)
      (Nat.Coprime.pow_right _ (by norm_num))
  have hle : Subgroup.zpowers z ≤ CFSG.pPrimeCore 3 (PQuot 3 L) := le_sSup ⟨hN, hcop⟩
  have hbot2 : CFSG.pPrimeCore 3 (PQuot 3 L) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hz1 : z = 1 := by
    have hzmem : z ∈ CFSG.pPrimeCore 3 (PQuot 3 L) := hle (Subgroup.mem_zpowers z)
    rw [hbot2, Subgroup.mem_bot] at hzmem
    exact hzmem
  have hker : (⟨t, htL⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := by
    rw [← ker_pQuotHom 3 L]
    exact MonoidHom.mem_ker.2 hz1
  exact (chev_mem_glaPPrimeCoreOf_iff htL).2 hker

theorem i1015oneImage_invariant {L B T : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hTL : T ≤ L) (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    ∀ α ∈ (i1015oneAct hBN).range, ∀ y ∈ i1015oneImage hTL, α y ∈ i1015oneImage hTL := by
  rintro α ⟨x, rfl⟩ y hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
  have hxT : (x : G) ∈ Subgroup.normalizer (T : Set G) := hBT x.2
  have hconj : L.normalizerMonoidHom (Subgroup.inclusion hBN x) k ∈ T.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have hcoe : ((L.normalizerMonoidHom (Subgroup.inclusion hBN x) k : ↥L) : G) =
        (x : G) * (k : G) * (x : G)⁻¹ := rfl
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.1 hxT _).1 hk
  have hα : i1015oneAct hBN x (chevQuotHom 3 L k) =
      chevQuotHom 3 L (L.normalizerMonoidHom (Subgroup.inclusion hBN x) k) :=
    chevAut_chevQuotHom 3 L (Subgroup.inclusion hBN x) k
  rw [hα]
  exact Subgroup.mem_map_of_mem _ hconj

theorem i1015oneConfig {X L B T : Subgroup G} (hL : GLAPComponent 3 X L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hB : IsElemAbelian 3 B)
    (hcard : 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 L) ≤ Nat.card ↥B) (hTL : T ≤ L)
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hTn : ¬ T ≤ GLAPPrimeCoreOf 3 L) :
    27 ≤ Nat.card ↥(i1015oneAct hBN).range ∧ IsElemAbelian 3 (i1015oneAct hBN).range ∧
      i1015oneImage hTL ≠ ⊥ ∧ IsPGroup 2 (i1015oneImage hTL) ∧
      ∀ α ∈ (i1015oneAct hBN).range, ∀ y ∈ i1015oneImage hTL, α y ∈ i1015oneImage hTL :=
  ⟨i1015oneAct_card_ge hL hBN hcard, i1015oneAct_range_isElemAbelian hBN hB,
    i1015oneImage_ne_bot hL hTL hT2 hTn, i1015oneImage_isPGroup hTL hT2,
    i1015oneImage_invariant hBN hTL hBT⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneAct
