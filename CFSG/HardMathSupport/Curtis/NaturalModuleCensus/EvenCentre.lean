module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

section Sylow

variable {G X : Type*} [Group G] [Finite G] [Group X]

theorem mem_normalizer_of_map_mem_normalizer (ψ : G →* X) (hker : ψ.ker ≤ Subgroup.center G)
    (T : Sylow 2 G) {x : G}
    (hx : ψ x ∈ Subgroup.normalizer (((T : Subgroup G).map ψ : Subgroup X) : Set X)) :
    x ∈ Subgroup.normalizer ((T : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Subgroup.mem_normalizer_fintype
  intro t ht
  have h1 : ψ (x * t * x⁻¹) ∈ (T : Subgroup G).map ψ := by
    have := (Subgroup.mem_normalizer_iff.1 hx (ψ t)).1 ⟨t, ht, rfl⟩
    simpa using this
  obtain ⟨s, hs, hse⟩ := h1
  have hk : s⁻¹ * (x * t * x⁻¹) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
  set k := s⁻¹ * (x * t * x⁻¹) with hkdef
  have hz : x * t * x⁻¹ = s * k := by rw [hkdef]; group
  have hkc : ∀ g : G, g * k = k * g := Subgroup.mem_center_iff.1 (hker hk)
  have hcomm : Commute s k := hkc s
  obtain ⟨a, ha⟩ := T.isPGroup' ⟨s, hs⟩
  obtain ⟨b, hb⟩ := T.isPGroup' ⟨t, ht⟩
  have ha' : s ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hb' : t ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hz2 : (x * t * x⁻¹) ^ 2 ^ b = 1 := by rw [conj_pow, hb', mul_one, mul_inv_cancel]
  have hk2 : k ^ 2 ^ (max a b) = 1 := by
    have h1 : s ^ 2 ^ (max a b) = 1 := by
      obtain ⟨m, hm⟩ : 2 ^ a ∣ 2 ^ (max a b) := pow_dvd_pow 2 (le_max_left a b)
      rw [hm, pow_mul, ha', one_pow]
    have h2 : (x * t * x⁻¹) ^ 2 ^ (max a b) = 1 := by
      obtain ⟨m, hm⟩ : 2 ^ b ∣ 2 ^ (max a b) := pow_dvd_pow 2 (le_max_right a b)
      rw [hm, pow_mul, hz2, one_pow]
    rw [hz, hcomm.mul_pow, h1, one_mul] at h2
    exact h2
  have hkn : (Subgroup.zpowers k).Normal := ⟨fun n hn g => by
    obtain ⟨j, rfl⟩ := hn
    have : g * k ^ j * g⁻¹ = k ^ j := by
      rw [(Commute.zpow_right (show Commute g k from hkc g) j).eq]; group
    rw [this]; exact Subgroup.zpow_mem_zpowers k j⟩
  have hkp : IsPGroup 2 (Subgroup.zpowers k) := by
    intro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := hy
    refine ⟨max a b * 0 + (max a b), ?_⟩
    apply Subtype.ext
    simp only [zero_add, mul_zero]
    change (k ^ j) ^ 2 ^ (max a b) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk2, one_zpow]
  have hkT : k ∈ (T : Subgroup G) := hkp.le_sylow_of_normal T (Subgroup.mem_zpowers k)
  rw [hz]
  exact Subgroup.mul_mem _ hs hkT

theorem normalizer_map_le_map_of_central (ψ : G →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) (T : Sylow 2 G) {J : Subgroup G}
    (hNJ : Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ J) :
    Subgroup.normalizer (((T : Subgroup G).map ψ : Subgroup X) : Set X) ≤ J.map ψ := by
  intro y hy
  obtain ⟨x, rfl⟩ := hψ y
  exact ⟨x, hNJ (mem_normalizer_of_map_mem_normalizer ψ hker T hy), rfl⟩

end Sylow

theorem pSubgroup_le_perfectJoin_of_quotient_central {G X : Type*} [Group G] [Group X] [Finite G]
    {ψ : G →* X} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G) {p : ℕ}
    (hp : p.Prime) (hpk : ¬ p ∣ Nat.card ψ.ker) (hH : PerfectJoinHub p X) (T : Sylow 2 G)
    {J : Subgroup G} (hNJ : Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ J)
    {A : Subgroup G} (hAJ : A ≤ J) (hA : IsPGroup p A) : A ≤ perfectJoin J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkJ : ψ.ker ≤ J :=
    hker.trans ((Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)).trans hNJ)
  have hNS : Subgroup.normalizer (((T.mapSurjective hψ : Sylow 2 X) : Subgroup X) : Set X) ≤
      J.map ψ := by
    rw [Sylow.coe_mapSurjective]
    exact normalizer_map_le_map_of_central ψ hψ hker T hNJ
  have h1 := hH (T.mapSurjective hψ) (J.map ψ) hNS (A.map ψ) (Subgroup.map_mono hAJ) (hA.map ψ)
  rw [← ToralCensus.map_perfectJoin_eq ψ hψ hker hkJ] at h1
  exact ToralCensus.le_of_map_le_map_of_central ψ hker hp hpk hA h1

theorem pSubgroup_le_perfectJoin_of_parabolic_central {Y : Type*} [Group Y] [Finite Y]
    {L J : Subgroup Y} (hP : IsParabolicTwo L J) {p : ℕ} (hp : p.Prime)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hH : PerfectJoinHub p (↥L ⧸ Subgroup.center ↥L)) {A : Subgroup Y} (hAJ : A ≤ J)
    (hA : IsPGroup p A) : A ≤ perfectJoin J := by
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker = Subgroup.center ↥L :=
    QuotientGroup.ker_mk' _
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  have hNJ' : Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
    have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ (T' : Subgroup ↥L) := by
      simpa [T', Subgroup.mem_subgroupOf] using ht
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
    simpa [T', Subgroup.mem_subgroupOf] using h2
  have hAJ' : A.subgroupOf L ≤ J.subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hAJ (Subgroup.mem_subgroupOf.1 hx))
  have hpZ' : ¬ p ∣ Nat.card (QuotientGroup.mk' (Subgroup.center ↥L)).ker := by
    rw [hker]
    exact hpZ
  have h := pSubgroup_le_perfectJoin_of_quotient_central (QuotientGroup.mk'_surjective _)
    hker.le hp hpZ' hH T' hNJ' hAJ' (hA.comap_subtype (K := L))
  intro a ha
  have hmem : (⟨a, hJL (hAJ ha)⟩ : ↥L) ∈ perfectJoin (J.subgroupOf L) := h ha
  have hle : (J.subgroupOf L).map L.subtype ≤ J := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  exact CFSG.AGLEmbedding.ParabAutIrr.map_perfectJoin_le L.subtype hle ⟨_, hmem, rfl⟩

structure CompParabE {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) : Prop where
  comp : IsComponentOf L ⊤
  type : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)
  parab : IsParabolicTwo L J
  ne_top : J ≠ L
  ne_borel : ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)

theorem CompParab.toE {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} (h : CompParab L J) :
    CompParabE L J :=
  ⟨h.comp, h.type, h.parab, h.ne_top, h.ne_borel⟩

open TauCeti in
theorem card_center_dvd_six_of_small
    (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type} [Group A] [Finite A]
    [Group.IsPerfect A] (hS : IsSmallTwoOrG2 (A ⧸ Subgroup.center A)) :
    Nat.card (Subgroup.center A) ∣ 6 := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
  · have hn5 : 5 ≤ n := by omega
    have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
      (CFSG.GH74.Generic.centralQuotientMap e)
      (CFSG.GH74.Generic.centralQuotientMap_surjective e)
      (CFSG.GH74.Generic.centralQuotientMap_ker e).le
    rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
      (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn5).2] at hdvd
    rcases hn with rfl | rfl | rfl
    · rw [ite_eq_right (by decide)] at hdvd
      exact hdvd.trans (by norm_num)
    · rw [ite_eq_left (by decide)] at hdvd
      exact hdvd
    · rw [ite_eq_right (by decide)] at hdvd
      exact hdvd.trans (by norm_num)
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 7 ∧ q.exponent = 1 := by
      rw [PrimePower.card_def] at hq7
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq7
    have hc := statedClassicalModel_of_typeA hv (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hp, hf] at hm
    have h := ToralCensus.card_center_dvd_multiplierOrders hGA e hm
    simp only [CFSG.Blueprint.Multiplier.genericOrders,
      CFSG.Blueprint.Multiplier.exceptionalOrders] at h
    exact (show Nat.card (Subgroup.center A) ∣ 2 by simpa using h).trans (by norm_num)
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := by
      rw [PrimePower.card_def] at hq3
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq3
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hp, hf] at hm
    have h := ToralCensus.card_center_dvd_multiplierOrders hGA e hm
    simp only [CFSG.Blueprint.Multiplier.genericOrders,
      CFSG.Blueprint.Multiplier.exceptionalOrders] at h
    have h2 := h
    simp at h2
    rw [h2, Subgroup.card_bot]
    norm_num

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
