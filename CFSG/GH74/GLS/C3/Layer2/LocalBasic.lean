module

public import CFSG.GH74.GLS.C3.Layer2.Config
public import CFSG.GH74.GLS.C3.Layer2.GenLemmas

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2

section Plain

variable {G : Type} [Group G] {x : G} {K : Subgroup G}

theorem CxK_le_centralizer : CxK x K ≤ centralizer ({x} : Set G) := by
  unfold CxK; exact inf_le_left

theorem self_mem_centralizer_singleton : x ∈ centralizer ({x} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

@[expose] def xC (x : G) : ↥(centralizer ({x} : Set G)) := ⟨x, self_mem_centralizer_singleton⟩

end Plain

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfig

theorem x_order (h : IsAConfig n x K T Q S a) : orderOf x = 2 := by
  obtain ⟨⟨hx, _⟩, _⟩ := h.twoTerminal
  exact hx

theorem x_sq (h : IsAConfig n x K T Q S a) : x ^ 2 = 1 := by
  have := pow_orderOf_eq_one x
  rwa [h.x_order] at this

theorem x_ne_one (h : IsAConfig n x K T Q S a) : x ≠ 1 := by
  intro hx
  have := h.x_order
  rw [hx, orderOf_one] at this
  omega

theorem K_le_C (h : IsAConfig n x K T Q S a) : K ≤ centralizer ({x} : Set G) := by
  obtain ⟨⟨_, _, hKC, _⟩, _⟩ := h.twoTerminal
  exact hKC

theorem C_le_normalizer_K (h : IsAConfig n x K T Q S a) :
    centralizer ({x} : Set G) ≤ normalizer (K : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h.normalInC c hc k hk, fun hk => ?_⟩
  have := h.normalInC c⁻¹ (inv_mem hc) _ hk
  simpa [mul_assoc] using this

theorem T_le_C (h : IsAConfig n x K T Q S a) : T ≤ centralizer ({x} : Set G) := h.sylowT.le

theorem Q_le_T (h : IsAConfig n x K T Q S a) : Q ≤ T := by
  rw [h.hQ]; exact inf_le_left

theorem Q_le_CxK (h : IsAConfig n x K T Q S a) : Q ≤ CxK x K := by
  rw [h.hQ]; exact inf_le_right

theorem pPrimeCore_eq_bot_of_normal (h : IsAConfig n x K T Q S a) {N : Subgroup G}
    (hNC : N ≤ centralizer ({x} : Set G))
    (hN : centralizer ({x} : Set G) ≤ normalizer (N : Set G)) : pPrimeCore 2 ↥N = ⊥ := by
  have hNn : (N.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mpr hN
  have h1 : pPrimeCore 2 ↥(N.subgroupOf (centralizer ({x} : Set G))) = ⊥ := by
    have h2 := pPrimeCore_map_le_of_normal (N.subgroupOf (centralizer ({x} : Set G)))
    rw [h.noOddCore, le_bot_iff] at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h2
  have h3 := pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hNC)
  rw [h1, Subgroup.map_bot] at h3
  exact h3.symm

theorem pPrimeCore_K (h : IsAConfig n x K T Q S a) : pPrimeCore 2 ↥K = ⊥ :=
  h.pPrimeCore_eq_bot_of_normal h.K_le_C h.C_le_normalizer_K

theorem pPrimeCoreOf_K (h : IsAConfig n x K T Q S a) : pPrimeCoreOf 2 K = ⊥ := by
  unfold pPrimeCoreOf
  rw [h.pPrimeCore_K, Subgroup.map_bot]

theorem K_equiv_alt (h : IsAConfig n x K T Q S a) : Nonempty (↥K ≃* alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := h.kbar
  exact ⟨(((QuotientGroup.quotientMulEquivOfEq h.pPrimeCore_K).trans
    QuotientGroup.quotientBot).symm).trans e⟩

theorem mem_CxK_iff (h : IsAConfig n x K T Q S a) (c : G) :
    c ∈ CxK x K ↔ c ∈ centralizer ({x} : Set G) ∧ ∀ k ∈ K, k * c = c * k := by
  unfold CxK
  rw [h.pPrimeCoreOf_K, mem_inf]
  refine and_congr_right fun _ => ⟨fun ⟨_, _, hk⟩ k hk' => ?_, fun hc' => ?_⟩
  · have := hk k hk'
    rw [Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · have hfix : ∀ k' ∈ K, c * k' * c⁻¹ = k' := fun k' hk' => by
      rw [← hc' k' hk']; group
    have hfix' : ∀ k' ∈ K, c⁻¹ * k' * c = k' := fun k' hk' => by
      rw [mul_assoc, hc' k' hk', ← mul_assoc]; simp
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [mem_normalizer_iff]
      intro k
      refine ⟨fun hk => by rw [hfix k hk]; exact hk, fun hk' => ?_⟩
      have h1 := hfix' _ hk'
      have h2 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
      rw [h2] at h1
      rw [h1]; exact hk'
    · rw [mem_normalizer_iff]
      intro k
      simp [Subgroup.mem_bot]
    · rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hc' k hk)

theorem CxK_normal (h : IsAConfig n x K T Q S a) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ y ∈ CxK x K, c * y * c⁻¹ ∈ CxK x K := by
  intro c hc y hy
  rw [h.mem_CxK_iff] at hy ⊢
  obtain ⟨hyC, hyK⟩ := hy
  refine ⟨mul_mem (mul_mem hc hyC) (inv_mem hc), fun k hk => ?_⟩
  have hk' : c⁻¹ * k * c ∈ K := by
    have := h.normalInC c⁻¹ (inv_mem hc) k hk
    simpa using this
  have h1 := hyK _ hk'
  calc k * (c * y * c⁻¹) = c * ((c⁻¹ * k * c) * y) * c⁻¹ := by group
    _ = c * (y * (c⁻¹ * k * c)) * c⁻¹ := by rw [h1]
    _ = c * y * c⁻¹ * k := by group

theorem C_le_normalizer_CxK (h : IsAConfig n x K T Q S a) :
    centralizer ({x} : Set G) ≤ normalizer (CxK x K : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h.CxK_normal c hc y hy, fun hy => ?_⟩
  have := h.CxK_normal c⁻¹ (inv_mem hc) _ hy
  simpa [mul_assoc] using this

theorem x_mem_T (h : IsAConfig n x K T Q S a) : x ∈ T := by
  have hs : IsSylowOf 2 (T.subgroupOf (centralizer ({x} : Set G))) ⊤ := by
    refine (isSylowOf_map_subtype_iff (centralizer ({x} : Set G))).1 ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h.T_le_C, Subgroup.map_top,
      Subgroup.range_subtype]
    exact h.sylowT
  have hx2 : (⟨x, self_mem_centralizer_singleton⟩ : ↥(centralizer ({x} : Set G))) ^ 2 = 1 :=
    Subtype.ext h.x_sq
  have hxc : (⟨x, self_mem_centralizer_singleton⟩ : ↥(centralizer ({x} : Set G))) ∈
      Subgroup.center _ :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  exact mem_of_isSylowOf_of_central_involution hs hx2 hxc

theorem x_mem_CxK (h : IsAConfig n x K T Q S a) : x ∈ CxK x K :=
  (h.mem_CxK_iff x).2 ⟨self_mem_centralizer_singleton, fun _ hk =>
    (mem_centralizer_singleton_iff.1 (h.K_le_C hk))⟩

theorem x_mem_Q (h : IsAConfig n x K T Q S a) : x ∈ Q := by
  rw [h.hQ]; exact ⟨h.x_mem_T, h.x_mem_CxK⟩

theorem pPrimeCore_CxK (h : IsAConfig n x K T Q S a) : pPrimeCore 2 ↥(CxK x K) = ⊥ :=
  h.pPrimeCore_eq_bot_of_normal CxK_le_centralizer h.C_le_normalizer_CxK

theorem CxK_eq_Q (h : IsAConfig n x K T Q S a) : CxK x K = Q := by
  apply le_antisymm _ h.Q_le_CxK
  have : IsElementaryAbelian 2 ↥Q := h.elemQ
  have : IsElementaryAbelian 2 ↥(Q.subgroupOf (CxK x K)) :=
    isElementaryAbelian_subgroupOf h.Q_le_CxK
  obtain ⟨-, hQp, hQidx⟩ := isSylowOf_iff.1 h.sylowQ
  have hQ4 : Nat.card ↥(Q.subgroupOf (CxK x K)) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_CxK).toEquiv).trans h.card_Q
  have hxc : (⟨x, h.x_mem_CxK⟩ : ↥(CxK x K)) ∈ Subgroup.center _ :=
    Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (mem_centralizer_singleton_iff.1 (CxK_le_centralizer g.2))
  have htop := eq_top_of_klein_sylow_central (Q.subgroupOf (CxK x K)) hQp.comap_subtype hQidx hQ4
    (x := ⟨x, h.x_mem_CxK⟩) (Subgroup.mem_subgroupOf.2 h.x_mem_Q)
    (fun hx => h.x_ne_one (congrArg Subtype.val hx)) hxc h.pPrimeCore_CxK
  intro y hy
  have : (⟨y, hy⟩ : ↥(CxK x K)) ∈ Q.subgroupOf (CxK x K) := by rw [htop]; trivial
  exact this

theorem mem_Q_iff (h : IsAConfig n x K T Q S a) (c : G) :
    c ∈ Q ↔ c ∈ centralizer ({x} : Set G) ∧ ∀ k ∈ K, k * c = c * k := by
  rw [← h.mem_CxK_iff, h.CxK_eq_Q]

theorem Q_normal (h : IsAConfig n x K T Q S a) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
  intro c hc q hq
  rw [← h.CxK_eq_Q] at hq ⊢
  exact h.CxK_normal c hc q hq

theorem C_le_normalizer_Q (h : IsAConfig n x K T Q S a) :
    centralizer ({x} : Set G) ≤ normalizer (Q : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h.Q_normal c hc y hy, fun hy => ?_⟩
  have := h.Q_normal c⁻¹ (inv_mem hc) _ hy
  simpa [mul_assoc] using this

theorem Q_comm (h : IsAConfig n x K T Q S a) {q r : G} (hq : q ∈ Q) (hr : r ∈ Q) :
    q * r = r * q := by
  have := h.elemQ
  exact setLike_mul_comm hq hr

theorem Q_sq (h : IsAConfig n x K T Q S a) {q : G} (hq : q ∈ Q) : q ^ 2 = 1 := by
  have := h.elemQ
  exact elemPow_eq_one_of_isElementaryAbelian q hq

theorem K_inf_Q (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n) : K ⊓ Q = ⊥ := by
  obtain ⟨e⟩ := h.K_equiv_alt
  rw [eq_bot_iff]
  rintro y ⟨hyK, hyQ⟩
  have hy : ∀ k ∈ K, k * y = y * k := ((h.mem_Q_iff y).1 hyQ).2
  have hc : e ⟨y, hyK⟩ ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hy k k.2)
  rw [alternatingGroup.center_eq_bot (by simpa using hn.trans' (by norm_num)),
    Subgroup.mem_bot] at hc
  have : (⟨y, hyK⟩ : ↥K) = 1 := e.injective (by rw [hc, map_one])
  exact congrArg Subtype.val this

end IsAConfig

end CFSG.GH74.GLS
