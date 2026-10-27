module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem isPGroup_S : IsPGroup 2 h.S := by
  obtain ⟨P₀, hP₀⟩ := h.S_sylow
  have h1 : IsPGroup 2 ((P₀ : Subgroup _).map
      (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)).subtype) := P₀.isPGroup'.map _
  rwa [hP₀, map_subgroupOf_eq_of_le h.S_le] at h1

theorem comm_a {s : H} (hs : s ∈ h.S) : s * h.a = h.a * s :=
  mem_centralizer_singleton_iff.mp (mem_inf.mp (h.S_le hs)).1

theorem S_le_normalizer : h.S ≤ normalizer (h.J : Set H) := fun _ hs => (mem_inf.mp (h.S_le hs)).2

theorem a_mem_coreActionKernel : h.a ∈ coreActionKernel h.J :=
  GSLit.mem_coreActionKernel_of_le_centralizer h.J_le

theorem a_mem_S : h.a ∈ h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H) with hM
  have haM : h.a ∈ M := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    (mem_coreActionKernel.mp h.a_mem_coreActionKernel).1⟩
  have ha2 : IsPGroup 2 (zpowers h.a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_a, pow_one])
  have hnorm : zpowers h.a ≤ normalizer (h.S : Set H) := by
    refine (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro s hs
    exact h.comm_a hs
  have hR : IsPGroup 2 ↥(zpowers h.a ⊔ h.S) := ha2.to_sup_of_normal_right' h.isPGroup_S hnorm
  have hRM : zpowers h.a ⊔ h.S ≤ M := sup_le (zpowers_le.mpr haM) h.S_le
  obtain ⟨P₀, hP₀⟩ := h.S_sylow
  have hle : (P₀ : Subgroup M) ≤ (zpowers h.a ⊔ h.S).subgroupOf M := by
    rw [hP₀]
    exact fun y hy => mem_subgroupOf.mpr (mem_sup_right (mem_subgroupOf.mp hy))
  have heq := P₀.is_maximal' (Q := (zpowers h.a ⊔ h.S).subgroupOf M) hR.comap_subtype hle
  have h1 : (⟨h.a, haM⟩ : M) ∈ (zpowers h.a ⊔ h.S).subgroupOf M :=
    mem_subgroupOf.mpr (mem_sup_left (mem_zpowers h.a))
  rw [heq, hP₀] at h1
  exact mem_subgroupOf.mp h1

theorem a_mem_P : h.a ∈ h.P := mem_inf.mpr ⟨h.a_mem_S, h.a_mem_coreActionKernel⟩

theorem x_comm_a : h.x * h.a = h.a * h.x := h.comm_a h.x_mem

theorem P_le_S : h.P ≤ h.S := inf_le_left

theorem D_le_S : h.D ≤ h.S := inf_le_left

theorem D_le_J : h.D ≤ h.J := inf_le_right

theorem B_le_P : h.B ≤ h.P := h.B_le

theorem B_le_S : h.B ≤ h.S := h.B_le_P.trans h.P_le_S

theorem _root_.CFSG.ComponentClassification.GSThmB.eq_bot_of_isPGroup_two_of_coprime
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} (h2 : IsPGroup 2 K)
    (hc : Nat.Coprime 2 (Nat.card K)) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  rcases n with _ | n
  · exact Subgroup.eq_bot_of_card_eq K (by rw [hn, pow_zero])
  · rw [hn, pow_succ] at hc
    exact absurd (Nat.Coprime.coprime_dvd_right (dvd_mul_left 2 _) hc) (by norm_num)

theorem S_inf_oddCore_eq_bot : h.S ⊓ (pPrimeCore 2 h.J).map h.J.subtype = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_of_isPGroup_two_of_coprime (h.isPGroup_S.to_le inf_le_left) ?_
  have hc : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 h.J).map h.J.subtype)) := by
    rw [Subgroup.card_map_of_injective h.J.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hc

theorem D_comm_P {d p : H} (hd : d ∈ h.D) (hp : p ∈ h.P) : d * p = p * d := by
  have hdS := h.D_le_S hd
  have hdJ := h.D_le_J hd
  have hpS := h.P_le_S hp
  have hpC := (mem_inf.mp hp).2
  have h1 : d⁻¹ * p⁻¹ * d * p ∈ (pPrimeCore 2 h.J).map h.J.subtype :=
    (mem_coreActionKernel.mp hpC).2 d hdJ
  have h2 : d⁻¹ * p⁻¹ * d * p ∈ h.S :=
    mul_mem (mul_mem (mul_mem (inv_mem hdS) (inv_mem hpS)) hdS) hpS
  have h3 : d⁻¹ * p⁻¹ * d * p = 1 := by
    have := h.S_inf_oddCore_eq_bot ▸ mem_inf.mpr ⟨h2, h1⟩
    exact mem_bot.mp this
  calc d * p = (p * d) * (d⁻¹ * p⁻¹ * d * p) := by group
    _ = p * d := by rw [h3, mul_one]

theorem D_le_Q : h.D ≤ h.Q := by
  intro d hd
  refine mem_inf.mpr ⟨h.D_le_S hd, centralizer_le_normalizer _ ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact (h.D_comm_P hd (h.B_le_P hb)).symm

theorem isQuasisimple_J : IsQuasisimple (OddBar h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.J _ h.J_le).1
    h.isPComponent_J).2.2

theorem isQuasisimple_K : IsQuasisimple (OddBar h.K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.K _ h.isPComponent_K.1).1
    h.isPComponent_K.2).2.2

theorem B_le_coreActionKernel : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right

theorem isPGroup_B : IsPGroup 2 h.B := h.isPGroup_S.to_le h.B_le_S

theorem orderOf_eq_two_pow_of_mem_S {y : H} (hy : y ∈ h.S) : ∃ k : ℕ, orderOf y = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup_S) ⟨y, hy⟩
  exact ⟨k, by rw [← Subgroup.orderOf_mk y hy, hk]⟩

theorem V_eq_K (hKa : conjugate h.K h.a = h.K) : h.V = h.K := by
  rw [Hyp52.V, ← h.layer_eq_K, hKa, sup_idem]

end Hyp52

end CFSG.ComponentClassification.GSThmB
