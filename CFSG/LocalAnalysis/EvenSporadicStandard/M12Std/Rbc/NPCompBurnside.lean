module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicOddComplement
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup

private theorem eq_of_ne_one_of_card_le_two {α : Type*} [Group α] [Finite α]
    (hcard : Nat.card α ≤ 2) {a b : α} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have h3 : ({1, a, b} : Set α).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, a, b, fun h => ha h.symm, fun h => hb h.symm, hab, rfl⟩
  have hle : ({1, a, b} : Set α).ncard ≤ Nat.card α := Set.ncard_le_card _
  omega

theorem card_eq_card_sylow_of_oddCore_eq_bot {M : Type*} [Group M] [Finite M]
    (hO : CFSG.oddCore M = ⊥) (P : Sylow 2 M) (hP : IsCyclic ↥(P : Subgroup M)) :
    Nat.card M = Nat.card ↥(P : Subgroup M) := by
  by_cases heven : Even (Nat.card M)
  · obtain ⟨kernel, hchar, hodd, hcompl, _⟩ :=
      CFSG.TwoRankLowerBound.Helpers.exists_characteristic_odd_complement_of_cyclic_sylow_two
        P hP heven
    haveI : kernel.Characteristic := hchar
    have hker_le : kernel ≤ CFSG.oddCore M := le_sSup ⟨inferInstance, hodd⟩
    rw [hO, le_bot_iff] at hker_le
    have hcard : Nat.card kernel = 1 := Subgroup.card_eq_one.mpr hker_le
    have h := hcompl.card_mul_card
    rw [hcard, one_mul] at h
    exact h.symm
  · have hoddM : Odd (Nat.card M) := Nat.not_even_iff_odd.mp heven
    have htop_le : (⊤ : Subgroup M) ≤ CFSG.oddCore M :=
      le_sSup ⟨inferInstance, by rw [Subgroup.card_top]; exact hoddM⟩
    rw [hO] at htop_le
    have htop_eq : (⊤ : Subgroup M) = ⊥ := le_bot_iff.mp htop_le
    have hM : Nat.card M = 1 := by
      simpa using (Subgroup.card_eq_one.mpr htop_eq : Nat.card (⊤ : Subgroup M) = 1)
    have hPbot : (P : Subgroup M) = ⊥ := le_bot_iff.mp (le_top.trans htop_le)
    rw [hM, hPbot, Subgroup.card_bot]

theorem oddCore_eq_bot_of_normal {K : Type*} [Group K] [Finite K] (hO : CFSG.oddCore K = ⊥)
    (N : Subgroup K) [N.Normal] : CFSG.oddCore ↥N = ⊥ := by
  have hO2 : CFSG.pPrimeCore 2 K = ⊥ :=
    (CFSG.EvenSporadicStandard.Solomon78.oddCore_eq_pPrimeCore_two' K).symm.trans hO
  have hs : N.IsSubnormal := (inferInstance : N.Normal).isSubnormal
  have hle := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (G := K) hs
  rw [hO2, le_bot_iff] at hle
  rw [CFSG.EvenSporadicStandard.Solomon78.oddCore_eq_pPrimeCore_two']
  exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pPrimeCore 2 N)
    N.subtype_injective).1 hle

theorem card_eq_two_of_card_centralizer_le_two {M : Type*} [Group M] [Finite M]
    (hO : CFSG.oddCore M = ⊥) {h : M} (hh : h * h = 1) (h1 : h ≠ 1)
    (hc : Nat.card ↥(centralizer ({h} : Set M)) ≤ 2) : Nat.card M = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf h = 2 := orderOf_eq_prime (p := 2) (by rwa [pow_two]) h1
  have hzp : IsPGroup 2 (Subgroup.zpowers h) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨P, hPle⟩ := hzp.exists_le_sylow
  have hhP : h ∈ (P : Subgroup M) := hPle (Subgroup.mem_zpowers h)
  haveI : Nontrivial ↥(P : Subgroup M) :=
    ⟨⟨⟨h, hhP⟩, 1, fun heq => h1 (by simpa using Subtype.ext_iff.mp heq)⟩⟩
  have hcenter : Nontrivial (Subgroup.center ↥(P : Subgroup M)) :=
    P.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥(P : Subgroup M))
  have hzcomm : (⟨h, hhP⟩ : ↥(P : Subgroup M)) * (z : ↥(P : Subgroup M)) =
      (z : ↥(P : Subgroup M)) * (⟨h, hhP⟩ : ↥(P : Subgroup M)) :=
    Subgroup.mem_center_iff.mp z.2 (⟨h, hhP⟩ : ↥(P : Subgroup M))
  have hzmem_c : ((z : ↥(P : Subgroup M)) : M) ∈ centralizer ({h} : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simpa using congrArg Subtype.val hzcomm
  have hhmem_c : h ∈ centralizer ({h} : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  have hzM_ne : ((z : ↥(P : Subgroup M)) : M) ≠ 1 := by
    intro hzM
    apply hz1
    exact Subtype.ext (Subtype.ext hzM)
  have hzeq : (⟨h, hhmem_c⟩ : ↥(centralizer ({h} : Set M))) =
      ⟨((z : ↥(P : Subgroup M)) : M), hzmem_c⟩ :=
    eq_of_ne_one_of_card_le_two hc
      (by intro heq; exact h1 (by simpa using Subtype.ext_iff.mp heq))
      (by intro heq; exact hzM_ne (by simpa using Subtype.ext_iff.mp heq))
  have hz_eq : h = ((z : ↥(P : Subgroup M)) : M) := congrArg Subtype.val hzeq
  have hzP : (z : ↥(P : Subgroup M)) = (⟨h, hhP⟩ : ↥(P : Subgroup M)) := by
    apply Subtype.ext
    exact hz_eq.symm
  have hcent : (⟨h, hhP⟩ : ↥(P : Subgroup M)) ∈ Subgroup.center ↥(P : Subgroup M) :=
    hzP ▸ z.2
  have hleC : (P : Subgroup M) ≤ centralizer ({h} : Set M) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hcent (⟨p, hp⟩ : ↥(P : Subgroup M)))).symm
  have hPcard_ge : 2 ≤ Nat.card ↥(P : Subgroup M) := by
    calc 2 = Nat.card ↥(Subgroup.zpowers h) := by rw [Nat.card_zpowers, hord]
      _ ≤ Nat.card ↥(P : Subgroup M) := Subgroup.card_le_of_le hPle
  have hPcard_le : Nat.card ↥(P : Subgroup M) ≤
      Nat.card ↥(centralizer ({h} : Set M)) := Subgroup.card_le_of_le hleC
  have hPcard : Nat.card ↥(P : Subgroup M) = 2 := le_antisymm (hPcard_le.trans hc) hPcard_ge
  have hcyc : IsCyclic ↥(P : Subgroup M) := isCyclic_of_prime_card hPcard
  have hM : Nat.card M = Nat.card ↥(P : Subgroup M) :=
    card_eq_card_sylow_of_oddCore_eq_bot hO P hcyc
  rw [hM, hPcard]

theorem le_center_of_card_le_two {K : Type*} [Group K] [Finite K] (H : Subgroup K) [H.Normal]
    (hH : Nat.card ↥H ≤ 2) : H ≤ center K := by
  intro h hh
  rw [Subgroup.mem_center_iff]
  intro k
  by_cases h1 : h = 1
  · subst h
    simp
  · have hconj : k * h * k⁻¹ ∈ H := (inferInstance : H.Normal).conj_mem h hh k
    have hne : k * h * k⁻¹ ≠ 1 := by
      intro hc
      apply h1
      calc h = k⁻¹ * (k * h * k⁻¹) * k := by group
        _ = 1 := by rw [hc]; group
    have heq : (⟨k * h * k⁻¹, hconj⟩ : ↥H) = ⟨h, hh⟩ :=
      eq_of_ne_one_of_card_le_two hH
        (by intro heq; exact hne (by simpa using Subtype.ext_iff.mp heq))
        (by intro heq; exact h1 (by simpa using Subtype.ext_iff.mp heq))
    have hval : k * h * k⁻¹ = h := congrArg Subtype.val heq
    calc k * h = (k * h * k⁻¹) * k := by group
      _ = h * k := by rw [hval]

end CFSG.EvenSporadicStandard.M12Std.Rbc
