module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG

open scoped commutatorElement

theorem pPrimeCore_eq_bot_of_normal_quotient_simple
    {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {N : Subgroup X} [N.Normal]
    (hN : pPrimeCore p ↥N = ⊥) (hsimple : IsSimpleGroup (X ⧸ N))
    (hdvd : p ∣ Nat.card (X ⧸ N)) :
    pPrimeCore p X = ⊥ := by
  classical
  rw [pPrimeCore_eq_bot_iff]
  intro K hK hcop
  let q : X →* X ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hKn : (K.map q).Normal := hK.map q hq
  have hKcop : Nat.Coprime p (Nat.card (K.map q)) :=
    hcop.coprime_dvd_right (Subgroup.card_map_dvd (H := K) q)
  have hKne : K.map q ≠ ⊤ := by
    intro htop
    have hpK : p ∣ Nat.card (K.map q) := by
      rw [htop, Subgroup.card_top]
      exact hdvd
    exact (hp.coprime_iff_not_dvd.1 hKcop) hpK
  haveI : (K.map q).Normal := hKn
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.map q) with hbot | htop
  ·
    have hKN : K ≤ N := by
      intro k hk
      have hkq : q k ∈ K.map q := Subgroup.mem_map_of_mem q hk
      rw [hbot, Subgroup.mem_bot] at hkq
      exact (QuotientGroup.eq_one_iff k).1 hkq
    have hKn' : (K.subgroupOf N).Normal := hK.subgroupOf N
    have hKcopN : Nat.Coprime p (Nat.card ↥(K.subgroupOf N)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv]
      exact hcop
    have hle : K.subgroupOf N ≤ pPrimeCore p ↥N := le_sSup ⟨hKn', hKcopN⟩
    rw [hN] at hle
    rw [eq_bot_iff]
    intro k hk
    have hmem : (⟨k, hKN hk⟩ : ↥N) ∈ K.subgroupOf N := Subgroup.mem_subgroupOf.2 hk
    have h1 : (⟨k, hKN hk⟩ : ↥N) = 1 := by
      have := hle hmem
      rwa [Subgroup.mem_bot] at this
    exact Subtype.ext_iff.1 h1
  · exact absurd htop hKne

theorem le_centralizer_of_isQuasisimple_of_coprime {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {N L : Subgroup H} [N.Normal] [L.Normal] (hL : CFSG.IsQuasisimple ↥L)
    (hNcop : Nat.Coprime p (Nat.card N)) (hLp : ¬ Nat.Coprime p (Nat.card L)) :
    N ≤ Subgroup.centralizer (L : Set H) := by
  classical
  have hNL_n : ((N ⊓ L).subgroupOf L).Normal := inferInstance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hNL_n with htop | hcenter
  · exfalso
    have hLN : L ≤ N := by
      intro l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ (N ⊓ L).subgroupOf L := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
    have hpL : p ∣ Nat.card L := by
      by_contra h
      exact hLp ((hp.coprime_iff_not_dvd).2 h)
    exact ((hp.coprime_iff_not_dvd).1 hNcop) (hpL.trans (Subgroup.card_dvd_of_le hLN))
  · have hcomm_le : ⁅N, L⁆ ≤ N ⊓ L :=
      le_inf (Subgroup.commutator_le_left (H₁ := N) (H₂ := L))
        (Subgroup.commutator_le_right (H₁ := N) (H₂ := L))
    have hcomm : ∀ x ∈ ⁅N, L⁆, ∀ y ∈ L, y * x = x * y := by
      intro x hx y hy
      have hxNL : x ∈ N ⊓ L := hcomm_le hx
      have hxL : x ∈ L := (Subgroup.mem_inf.1 hxNL).2
      have hc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L :=
        hcenter (by rw [Subgroup.mem_subgroupOf]; exact hxNL)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hy⟩)
    have h1 : ⁅⁅N, L⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcomm x hx y hy
    have h2 : ⁅⁅L, N⁆, L⁆ = ⊥ := by
      rw [← Subgroup.commutator_comm N L]
      exact h1
    have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := L) (H₂ := L) (H₃ := N) h2 h1
    have hperf : ⁅L, L⁆ = L := by
      rw [← Subgroup.map_subtype_commutator L, hL.1.commutator_eq_top,
        Subgroup.map_top, Subgroup.range_subtype]
    rw [hperf] at hrot
    have hbot : ⁅N, L⁆ = ⊥ := by
      rwa [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hbot

end CFSG
