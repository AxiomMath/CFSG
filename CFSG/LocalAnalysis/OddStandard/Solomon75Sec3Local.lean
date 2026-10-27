module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Gold

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.Goldschmidt

open scoped commutatorElement

section Lemma35

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_map_sylow_of_isPGroup_normalizer {Z N : Subgroup X} (hZ : IsPGroup 2 ↥Z)
    (hN : N = normalizer (Z : Set X)) (S : Sylow 2 ↥N) :
    Z ≤ (S : Subgroup ↥N).map N.subtype := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZN : Z ≤ N := hN ▸ Subgroup.le_normalizer
  have hnorm : (Z.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).2 hN.le
  have hp : IsPGroup 2 ↥(Z.subgroupOf N) := hZ.of_equiv (Subgroup.subgroupOfEquivOfLe hZN).symm
  have h1 : Z.subgroupOf N ≤ (S : Subgroup ↥N) := hp.le_sylow_of_normal S
  intro z hz
  exact ⟨⟨z, hZN hz⟩, h1 (show (⟨z, hZN hz⟩ : ↥N) ∈ Z.subgroupOf N from hz), rfl⟩

end Lemma35

section Sec5Basic

variable {X : Type} [Group X] {n : ℕ} {z : X} {Z : Subgroup X}

theorem IsSec5Pair.ne_bot (h : IsSec5Pair X n z Z) : Z ≠ ⊥ := by
  intro hZ
  have hz1 : z = 1 := by
    have := h.mem
    rw [hZ] at this
    exact Subgroup.mem_bot.1 this
  have := h.orderOf_z
  rw [hz1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem IsSec5Pair.isPGroup (h : IsSec5Pair X n z Z) : IsPGroup 2 ↥Z := h.sylow.2.1

theorem IsSec5Pair.exists_isAhatIntr (h : IsSec5Pair X n z Z) :
    ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ IsAhatIntr X t L := by
  have hW : K0 X n (centralizer ({z} : Set X)) ≠ ⊥ := by
    intro hW
    have hz := (h.sylow.1 h.mem).1
    rw [hW] at hz
    have hz1 : z = 1 := Subgroup.mem_bot.1 hz
    have := h.orderOf_z
    rw [hz1, orderOf_one] at this
    exact absurd this (by norm_num)
  unfold K0 at hW
  obtain ⟨L, ⟨⟨u, hu⟩, -⟩, -⟩ : ∃ L ∈ {L : Subgroup X | (∃ u : X,
      IsIntrinsicIn X (centralizer ({z} : Set X)) L u) ∧
      IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) n}, L ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hW (sSup_eq_bot.2 hcon)
  obtain ⟨Lu, hLu, -⟩ := hu.2.2.2.2
  exact ⟨u, Lu, hu.1, hLu⟩

end Sec5Basic

section Sec5

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}

theorem eq_one_of_mem_pPrimeCoreOf_of_isPGroup {W P : Subgroup X} {x : X}
    (hx : x ∈ pPrimeCoreOf 2 W) (hP : IsPGroup 2 ↥P) (hxP : x ∈ P) : x = 1 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw, rfl⟩ := hx
  have hxP' : (w : X) ∈ P := hxP
  have hOdd : Odd (Nat.card (pPrimeCore 2 ↥W)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have h2 : Odd (orderOf w) := Odd.of_dvd_nat hOdd (Subgroup.orderOf_dvd_natCard _ hw)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨(w : X), hxP'⟩
  have h1 : orderOf (w : X) = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have h3 : orderOf (w : X) = orderOf w := Subgroup.orderOf_coe w
  have hk0 : k = 0 := by
    by_contra hk0
    refine (Nat.not_even_iff_odd.2 h2) ?_
    rw [← h3, h1]
    exact Nat.even_pow.2 ⟨even_two, hk0⟩
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
  exact h1

theorem IsSec5Pair.isMulCommutative (h : IsSec5Pair X n z Z) : IsMulCommutative Z := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha := h.sylow.1 a.2
  have hb := h.sylow.1 b.2
  have h1 : ⁅(b : X), (a : X)⁆ ∈ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) :=
    ha.2.2.2 b (hb.1)
  have h2 : ⁅(b : X), (a : X)⁆ ∈ Z := by
    rw [commutatorElement_def]
    exact Z.mul_mem (Z.mul_mem (Z.mul_mem b.2 a.2) (Z.inv_mem b.2)) (Z.inv_mem a.2)
  have h3 := eq_one_of_mem_pPrimeCoreOf_of_isPGroup h1 h.isPGroup h2
  have h4 : (b : X) * (a : X) = (a : X) * (b : X) := commutatorElement_eq_one_iff_mul_comm.1 h3
  exact h4.symm

end Sec5

section Lemma36

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X]

theorem lemma36 (hGold : CoreStatement) (hInv : AhatNoncommutingInvolutions)
    (hnonab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} {z : X} {Z : Subgroup X}
    (h : IsSec5Pair X n z Z) (S : Sylow 2 X) (hZS : Z ≤ (S : Subgroup X)) :
    ¬ CFSG.Open.fusionStronglyClosed (Z : Set X) (S : Subgroup X) := by
  intro hclosed
  obtain ⟨t, L, ht, hL⟩ := h.exists_isAhatIntr
  exact false_of_isAhatIntr_of_fusionStronglyClosed hGold hInv hnonab hL S hZS
    h.isMulCommutative h.ne_bot hclosed

theorem lemma36_set (hGold : CoreStatement) (hInv : AhatNoncommutingInvolutions)
    (hnonab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} {z : X} {Z : Subgroup X}
    (h : IsSec5Pair X n z Z) (S : Sylow 2 X) (hZS : Z ≤ (S : Subgroup X)) :
    {x : X | x ∈ (S : Subgroup X) ∧ ∃ g : X, g⁻¹ * x * g ∈ Z} ≠ (Z : Set X) := by
  intro heq
  refine lemma36 hGold hInv hnonab h S hZS ?_
  intro a ha g hg
  have hmem : g⁻¹ * a * g ∈ {x : X | x ∈ (S : Subgroup X) ∧ ∃ g : X, g⁻¹ * x * g ∈ Z} :=
    ⟨hg, g⁻¹, by
      have : g⁻¹⁻¹ * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [this]
      exact ha⟩
  rw [heq] at hmem
  exact hmem

end Lemma36

end CFSG.OddStandard.Solomon75
