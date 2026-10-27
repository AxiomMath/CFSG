module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Act

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement Pointwise

theorem y7a_pgroup_fixed {G : Type} [Group G] [Finite G] {C M V : Subgroup G}
    (hC : IsPGroup 2 C) (hM : IsPGroup 2 M) (hVM : V ≤ M)
    (hMV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V)
    (hCV : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hCM : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hne : ∃ m ∈ M, m ∉ V) :
    ∃ x ∈ M, x ∉ V ∧ ∀ c ∈ C, ⁅c, x⁆ ∈ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let n : ℕ := Nat.card ((M : Set G).image ((↑) : G → G ⧸ V))
  have hmul : (M : Set G) * (V : Set G) = (M : Set G) := by
    ext g
    constructor
    · intro hg
      obtain ⟨m, hm, v, hv, rfl⟩ := Set.mem_mul.mp hg
      exact M.mul_mem hm (hVM hv)
    · intro hg
      exact Set.mem_mul.mpr ⟨g, hg, 1, V.one_mem, mul_one g⟩
  have hcard : Nat.card ↥(M : Set G) = n * Nat.card ↥(V : Set G) := by
    have h := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient V (M : Set G)
    rw [hmul] at h
    exact h.trans (mul_comm _ _)
  have hUV : ∀ u ∈ (M : Set G), ∀ v ∈ V, u * v ∈ (M : Set G) := by
    intro u hu v hv
    exact M.mul_mem hu (hVM hv)
  have hMpos : 0 < Nat.card ↥(M : Set G) := by
    haveI : Nonempty ↥(M : Set G) := ⟨⟨1, M.one_mem⟩⟩
    exact Nat.card_pos
  have hn : 0 < n := by
    by_contra h
    have h0 : n = 0 := Nat.eq_zero_of_not_pos h
    rw [h0, zero_mul] at hcard
    exact (ne_of_gt hMpos) hcard
  have hVltM : Nat.card ↥V < Nat.card ↥M := by
    have hssub : (V : Set G) ⊂ (M : Set G) := by
      rw [Set.ssubset_iff_subset_ne]
      refine ⟨hVM, fun heq => ?_⟩
      obtain ⟨m, hmM, hmV⟩ := hne
      exact hmV (show m ∈ (V : Set G) from by rw [heq]; exact hmM)
    simpa using Set.Finite.card_lt_card (Set.toFinite (M : Set G)) hssub
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥M)).mp hM
  have hdiv : n ∣ 2 ^ a := ⟨Nat.card ↥V, by rw [← ha]; exact hcard⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      have hn1 : n = 1 := by rw [hk, hk0, pow_zero]
      rw [hn1, one_mul] at hcard
      exact (ne_of_gt hVltM) hcard
    · exact hkpos
  have h2dvdn : 2 ∣ n := by
    rw [hk]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos)
  obtain ⟨lab, hlab, hsurj⟩ :=
    y6_lab_exists (V := V) (U := (M : Set G)) (n := n) hn hUV hcard
  have hCVnorm : C ≤ normalizer (V : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact hCV c hc v hv
    · intro hv
      have h := hCV c⁻¹ (C.inv_mem hc) (c * v * c⁻¹) hv
      convert h using 1
      group
  obtain ⟨ψ, hψ, -⟩ :=
    y6_act_exists (X := C) (V := V) (U := (M : Set G)) (n := n) hCVnorm hCM lab hlab hsurj
  letI : MulAction ↥C (Fin n) := MulAction.compHom (Fin n) ψ
  have hfix1 : lab 1 ∈ MulAction.fixedPoints ↥C (Fin n) := by
    rw [MulAction.mem_fixedPoints]
    intro c
    have : ψ c (lab 1) = lab 1 := by
      rw [hψ c 1 M.one_mem]
      simp
    exact this
  obtain ⟨b, hb, hbne⟩ :=
    hC.exists_fixed_point_of_prime_dvd_card_of_fixed_point (p := 2) (α := Fin n)
      (by simpa using h2dvdn) hfix1
  obtain ⟨x, hxM, hxlab⟩ := hsurj b
  refine ⟨x, hxM, ?_, ?_⟩
  · intro hxV
    have h1 : x⁻¹ * 1 ∈ V := by simpa using V.inv_mem hxV
    have hcontra : lab 1 = b := by
      rw [← hxlab]
      exact ((hlab x hxM 1 M.one_mem).mpr h1).symm
    exact hbne hcontra
  · intro c hc
    have hfixc : ψ (⟨c, hc⟩ : ↥C) b = b := (MulAction.mem_fixedPoints.mp hb) ⟨c, hc⟩
    have hlab_eq : lab (c * x * c⁻¹) = lab x := by
      have h1 : ψ (⟨c, hc⟩ : ↥C) (lab x) = lab x := by
        have h := hfixc
        rw [← hxlab] at h
        exact h
      rw [hψ ⟨c, hc⟩ x hxM] at h1
      simpa using h1
    have hV : x⁻¹ * (c * x * c⁻¹) ∈ V :=
      (hlab x hxM (c * x * c⁻¹) (hCM c hc x hxM)).mp hlab_eq.symm
    have hcom : ⁅c, x⁆ = x * (x⁻¹ * (c * x * c⁻¹)) * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hcom]
    exact hMV x hxM _ hV

end CFSG.OddStandard.HigherRank.YamadaG23
