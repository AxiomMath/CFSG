module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltYCore
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltY

open Equiv Equiv.Perm Subgroup

theorem card_centralizer_cycleType_three {g : Perm (Fin 9)}
    (hg : g.cycleType = Multiset.replicate 3 3) :
    Nat.card ↥(centralizer ({g} : Set (Perm (Fin 9)))) = 162 := by
  rw [Equiv.Perm.nat_card_centralizer, hg]
  have h : (Multiset.replicate 3 3 : Multiset ℕ) = {3, 3, 3} := rfl
  rw [h]
  have h1 : ({3, 3, 3} : Multiset ℕ).sum = 9 := by decide
  have h2 : ({3, 3, 3} : Multiset ℕ).prod = 27 := by decide
  have h3 : ({3, 3, 3} : Multiset ℕ).toFinset = {3} := by decide
  have h4 : Multiset.count 3 ({3, 3, 3} : Multiset ℕ) = 3 := by decide
  rw [Fintype.card_fin, h1, h2, h3, Finset.prod_singleton, h4]
  decide

theorem nine_trivial {P W : Subgroup (Perm (Fin 9))} (hPA : P ≤ alternatingGroup (Fin 9))
    (hPc : Nat.card P = 2 ^ 6) (hW : IsPGroup 3 ↥W)
    (hN : P ≤ normalizer (W : Set (Perm (Fin 9)))) : W = ⊥ := by
  classical
  have hbad : ∀ k < 9, 1 ≤ k → k % 3 = 0 → ¬ (2 * 2 ^ 6 ∣ k.factorial * (9 - k).factorial) := by
    decide
  have S : ∀ V : Subgroup (Perm (Fin 9)), IsPGroup 3 ↥V →
      P ≤ normalizer (V : Set (Perm (Fin 9))) → V = ⊥ ∨ (movedSet V).card = 9 := by
    intro V hV hNV
    rcases moved_card_dichotomy hPA hPc hbad hV hNV with h | h
    · exact Or.inl (movedSet_eq_empty_iff.1 h)
    · exact Or.inr h
  by_contra hW0
  have hP2 : IsPGroup 2 ↥P := IsPGroup.of_card (n := 6) hPc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := IsPGroup.card_modEq_card_fixedPoints hP2 (Fin 9)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin 9, ∀ p ∈ P, p x₀ = x₀ := by
    by_contra hne
    push Not at hne
    have hemp : MulAction.fixedPoints ↥P (Fin 9) = ∅ := by
      ext x
      simp only [MulAction.mem_fixedPoints, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨p, hp, hpx⟩ := hne x
      exact ⟨⟨p, hp⟩, hpx⟩
    rw [hemp, Nat.card_fin] at hmod
    simp [Nat.ModEq] at hmod
  set W₁ : Subgroup (Perm (Fin 9)) := W ⊓ MulAction.stabilizer (Perm (Fin 9)) x₀ with hW₁def
  have hmemW₁ : ∀ h, h ∈ W₁ ↔ h ∈ W ∧ h x₀ = x₀ := fun h => by
    simp [hW₁def, MulAction.mem_stabilizer_iff]
  have hW₁N : P ≤ normalizer (W₁ : Set (Perm (Fin 9))) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hpx : p x₀ = x₀ := hx₀ p hp
    have hpix : p⁻¹ x₀ = x₀ := by rw [Perm.inv_eq_iff_eq]; exact hpx.symm
    rw [hmemW₁, hmemW₁, (Subgroup.mem_normalizer_iff.1 (hN hp) h)]
    have h1 : (p * h * p⁻¹) x₀ = p (h x₀) := by simp [Perm.mul_apply, hpix]
    rw [h1]
    constructor
    · rintro ⟨h2, h3⟩
      exact ⟨h2, by rw [h3]; exact hpx⟩
    · rintro ⟨h2, h3⟩
      exact ⟨h2, p.injective (h3.trans hpx.symm)⟩
  have hW₁ : W₁ = ⊥ := by
    rcases S W₁ (hW.to_le inf_le_left) hW₁N with h | h
    · exact h
    · exfalso
      have huniv : movedSet W₁ = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using h)
      have hx : x₀ ∈ movedSet W₁ := by rw [huniv]; exact Finset.mem_univ _
      obtain ⟨w, hw, hwx⟩ := mem_movedSet.1 hx
      exact hwx ((hmemW₁ w).1 hw).2
  have : Fintype ↥W := Fintype.ofFinite _
  let O : Finset (Fin 9) := Finset.univ.image (fun w : ↥W => (w : Perm (Fin 9)) x₀)
  have hmemO : ∀ y, y ∈ O ↔ ∃ w ∈ W, w x₀ = y := fun y => by
    simp [O]
  have hinj : Function.Injective (fun w : ↥W => (w : Perm (Fin 9)) x₀) := by
    intro a b hab
    have h1 : ((a : Perm (Fin 9))⁻¹ * (b : Perm (Fin 9))) ∈ W₁ := by
      rw [hmemW₁]
      refine ⟨W.mul_mem (W.inv_mem a.2) b.2, ?_⟩
      have hab' : (b : Perm (Fin 9)) x₀ = (a : Perm (Fin 9)) x₀ := hab.symm
      simp [Perm.mul_apply, hab']
    rw [hW₁, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact Subtype.ext h1
  have hOcard : O.card = Nat.card W := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  have hOinv : ∀ p ∈ P, ∀ y, p y ∈ O ↔ y ∈ O := by
    have fwd : ∀ p ∈ P, ∀ y, y ∈ O → p y ∈ O := by
      intro p hp y hy
      obtain ⟨w, hw, rfl⟩ := (hmemO y).1 hy
      refine (hmemO _).2 ⟨p * w * p⁻¹, (Subgroup.mem_normalizer_iff.1 (hN hp) w).1 hw, ?_⟩
      have hpix : p⁻¹ x₀ = x₀ := by rw [Perm.inv_eq_iff_eq]; exact (hx₀ p hp).symm
      simp [Perm.mul_apply, hpix]
    intro p hp y
    refine ⟨fun h => ?_, fwd p hp y⟩
    simpa using fwd p⁻¹ (P.inv_mem hp) (p y) h
  have hWcard : Nat.card W = 9 := by
    obtain ⟨k, hk⟩ := hW.exists_card_eq
    have hle : Nat.card W ≤ 9 := by
      rw [← hOcard]
      simpa using Finset.card_le_univ O
    have hgt : 1 < Nat.card W := (Subgroup.one_lt_card_iff_ne_bot W).2 hW0
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have h3 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases k
    · omega
    · exfalso
      have h3 : O.card = 3 := by rw [hOcard, hk]; norm_num
      have hd := two_mul_card_dvd O (Or.inl (by omega)) P hPA hOinv
      rw [hPc, h3] at hd
      revert hd
      decide
    · rw [hk]; norm_num
  have hOuniv : O = Finset.univ := Finset.eq_univ_of_card O (by rw [hOcard, hWcard]; simp)
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 3 (by rw [hWcard]; norm_num)
  set g : Perm (Fin 9) := (w₀ : Perm (Fin 9)) with hgdef
  have hgW : g ∈ W := w₀.2
  have hgord : orderOf g = 3 := by rw [hgdef, Subgroup.orderOf_coe, hw₀]
  have hgfree : ∀ x, g x ≠ x := by
    intro x hgx
    have hx : x ∈ O := by rw [hOuniv]; exact Finset.mem_univ x
    obtain ⟨v, hv, rfl⟩ := (hmemO x).1 hx
    have h1 : v⁻¹ * g * v ∈ W₁ := by
      rw [hmemW₁]
      refine ⟨W.mul_mem (W.mul_mem (W.inv_mem hv) hgW) hv, ?_⟩
      simp [Perm.mul_apply, hgx]
    rw [hW₁, Subgroup.mem_bot] at h1
    have h2 : g = 1 := by
      have := congrArg (fun t => v * t * v⁻¹) h1
      simpa [mul_assoc] using this
    rw [h2, orderOf_one] at hgord
    omega
  have hsupp : g.support.card = 9 := by
    have : g.support = Finset.univ := by
      ext x
      simp [Perm.mem_support, hgfree x]
    rw [this]
    simp
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [hgord]; exact Nat.prime_three)
  have hsum := Equiv.Perm.sum_cycleType g
  rw [hm, hgord, hsupp, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hm2 : m = 2 := by omega
  have hcyc : g.cycleType = Multiset.replicate 3 3 := by rw [hm, hgord, hm2]
  have hcent := card_centralizer_cycleType_three hcyc
  set y₀ : Fin 9 := g x₀ with hy₀def
  have hy₀ : y₀ ≠ x₀ := hgfree x₀
  set S₁ : Subgroup ↥P := MulAction.stabilizer ↥P y₀ with hS₁def
  have hidx : S₁.index ≤ 8 := by
    rw [hS₁def, MulAction.index_stabilizer]
    have hsub : MulAction.orbit ↥P y₀ ⊆
        ((Finset.univ.erase x₀ : Finset (Fin 9)) : Set (Fin 9)) := by
      rintro _ ⟨p, rfl⟩
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and]
      intro h
      apply hy₀
      have h1 : (p : Perm (Fin 9)) y₀ = (p : Perm (Fin 9)) x₀ := by rw [hx₀ p p.2]; exact h
      exact (p : Perm (Fin 9)).injective h1
    calc (MulAction.orbit ↥P y₀).ncard
        ≤ ((Finset.univ.erase x₀ : Finset (Fin 9)) : Set (Fin 9)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = 8 := by
          rw [Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _)]
          simp
  have hcentS : ∀ p : ↥P, p ∈ S₁ → (p : Perm (Fin 9)) ∈ centralizer ({g} : Set (Perm (Fin 9))) := by
    intro p hp
    rw [hS₁def, MulAction.mem_stabilizer_iff] at hp
    have hpy : (p : Perm (Fin 9)) y₀ = y₀ := hp
    have hpx : (p : Perm (Fin 9)) x₀ = x₀ := hx₀ p p.2
    have hpix : (p : Perm (Fin 9))⁻¹ x₀ = x₀ := by rw [Perm.inv_eq_iff_eq]; exact hpx.symm
    have hg'W : (p : Perm (Fin 9)) * g * (p : Perm (Fin 9))⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hN p.2) g).1 hgW
    have hg'x : ((p : Perm (Fin 9)) * g * (p : Perm (Fin 9))⁻¹) x₀ = y₀ := by
      simp only [Perm.mul_apply, hpix]
      exact hpy
    have h1 : g⁻¹ * ((p : Perm (Fin 9)) * g * (p : Perm (Fin 9))⁻¹) ∈ W₁ := by
      rw [hmemW₁]
      refine ⟨W.mul_mem (W.inv_mem hgW) hg'W, ?_⟩
      simp [Perm.mul_apply, hg'x, hy₀def]
    rw [hW₁, Subgroup.mem_bot, inv_mul_eq_one] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : (p : Perm (Fin 9)) * g * (p : Perm (Fin 9))⁻¹ = g := h1.symm
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hdvd1 : Nat.card S₁ ∣ 162 := by
    have hle : S₁.map P.subtype ≤ centralizer ({g} : Set (Perm (Fin 9))) := by
      rintro _ ⟨p, hp, rfl⟩
      exact hcentS p hp
    have := Subgroup.card_dvd_of_le hle
    rwa [hcent, Subgroup.card_map_of_injective P.subtype_injective] at this
  have hdvd2 : Nat.card S₁ ∣ 64 := by
    have := Subgroup.card_subgroup_dvd_card S₁
    rwa [hPc] at this
  have hdvd3 : Nat.card S₁ ∣ 2 := by
    have h162 : Nat.gcd 162 64 = 2 := by norm_num
    have := Nat.dvd_gcd hdvd1 hdvd2
    rwa [h162] at this
  have hprod : S₁.index * Nat.card S₁ = 64 := by
    rw [Subgroup.index_mul_card, hPc]
    norm_num
  have hle2 : Nat.card S₁ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd3
  have := Nat.mul_le_mul hidx hle2
  omega



theorem three_group_trivial_alt {n e : ℕ}
    (hne : (n = 5 ∧ e = 2) ∨ (n = 8 ∧ e = 6) ∨ (n = 9 ∧ e = 6) ∨ (n = 10 ∧ e = 7))
    {P W : Subgroup (Perm (Fin n))} (hPA : P ≤ alternatingGroup (Fin n))
    (hPc : Nat.card P = 2 ^ e) (hW : IsPGroup 3 ↥W)
    (hN : P ≤ normalizer (W : Set (Perm (Fin n)))) : W = ⊥ := by
  rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact three_group_trivial (Or.inl ⟨rfl, rfl⟩) hPA hPc hW hN
  · exact three_group_trivial (Or.inr (Or.inl ⟨rfl, rfl⟩)) hPA hPc hW hN
  · exact nine_trivial hPA hPc hW hN
  · exact three_group_trivial (Or.inr (Or.inr ⟨rfl, rfl⟩)) hPA hPc hW hN

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltY
