module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHSplit
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH

open Subgroup

variable {V : Type*} [CommGroup V]

theorem card_minusPart_top_conj {s t g : MulAut V} (hgt : g * s * g⁻¹ = t) :
    Nat.card (minusPart t (⊤ : Subgroup V)) = Nat.card (minusPart s (⊤ : Subgroup V)) := by
  have hs : s = g⁻¹ * t * g := by rw [← hgt]; simp [mul_assoc]
  have h1 : ∀ x ∈ minusPart t (⊤ : Subgroup V), g⁻¹ x ∈ minusPart s (⊤ : Subgroup V) := by
    rintro x ⟨-, hx⟩
    refine ⟨mem_top _, ?_⟩
    rw [hs, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hx, map_inv]
  have h2 : ∀ y ∈ minusPart s (⊤ : Subgroup V), g y ∈ minusPart t (⊤ : Subgroup V) := by
    rintro y ⟨-, hy⟩
    refine ⟨mem_top _, ?_⟩
    rw [← hgt, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy, map_inv]
  exact Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ x, h1 x x.2⟩
      invFun := fun y => ⟨g y, h2 y y.2⟩
      left_inv := fun x => Subtype.ext (MulAut.apply_inv_self V g x)
      right_inv := fun y => Subtype.ext (MulAut.inv_apply_self V g y) }

theorem minusPart_eq_self_of_inv {t : MulAut V} {U : Subgroup V} (ht : ∀ u ∈ U, t u = u⁻¹) :
    minusPart t U = U :=
  Subgroup.ext fun u => ⟨fun hu => hu.1, fun hu => ⟨hu, ht u hu⟩⟩

namespace Setup

variable {p : ℕ} {S : Subgroup (MulAut V)} (h : Setup p S)
include h

theorem minusPart_eq_bot_of_fix {t : MulAut V} {U : Subgroup V} (ht : ∀ u ∈ U, t u = u) :
    minusPart t U = ⊥ := by
  ext u
  simp only [mem_minusPart, Subgroup.mem_bot]
  constructor
  · rintro ⟨hu, htu⟩
    rw [ht u hu] at htu
    exact h.eq_one_of_eq_inv htu
  · rintro rfl
    exact ⟨U.one_mem, by simp⟩

theorem weight_base [Finite V] [Fintype S] (hS8 : Fintype.card S = 8) {U : Subgroup V}
    (hpm : ∀ t ∈ S, (∀ u ∈ U, t u = u) ∨ ∀ u ∈ U, t u = u⁻¹) :
    (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) * Nat.card (fixPart S U) ^ 4 =
      Nat.card U ^ 4 := by
  by_cases hall : ∀ t ∈ S, ∀ u ∈ U, t u = u
  · have h1 : ∀ t : S, minusPart (t : MulAut V) U = ⊥ := fun t =>
      h.minusPart_eq_bot_of_fix (hall t t.2)
    have h2 : fixPart S U = U :=
      le_antisymm (fixPart_le S U) fun u hu => ⟨hu, fun t ht => hall t ht u hu⟩
    simp [h1, h2]
  · push Not at hall
    obtain ⟨t₀, ht₀, u₀, hu₀, hne⟩ := hall
    have hneg : ∀ u ∈ U, t₀ u = u⁻¹ := (hpm t₀ ht₀).resolve_left fun h' => hne (h' u₀ hu₀)
    have hfix : fixPart S U = ⊥ := by
      ext u
      simp only [mem_fixPart, Subgroup.mem_bot]
      constructor
      · rintro ⟨hu, hf⟩
        have := hf t₀ ht₀
        rw [hneg u hu] at this
        exact h.eq_one_of_eq_inv this.symm
      · rintro rfl
        exact ⟨U.one_mem, fun t _ => map_one t⟩
    let T₀ : S := ⟨t₀, ht₀⟩
    have hpair : ∀ t : S, Nat.card (minusPart (t : MulAut V) U) *
        Nat.card (minusPart ((T₀ * t : S) : MulAut V) U) = Nat.card U := by
      intro t
      by_cases hpos : ∀ u ∈ U, (t : MulAut V) u = u
      · have e1 : minusPart (t : MulAut V) U = ⊥ := h.minusPart_eq_bot_of_fix hpos
        have e2 : minusPart ((T₀ * t : S) : MulAut V) U = U := by
          refine minusPart_eq_self_of_inv fun u hu => ?_
          show t₀ ((t : MulAut V) u) = u⁻¹
          rw [hpos u hu, hneg u hu]
        rw [e1, e2, Subgroup.card_bot, one_mul]
      · have hneg' : ∀ u ∈ U, (t : MulAut V) u = u⁻¹ := (hpm t t.2).resolve_left hpos
        have e1 : minusPart (t : MulAut V) U = U := minusPart_eq_self_of_inv hneg'
        have e2 : minusPart ((T₀ * t : S) : MulAut V) U = ⊥ := by
          refine h.minusPart_eq_bot_of_fix fun u hu => ?_
          show t₀ ((t : MulAut V) u) = u
          rw [hneg' u hu, map_inv, hneg u hu, inv_inv]
        rw [e1, e2, Subgroup.card_bot, mul_one]
    have hshift : ∏ t : S, Nat.card (minusPart ((T₀ * t : S) : MulAut V) U) =
        ∏ t : S, Nat.card (minusPart (t : MulAut V) U) :=
      Fintype.prod_equiv (Equiv.mulLeft T₀) _ _ fun _ => rfl
    have hsq : (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) ^ 2 =
        (Nat.card U ^ 4) ^ 2 := by
      calc (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) ^ 2
          = (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) *
            ∏ t : S, Nat.card (minusPart ((T₀ * t : S) : MulAut V) U) := by rw [hshift, sq]
        _ = ∏ t : S, (Nat.card (minusPart (t : MulAut V) U) *
            Nat.card (minusPart ((T₀ * t : S) : MulAut V) U)) := Finset.prod_mul_distrib.symm
        _ = ∏ _t : S, Nat.card U := Finset.prod_congr rfl fun t _ => hpair t
        _ = Nat.card U ^ 8 := by rw [Finset.prod_const, Finset.card_univ, hS8]
        _ = (Nat.card U ^ 4) ^ 2 := by rw [← pow_mul]
    have hprod : ∏ t : S, Nat.card (minusPart (t : MulAut V) U) = Nat.card U ^ 4 :=
      Nat.pow_left_injective two_ne_zero hsq
    rw [hprod, hfix, Subgroup.card_bot, one_pow, mul_one]

theorem weight_step [Finite V] [Fintype S] {U : Subgroup V} (hU : IsInvariant S U) {s : MulAut V}
    (hs : s ∈ S)
    (hA : (∏ t : S, Nat.card (minusPart (t : MulAut V) (plusPart s U))) *
        Nat.card (fixPart S (plusPart s U)) ^ 4 = Nat.card (plusPart s U) ^ 4)
    (hB : (∏ t : S, Nat.card (minusPart (t : MulAut V) (minusPart s U))) *
        Nat.card (fixPart S (minusPart s U)) ^ 4 = Nat.card (minusPart s U) ^ 4) :
    (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) * Nat.card (fixPart S U) ^ 4 =
      Nat.card U ^ 4 := by
  have hsU : ∀ u ∈ U, s u ∈ U := hU s hs
  have hmin : ∀ t : S, Nat.card (minusPart (t : MulAut V) U) =
      Nat.card (minusPart (t : MulAut V) (plusPart s U)) *
        Nat.card (minusPart (t : MulAut V) (minusPart s U)) := by
    intro t
    have := h.card_eq_mul hs ((h.isInvariant_minusPart t.2 hU) s hs)
    rwa [plusPart_minusPart, minusPart_minusPart] at this
  have hfix : Nat.card (fixPart S U) =
      Nat.card (fixPart S (plusPart s U)) * Nat.card (fixPart S (minusPart s U)) := by
    have := h.card_eq_mul hs ((h.isInvariant_fixPart hU) s hs)
    rwa [plusPart_fixPart, minusPart_fixPart] at this
  have hcardU := h.card_eq_mul hs hsU
  calc (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) * Nat.card (fixPart S U) ^ 4
      = (∏ t : S, (Nat.card (minusPart (t : MulAut V) (plusPart s U)) *
          Nat.card (minusPart (t : MulAut V) (minusPart s U)))) *
        (Nat.card (fixPart S (plusPart s U)) * Nat.card (fixPart S (minusPart s U))) ^ 4 := by
        rw [hfix, Finset.prod_congr rfl fun t _ => hmin t]
    _ = ((∏ t : S, Nat.card (minusPart (t : MulAut V) (plusPart s U))) *
          Nat.card (fixPart S (plusPart s U)) ^ 4) *
        ((∏ t : S, Nat.card (minusPart (t : MulAut V) (minusPart s U))) *
          Nat.card (fixPart S (minusPart s U)) ^ 4) := by
        rw [Finset.prod_mul_distrib, mul_pow]
        exact mul_mul_mul_comm _ _ _ _
    _ = Nat.card (plusPart s U) ^ 4 * Nat.card (minusPart s U) ^ 4 := by rw [hA, hB]
    _ = Nat.card U ^ 4 := by rw [hcardU, mul_pow]

theorem weight_eq [Finite V] [Fintype S] (hS8 : Fintype.card S = 8) :
    ∀ U, IsInvariant S U →
      (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) * Nat.card (fixPart S U) ^ 4 =
        Nat.card U ^ 4 :=
  h.induction
    (P := fun U => (∏ t : S, Nat.card (minusPart (t : MulAut V) U)) *
      Nat.card (fixPart S U) ^ 4 = Nat.card U ^ 4)
    (fun _ _ hpm => h.weight_base hS8 hpm)
    (fun _ hU _ hs _ _ hA hB => h.weight_step hU hs hA hB)

end Setup

theorem seven_le_of_elemAb_eight {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ p = 1) (hcard : Nat.card V = p ^ r)
    (S : Subgroup (MulAut V)) (hS : ∀ s ∈ S, s * s = 1)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) (h8 : Nat.card S = 8)
    (hconj : ∀ s ∈ S, ∀ t ∈ S, s ≠ 1 → t ≠ 1 → ∃ g : MulAut V, g * s * g⁻¹ = t) : 7 ≤ r := by
  classical
  have h : Setup p S := ⟨Fact.out, hp2, hV, hS, hcomm⟩
  have : Finite S := Nat.finite_of_card_ne_zero (by omega)
  let _ : Fintype S := Fintype.ofFinite S
  have hS8 : Fintype.card S = 8 := by rw [← Nat.card_eq_fintype_card]; exact h8
  have hQ := h.weight_eq hS8 ⊤ (fun _ _ _ _ => mem_top _)
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : S, T₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).2 fun x hx => by
      simpa using hcon ⟨x, hx⟩
    have := (Subgroup.eq_bot_iff_card S).1 hbot
    omega
  have hne1 : ∀ t : S, t ≠ 1 → (t : MulAut V) ≠ 1 := fun t ht h' => ht (Subtype.ext h')
  have hprod : ∏ t : S, Nat.card (minusPart (t : MulAut V) (⊤ : Subgroup V)) =
      Nat.card (minusPart (T₀ : MulAut V) (⊤ : Subgroup V)) ^ 7 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : S))]
    have h1 : minusPart ((1 : S) : MulAut V) (⊤ : Subgroup V) = ⊥ :=
      h.minusPart_eq_bot_of_fix fun u _ => rfl
    have h2 : ∀ t ∈ Finset.univ.erase (1 : S),
        Nat.card (minusPart (t : MulAut V) (⊤ : Subgroup V)) =
          Nat.card (minusPart (T₀ : MulAut V) (⊤ : Subgroup V)) := by
      intro t ht
      obtain ⟨g, hg⟩ := hconj T₀ T₀.2 t t.2 (hne1 T₀ hT₀) (hne1 t (Finset.ne_of_mem_erase ht))
      exact card_minusPart_top_conj hg
    rw [Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hS8, h1, Subgroup.card_bot, one_mul]
  have hdvd1 : Nat.card (minusPart (T₀ : MulAut V) (⊤ : Subgroup V)) ∣ p ^ r := by
    rw [← hcard]; exact Subgroup.card_subgroup_dvd_card _
  have hdvd2 : Nat.card (fixPart S (⊤ : Subgroup V)) ∣ p ^ r := by
    rw [← hcard]; exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow h.prime).1 hdvd1
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow h.prime).1 hdvd2
  rw [hprod, ha, he, Subgroup.card_top, hcard] at hQ
  simp only [← pow_mul, ← pow_add] at hQ
  have hexp : a * 7 + e * 4 = r * 4 := Nat.pow_right_injective h.prime.two_le hQ
  have hr : e ≠ r := by
    rintro rfl
    have htop : fixPart S (⊤ : Subgroup V) = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, he, hcard]
    refine hne1 T₀ hT₀ (MulEquiv.ext fun v => ?_)
    have hv : v ∈ fixPart S (⊤ : Subgroup V) := by rw [htop]; exact mem_top v
    exact hv.2 T₀ T₀.2
  omega

end CFSG.EvenSporadicStandard.M24Std.CResH
