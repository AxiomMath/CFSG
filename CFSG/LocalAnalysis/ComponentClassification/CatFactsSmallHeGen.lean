module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open Subgroup

@[expose] def Good5 (C : Type*) [Group C] : Prop :=
  ∀ L : Subgroup C, L.IsSubnormal → 5 ∣ Nat.card L → 8 ∣ Nat.card L

variable {C X : Type*} [Group C] [Group X]

theorem good5_of_not_dvd [Finite C] (h : ¬ 5 ∣ Nat.card C) : Good5 C :=
  fun L _ h5 => absurd (h5.trans (card_subgroup_dvd_card L)) h

theorem good5_of_witness [Finite C] (h25 : ¬ 25 ∣ Nat.card C) (y₀ y₁ : C)
    (h₀ : orderOf y₀ = 5) (h₁ : orderOf y₁ = 5)
    (h8 : 8 ∣ Nat.card (closure ({y₀, y₁} : Set C))) : Good5 C := by
  intro L hL h5
  have h25' : ¬ 5 ^ 2 ∣ Nat.card C := by simpa using h25
  have hy₀ := mem_of_isSubnormal_of_orderOf_eq_prime Nat.prime_five h25' hL h5 h₀
  have hy₁ := mem_of_isSubnormal_of_orderOf_eq_prime Nat.prime_five h25' hL h5 h₁
  have hle : closure ({y₀, y₁} : Set C) ≤ L := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hy₀
    · exact hy₁
  exact h8.trans (card_dvd_of_le hle)

theorem good5_of_surjective [Finite C] (ρ : C →* X) (hρ : Function.Surjective ρ)
    (hker : Nat.card ρ.ker ∣ 2) (hX : Good5 X) : Good5 C := by
  intro L hL h5
  set f : L →* X := ρ.comp L.subtype
  have hrange : f.range = L.map ρ := by rw [MonoidHom.range_comp, range_subtype]
  have hcard : Nat.card L = Nat.card f.ker * Nat.card (L.map ρ) := by
    rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm,
      ← card_eq_card_quotient_mul_card_subgroup]
  have hkf : Nat.card f.ker ∣ 2 := by
    have hle : f.ker.map L.subtype ≤ ρ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [← card_map_of_injective L.subtype_injective]
    exact (card_dvd_of_le hle).trans hker
  have h5' : 5 ∣ Nat.card (L.map ρ) := by
    rw [hcard] at h5
    have hc : Nat.Coprime 5 (Nat.card f.ker) := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hkf with h | h <;> rw [h] <;> norm_num
    exact hc.dvd_of_dvd_mul_left h5
  exact (hX _ (hL.map hρ) h5').trans (card_map_dvd L ρ)

theorem good5_of_mulEquiv [Finite C] (e : C ≃* X) (hX : Good5 X) : Good5 C := by
  refine good5_of_surjective e.toMonoidHom e.surjective ?_ hX
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  rw [this, card_bot]
  exact one_dvd 2

theorem five_dvd_not_eight_of_oddBar {L : Type*} [Group L] [Finite L]
    (e : L ⧸ CFSG.pPrimeCore 2 L ≃* alternatingGroup (Fin 5)) :
    5 ∣ Nat.card L ∧ ¬ 8 ∣ Nat.card L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hq : Nat.card (L ⧸ CFSG.pPrimeCore 2 L) = 60 := by
    rw [Nat.card_congr e.toEquiv, hA]
  have hcard : Nat.card L = 60 * Nat.card (CFSG.pPrimeCore 2 L) := by
    rw [card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 L), hq]
  have hodd : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 L)) := CFSG.pPrimeCore_coprime_card
  refine ⟨hcard ▸ dvd_mul_of_dvd_left (by norm_num) _, fun h8 => ?_⟩
  rw [hcard] at h8
  have h8' : 4 * 2 ∣ 4 * (15 * Nat.card (CFSG.pPrimeCore 2 L)) := by
    have : 60 * Nat.card (CFSG.pPrimeCore 2 L) = 4 * (15 * Nat.card (CFSG.pPrimeCore 2 L)) := by
      ring
    rw [← this]
    simpa using h8
  have h2 : 2 ∣ 15 * Nat.card (CFSG.pPrimeCore 2 L) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h8'
  have h2' : 2 ∣ Nat.card (CFSG.pPrimeCore 2 L) :=
    (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 2 15) h2)
  have := Nat.Coprime.eq_one_of_dvd hodd h2'
  omega

end CFSG.ComponentClassification.CatFactsSmall
