module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Fit

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

abbrev Zr (r : ℕ) (M : Subgroup G) : Subgroup G := zOf (Ep r M)

omit [Finite G] in
theorem Zr_le_Ep (r : ℕ) (M : Subgroup G) : Zr r M ≤ Ep r M := inf_le_left

omit [Finite G] in
theorem Zr_le_Fm (r : ℕ) (M : Subgroup G) : Zr r M ≤ Fm M := (Zr_le_Ep r M).trans (Ep_le_Fm r M)

omit [Finite G] in
theorem Zr_le (r : ℕ) (M : Subgroup G) : Zr r M ≤ M := (Zr_le_Fm r M).trans (Fm_le M)

omit [Finite G] in
theorem Zr_comm (r : ℕ) (M : Subgroup G) : ∀ a ∈ Zr r M, ∀ b ∈ Zr r M, a * b = b * a := by
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm

theorem Zr_ne_bot (hC : Ctx6 G z k S M p) {r : ℕ} (hr : r.Prime) : Zr r M ≠ ⊥ := by
  obtain ⟨b, hb, hbr⟩ := exists_prime_ne_of_twoPrimes hC.twoPrimes r
  have hE0 : Ep r M ≠ ⊥ := Ep_ne_bot hr hb.1 hbr hb.2
  have hnil : Group.IsNilpotent ↥(Ep r M) := by
    have : Group.IsNilpotent ↥((Ep r M).subgroupOf (Fm M)) := by
      have := Fm_nilpotent M
      infer_instance
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (Ep_le_Fm r M))
  have hne : (⊤ : Subgroup ↥(Ep r M)) ≠ ⊥ := by
    have : Nontrivial ↥(Ep r M) := (Subgroup.nontrivial_iff_ne_bot _).mpr hE0
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Ep r M))
    intro h
    exact hx ((Subgroup.mem_bot).mp (h ▸ Subgroup.mem_top x))
  have hz := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥(Ep r M)) (H := ⊤) hne
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hz
  intro hbot
  apply ha
  have haE : ((a : ↥(Ep r M)) : G) ∈ Zr r M := by
    refine ⟨(a : ↥(Ep r M)).2, ?_⟩
    show ((a : ↥(Ep r M)) : G) ∈ centralizer ((Ep r M : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_center_iff.mp a.2.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at haE
  exact Subtype.ext (Subtype.ext haE)

omit [Finite G] in
theorem le_normalizer_Zr (r : ℕ) (M : Subgroup G) :
    M ≤ normalizer ((Zr r M : Subgroup G) : Set G) := le_normalizer_zOf (le_normalizer_Ep r M)

theorem normalizer_Zr (hC : Ctx6 G z k S M p) {r : ℕ} (hr : r.Prime) :
    normalizer ((Zr r M : Subgroup G) : Set G) = M :=
  normalizer_eq_of_normalized hC (Zr_ne_bot hC hr) (Zr_le r M) (le_normalizer_Zr r M)

theorem Fm_le_centralizer_Zr {r : ℕ} (hr : r.Prime) (M : Subgroup G) :
    Fm M ≤ centralizer ((Zr r M : Subgroup G) : Set G) := by
  refine Fm_le_of_forall fun q hq => ?_
  by_cases hqr : q = r
  · subst hqr
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commute_Op_Ep q hr M)).trans
      (Subgroup.centralizer_le (fun x hx => Zr_le_Ep q M hx))
  · have h1 : Op q M ≤ Ep r M := Op_le_Ep hq hr hqr M
    have h2 : Ep r M ≤ centralizer ((Zr r M : Subgroup G) : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp hw.2 e he).symm
    exact h1.trans h2

theorem Zr_odd (hC : Ctx6 G z k S M p) (r : ℕ) : Odd (Nat.card ↥(Zr r M)) :=
  Odd.of_dvd_nat (odd_card_Fm hC.hyp hC.mem) (Subgroup.card_dvd_of_le (Zr_le_Fm r M))

theorem Zr_coprime {r : ℕ} (hr : r.Prime) (M : Subgroup G) : Nat.Coprime (Nat.card ↥(Zr r M)) r := by
  have : Fact r.Prime := ⟨hr⟩
  have h1 : Nat.card ↥(Ep r M) = Nat.card ↥(pPrimeCore r ↥(Fm M)) :=
    Subgroup.card_map_of_injective (Fm M).subtype_injective
  have h2 : Nat.Coprime r (Nat.card ↥(Ep r M)) := by
    rw [h1]; exact pPrimeCore_coprime_card (p := r) (G := ↥(Fm M))
  exact (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le (Zr_le_Ep r M)) h2.symm)

end Fit

end CFSG.GH74.GLS.Stage2.Bender.Thm1
