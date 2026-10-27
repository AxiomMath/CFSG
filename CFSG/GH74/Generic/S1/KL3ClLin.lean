module

public import CFSG.GH74.Generic.S1.KL3Cfg
public import CFSG.GH74.Generic.S1.KL3ClStated
public import CFSG.GH74.Generic.S1.KL3ClBlock

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1

theorem kl3cl_two_ne_zero {K : Type} [Field K] {p : ℕ} (hp : p.Prime) [CharP K p] (hp2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  intro h
  have h3 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

theorem kl3cl_false_of_block (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {n : ℕ} {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (hn : n = 5 ∨ (n = 4 ∧ 4 ≤ Nat.card K)) {S : Type} [Group S]
    (e : S ≃* StatedProj (StatedSL n K)) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    {Pb : Subgroup S} (eSL : ↥Pb ≃* SL(3, F)) {yb : S} (hyb : yb ∈ Pb) (hyb2 : orderOf yb = 2)
    (hsolv : Group.IsSolvable ↥(centralizer ({yb} : Set S))) : False := by
  obtain ⟨ρ, y, hρinj, hρH, -, hysq, hns, htr⟩ := kl3cl_rep_of_stated hGA e hF eSL hyb hyb2 hsolv
  obtain ⟨Q, hQperf, hQne, hQdet, hQcomm, hQscal⟩ :=
    kl3cl_exists_perfect_block h2 (by simpa using hn) y hysq hns
  have hQH : Q ≤ StatedSL n K := fun g hg => Subgroup.subset_closure (hQdet g hg)
  exact hQne (htr Q hQH hQcomm hQperf hQscal)

theorem kl3FamL5 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL3FamL5 := by
  intro S _ _ _ p f hp hf hmod4 hmodel F _ _ Pb yb hcfg
  obtain ⟨hF, ⟨eSL⟩, hyb, hyb2, hsolv⟩ := hcfg
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [pow_succ] at hmod4
    omega
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (p := p) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  exact kl3cl_false_of_block hGA (kl3cl_two_ne_zero hp hp2) (Or.inl rfl) e hF eSL hyb hyb2 hsolv

theorem kl3FamL4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL3FamL4 := by
  intro S _ _ _ p f hp hp2 hf _ hmodel F _ _ Pb yb hcfg
  obtain ⟨hF, ⟨eSL⟩, hyb, hyb2, hsolv⟩ := hcfg
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (p := p) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  by_cases h3 : p ^ f = 3
  · have hp3 : p = 3 := by
      have hdvd : p ∣ 3 := h3 ▸ dvd_pow_self p (by omega : f ≠ 0)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
    subst hp3
    refine ⟨rfl, ?_⟩
    exact Nat.pow_right_injective (a := 3) (by norm_num) (show 3 ^ f = 3 ^ 1 by simpa using h3)
  · exfalso
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have h4 : 4 ≤ Nat.card K := by rw [hK]; omega
    exact kl3cl_false_of_block hGA (kl3cl_two_ne_zero hp hp2) (Or.inr ⟨rfl, h4⟩) e hF eSL hyb hyb2
      hsolv

end CFSG.GH74.Generic.S1
