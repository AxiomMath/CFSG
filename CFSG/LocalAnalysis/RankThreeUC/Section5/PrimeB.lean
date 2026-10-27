module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.HyperplaneOrbitStructure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeB

open CFSG.LocalAnalysis.RankThreeUC.Section5

theorem prime_order {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1)) :
    Nat.card B = 2 ^ e - 1 ∧ Nat.Prime (Nat.card B) ∧ Odd e ∧
      B ≤ Subgroup.normalizer (T : Set G) := by
  have h51 := hc.oddPrimeClassTwoAction
  obtain ⟨hq, hodd⟩ := CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimePower.prime_and_odd e h51.two_lt hr
  set q := 2 ^ e - 1 with hqdef
  have hcyc : IsCyclic B := (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).2.2.1
  have hqpi : q ∈ piOf B := by
    rw [h51.pi_eq]; exact ⟨hq, dvd_rfl⟩
  have hdvd : q ∣ Nat.card B := hqpi.2
  have hpow : ∀ {d : ℕ}, Nat.Prime d → d ∣ Nat.card B → d = q := by
    intro d hd hdB
    have : d ∈ piOf B := ⟨hd, hdB⟩
    rw [h51.pi_eq] at this
    exact (Nat.prime_dvd_prime_iff_eq hd hq).1 this.2
  have hcard : Nat.card B = q := by
    have hn := Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hpow
    have hpg : IsPGroup q B := IsPGroup.of_card hn
    have hnorm : (⊤ : Subgroup B).Normal := inferInstance
    have hpg' : IsPGroup q (⊤ : Subgroup B) := by
      intro x
      obtain ⟨k, hk⟩ := hpg x.1
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hmem : ∀ x : B, x ∈ CFSG.Open.pCore q B := by
      intro x
      have : (⊤ : Subgroup B) ≤ CFSG.Open.pCore q B :=
        le_sSup ⟨hnorm, hpg'⟩
      exact this trivial
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hpe : g ^ q = 1 := by
      have hgm : (g : G) ∈ CFSG.Open.pCoreOf q B := ⟨g, hmem g, rfl⟩
      have := Monoid.pow_exponent_eq_one (⟨(g : G), hgm⟩ : CFSG.Open.pCoreOf q B)
      rw [h51.exponent_Or q hqpi] at this
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    have h1 : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one hpe
    have h2 : orderOf g = Nat.card B := orderOf_eq_card_of_forall_mem_zpowers hg
    exact Nat.dvd_antisymm (h2 ▸ h1) hdvd
  exact ⟨hcard, hcard ▸ hq, hodd, h51.normalizes hodd⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeB
