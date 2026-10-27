module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
import all CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CoprimeStarSubgroupStructure
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeActionFixedFree
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.RstarCoprime

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

variable {G : Type} [Group G] [Finite G]

theorem Bstar_mono {P B A : Subgroup G} (hAB : A ≤ B) : Bstar P A ≤ Bstar P B :=
  Subgroup.map_mono (fun x hx => hAB hx)

theorem Bstar_le_normalizer_Sstar {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    Bstar P B ≤ Subgroup.normalizer (Sstar P T B : Set (MulAut ↥P)) := by
  have hc := (CoprimeStarSubgroupStructure.«structure» h51 h53).2.2.2
  have := Subgroup.normalizer_commutator_ge_right (Sstar P T B) (Bstar P B)
  rwa [hc] at this

theorem R_le {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {A : Subgroup G} (hAB : A ≤ B) :
    R P T B A ≤ Sstar P T B :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Bstar_mono hAB).trans (Bstar_le_normalizer_Sstar hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction))

theorem isPGroup {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {A : Subgroup G} (hAB : A ≤ B) :
    IsPGroup 2 (R P T B A) :=
  (SstarQuotientFaithful.isPGroup hc).to_le (R_le hc hAB)

theorem generated {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) :
    ⁅R P T B A, Bstar P A⁆ = R P T B A := by
  have hS := SstarQuotientFaithful.isPGroup hc
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hq2 : q ≠ 2 := PrimeActionFixedFree.q_ne_two hc hAB hA
  have hcop : Nat.Coprime (Nat.card (Bstar P A)) (Nat.card (Sstar P T B)) := by
    rw [hn, PrimeActionFixedFree.card_image hc hq hAB hA]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr
      (hq.eq_two_or_odd'.resolve_left hq2))
  exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime (Sstar P T B) (Bstar P A) hcop
    ((Bstar_mono hAB).trans (Bstar_le_normalizer_Sstar hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction))

end CFSG.LocalAnalysis.RankThreeUC.Section5.RstarCoprime
