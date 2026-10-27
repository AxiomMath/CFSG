module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
import CFSG.Adapters.RankTwoModelTransports
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryLin

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.NonUnitary

theorem wcOn_psl2GF {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    WCOn p (PSL2GF p f) := by
  obtain ⟨U⟩ : Nonempty (Sylow p (PSL2GF p f)) := inferInstance
  have hUcard : Nat.card (U : Subgroup (PSL2GF p f)) = p ^ f := (psl2GF_sylow p f hf U).2
  by_cases hf1 : f = 1
  · subst hf1
    apply WCOn.of_factorization_le_one
    rw [U.card_eq_multiplicity] at hUcard
    have h1 : (Nat.card (PSL2GF p 1)).factorization p = 1 :=
      Nat.pow_right_injective (Fact.out : p.Prime).two_le hUcard
    exact h1.le
  · refine WCOn.of_normalizerMovesLines U fun _ _ A hAP hA => ?_
    by_contra hcon
    push Not at hcon
    have hbot : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hA
      exact (Fact.out : p.Prime).one_lt.ne hA
    have hN : Subgroup.normalizer ((U : Subgroup (PSL2GF p f)) : Set (PSL2GF p f)) ≤
        Subgroup.normalizer (A : Set (PSL2GF p f)) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hmap := hcon n hn
      constructor
      · intro hh
        rw [← hmap]
        exact ⟨h, hh, rfl⟩
      · intro hh
        rw [← hmap] at hh
        obtain ⟨h', hh', he⟩ := hh
        have : h' = h := by
          have he' : n * h' * n⁻¹ = n * h * n⁻¹ := he
          simpa using he'
        exact this ▸ hh'
    have hAU := psl2GF_invariant' hp2 hf U A hAP hbot hN
    rw [hAU, hUcard] at hA
    have hlt : p ^ 1 < p ^ f := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    rw [pow_one] at hlt
    omega

theorem wcOn_psl_two {K : Type} [Group K] [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : StatedClassicalModel K .PSL 2 p f) : WCOn p K := by
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K 2 p f h
  exact WCOn.of_mulEquiv e (wcOn_psl2GF hp2 hf)

theorem wcOn_psl_of_three_le {K : Type} [Group K] [Finite K] {n p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (h : StatedClassicalModel K .PSL n p f) : WCOn p K := by
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K n p f h
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  exact WCOn.of_mulEquiv e (WCOn.of_hasNoncommPair
    (CFSG.RankThree.PartOne.StrongP.hasNoncommPair_psl p n (K := GaloisField p f) hp3 hn))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
