module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22AltSection
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestThree
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Fi22Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem factorization_five_fi22 : (64561751654400 : ℕ).factorization 5 = 2 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hm : (2582470066176 : ℕ) ≠ 0 := by norm_num
  have hnd : ¬ 5 ∣ 2582470066176 := by norm_num
  rw [show (64561751654400 : ℕ) = 5 ^ 2 * 2582470066176 by norm_num,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm, Finsupp.add_apply,
    Nat.Prime.factorization_pow h5.out, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

theorem kFactFi22GuestThree :
    KFactFi22GuestThree := by
  intro L _ _ hL
  have hFi : IsFi22 L := hL
  obtain ⟨⟨X, Y, q, xs, D⟩, hcard⟩ := altData_of_isFi22 hL
  refine ⟨?_, ?_, kFactFi22AltSection L hFi, ?_⟩
  · obtain ⟨φ⟩ := hL
    obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
    have e : L ≃* CFSG.Blueprint.NativeSporadic.Fi22 := (β.trans φ.symm).symm
    have h1 : Nat.card (Outer L) = Nat.card (Outer CFSG.Blueprint.NativeSporadic.Fi22) :=
      CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e
    have hout : Nat.card (Outer L) = 2 :=
      h1.trans CFSG.RankThree.PartOne.card_outer_fi22_carrier
    rw [hout]
    norm_num
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨T⟩ : Nonempty (Sylow 5 L) := inferInstance
    obtain ⟨E, -, hE, hE81⟩ := kFactFi22GuestRank L hFi T
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hE81
  · intro A _ hA25
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨S, rfl⟩ : ∃ S : Sylow 5 L, (S : Subgroup L) = A :=
      ⟨Sylow.ofCard A (by rw [hA25, hcard, factorization_five_fi22]), Sylow.coe_ofCard _ _⟩
    obtain ⟨J, hJ, hle⟩ := D.exists_alt_join S
    exact ⟨9, J, le_refl _, hJ, hle⟩

end CFSG.AGLEmbeddingD2
