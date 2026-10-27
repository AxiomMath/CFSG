module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.Monster.Schur.Restriction
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.He

open Subgroup CFSG.Open

theorem noPerfectDoubleCover_He
    (hM : TBLit.HeldTrivialMultiplier) :
    CFSG.Monster.Schur.NoPerfectDoubleCover (Blueprint.NativeSporadic.Carrier .He) := by
  intro E _ π hπ hperf hker
  have : Finite (Blueprint.NativeSporadic.Carrier .He) :=
    Nat.finite_of_card_ne_zero (by
      rw [show Nat.card (Blueprint.NativeSporadic.Carrier .He) = 4030387200 from
        CFSG.Sporadic.He.card_He]
      norm_num)
  have : Finite E := CFSG.Monster.Schur.finite_of_card_ker_ne_zero π (by omega)
  have hsimple : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.isSimpleGroup_He
  obtain ⟨z, hz1, hzc, -, hkz⟩ :=
    CFSG.Monster.Schur.exists_central_involution_of_card_ker_eq_two π hker
  have hkc : π.ker ≤ center E := by
    rw [hkz, zpowers_le]
    exact hzc
  have hZHe : center (Blueprint.NativeSporadic.Carrier .He) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center _) with h | h
    · exact h
    · exfalso
      have : IsMulCommutative (Blueprint.NativeSporadic.Carrier .He) :=
        ⟨⟨fun a b => mem_center_iff.mp (h ▸ mem_top b) a⟩⟩
      have hp := Group.is_simple_iff_prime_card.1 hsimple
      rw [show Nat.card (Blueprint.NativeSporadic.Carrier .He) = 4030387200 from
        CFSG.Sporadic.He.card_He] at hp
      exact absurd hp (by norm_num)
  have hcz : center E ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, ← mem_bot, ← hZHe, mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := hπ y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
  have hZ : center E = π.ker := le_antisymm hcz hkc
  let e : E ⧸ center E ≃* Blueprint.NativeSporadic.Carrier .He :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hnc : ∃ a b : E ⧸ center E, a * b ≠ b * a := by
    obtain ⟨g, hg⟩ : ∃ g : Blueprint.NativeSporadic.Carrier .He, g ≠ 1 := exists_ne 1
    have hgc : g ∉ center (Blueprint.NativeSporadic.Carrier .He) := by
      rw [hZHe, mem_bot]
      exact hg
    rw [mem_center_iff] at hgc
    push Not at hgc
    obtain ⟨h, hh⟩ := hgc
    exact ⟨e.symm h, e.symm g, fun hab => hh (by simpa using congrArg e hab)⟩
  have hq : IsQuasisimple E :=
    ⟨hperf, @MulEquiv.isSimpleGroup _ _ _ _ hsimple e, hnc⟩
  have hbot := hM E hq ⟨e⟩
  rw [← hZ, hbot, card_bot] at hker
  omega

end CFSG.ComponentClassification.RankTwoSporadic.He
