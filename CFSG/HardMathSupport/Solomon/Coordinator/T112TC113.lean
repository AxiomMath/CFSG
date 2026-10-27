module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TC113Lin
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TC113Exc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

structure CoverT10113 : Prop where
  e6 : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L → Nat.card (Subgroup.center L) = 3 →
    ∀ r f : ℕ, CFSG.Models.LieModel (L ⧸ Subgroup.center L) .E6 0 r f → 3 ∣ r ^ f - 1 →
      6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  twistedE6 : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    ∀ r f : ℕ, CFSG.Models.LieModel (L ⧸ Subgroup.center L) .twistedE6 0 r f → 3 ∣ r ^ f + 1 →
      6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)

theorem tables112Types_T10_11_3_of_cover (hGA : CFSG.Open.GriessAllModelsStatement)
    (C : CoverT10113) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      CFSG.Open.IsKGroup K → Nat.card (Subgroup.center K) = 3 → LieCentralQuotient K →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 4 → IsTenElevenOne K ∨ IsHatGTwoThree K := by
  intro K _ _ hq _ hZ hLie h4
  have hperf : Group.IsPerfect K := ⟨hq.1⟩
  obtain ⟨d, ⟨e⟩⟩ := hLie
  obtain ⟨t, n, p, f, hm⟩ := exists_lieModel d
  have hmX : CFSG.Models.LieModel (K ⧸ Subgroup.center K) t n p f :=
    models_lieModel_of_mulEquiv e.symm hm
  have htab := center_dvd_table hGA (isQuasisimple_of_open' hq) (MulEquiv.refl _) hmX
  rw [hZ] at htab
  have hmain : ∀ n' : ℕ, n' ≠ 0 → 3 ∣ n' → n' ≠ 3 → 6 ≤ n' := by
    intro n' h0 h3 h33
    obtain ⟨k, rfl⟩ := h3
    omega
  rcases case_of_dvd_table Nat.prime_three (by norm_num) htab with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ |
    ⟨⟨rfl, -, hd⟩ | ⟨rfl, -, hd⟩⟩ | ⟨-, hx⟩
  ·
    have hn2 : 2 ≤ n := hmX.1.2.2.1
    have h3n : 3 ∣ n := hg.trans (Nat.gcd_dvd_left _ _)
    by_cases hn3 : n = 3
    · subst hn3
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
        (isSLThree_of_cover hGA hperf hZ (MulEquiv.refl _) hmX
          (hg.trans (Nat.gcd_dvd_right _ _)))))))
    · exfalso
      have h6 := hmain n (by omega) h3n hn3
      have := five_le_pRank_of_lin hGA hperf hZ
        (blueprintLieModel_of_models_lin hmX (Or.inl rfl) (by omega)) (Or.inl rfl) hg h6
      omega
  ·
    have hn2 : 3 ≤ n := hmX.1.2.2.1
    have h3n : 3 ∣ n := hg.trans (Nat.gcd_dvd_left _ _)
    by_cases hn3 : n = 3
    · subst hn3
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
        (isSUThree_of_cover hGA hperf hZ (MulEquiv.refl _) hmX
          (hg.trans (Nat.gcd_dvd_right _ _)))))))
    · exfalso
      have h6 := hmain n (by omega) h3n hn3
      have := five_le_pRank_of_lin hGA hperf hZ
        (blueprintLieModel_of_models_lin hmX (Or.inr rfl) (by omega)) (Or.inr rfl) hg h6
      omega
  ·
    exfalso
    obtain rfl : n = 0 := hmX.1.2.2
    have := C.e6 K hperf hZ p f hmX hd
    omega
  ·
    exfalso
    obtain rfl : n = 0 := hmX.1.2.2
    have := C.twistedE6 K hperf hZ p f hmX hd
    omega
  · rcases hx with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl (Or.inl (isHatSix_of_cover hq hZ (MulEquiv.refl _) hmX))
    · exfalso
      have := six_le_pRank_of_O7 hq hZ (MulEquiv.refl _) hmX
      omega
    · exact Or.inr (isHatGTwoThree_of_cover hq hZ (MulEquiv.refl _) hmX)
    · exfalso
      have := five_le_pRank_of_U43 hZ (MulEquiv.refl _) hmX
      omega

end CFSG.HardMathSupport.Solomon.Coordinator
