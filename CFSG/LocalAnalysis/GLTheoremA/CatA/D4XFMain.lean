module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TI117

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XF

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.LocalAnalysis.GLTheoremA.D4T

@[expose] def D4TwoAutNormInn : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isD4two →
    ∀ P S : Subgroup (MulAut K), CFSG.Open.IsElemAbelian 3 P → ¬ P ≤ innerAut K →
      Nat.card P = 3 ^ 3 → IsPGroup 2 S → S ≠ ⊥ → P ≤ Subgroup.normalizer (S : Set (MulAut K)) →
      S ≤ innerAut K → False

theorem d4two_aut_norm_of_residual (hres : D4TwoAutNormInn) {K : Type} [Group K] [Finite K]
    (h : catalogIs K S9.isD4two) (P S : Subgroup (MulAut K)) (hP : CFSG.Open.IsElemAbelian 3 P)
    (hPn : ¬ P ≤ innerAut K) (hcard : Nat.card P = 3 ^ 3) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hPS : P ≤ Subgroup.normalizer (S : Set (MulAut K))) : False := by
  by_cases hT : S.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K) : MulAut K →* MulAut K ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner K) = ⊥
  · refine hres K h P S hP hPn hcard hS2 hS1 hPS fun s hs => ?_
    have hm : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K) : MulAut K →* MulAut K ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner K) s ∈
        S.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K) : MulAut K →* MulAut K ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :=
      Subgroup.mem_map_of_mem _ hs
    rw [hT, Subgroup.mem_bot] at hm
    exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner K) s).1 hm
  · exact d4two_aut_norm_of_out_ne_bot h hP hPn hS2 hPS hT

theorem d4TwoFacts_of_residual (hres : D4TwoAutNormInn) {K : Type} [Group K] [Finite K]
    (h : catalogIs K S9.isD4two) : D4TwoFacts K :=
  ⟨d4two_rank3 h, d4two_rank4 h, d4two_aut_le h,
    fun P S hP hPn hcard hS2 hS1 hPS => d4two_aut_norm_of_residual hres h P S hP hPn hcard hS2 hS1 hPS⟩

theorem d4TwoFactsAt_of_residual (hres : D4TwoAutNormInn) : D4TwoFactsAt :=
  fun K _ _ h => d4TwoFacts_of_residual hres h

end CFSG.LocalAnalysis.GLTheoremA.D4XF
