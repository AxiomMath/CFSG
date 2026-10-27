module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Aut

open CFSG.Open

theorem prime_pow_eq_eight {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (h : p ^ k = 8) :
    p = 2 ∧ k = 3 := by
  have h8 : p ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
    exact dvd_pow_self p hk.ne'
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num))⟩

theorem pRank_le_two_of_rankLE2 {K : Type} [Group K] [Finite K]
    (hR : CFSG.LieType.SeitzGeneration.RankLE2 3 K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 :=
  CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => hR E hE

theorem pRank_mulAut_le_three_of_hom {C R : Type} [Group C] [Finite C] [Group R] [Finite R]
    [IsCyclic R] (Θ : MulAut C →* R)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    (hR : CFSG.Open.pRank 3 (⊤ : Subgroup C) ≤ 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut C)) ≤ 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have h1 := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_top_le_pRank_ker_add_pRank_range
    hp Θ
  have h2 : CFSG.Open.pRank 3 (MulAut.conj : C →* MulAut C).range =
      CFSG.Open.pRank 3 (⊤ : Subgroup C) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MonoidHom.ofInjective hinj)]
  have hcyc : IsCyclic ↥(⊤ : Subgroup R) :=
    isCyclic_of_surjective (Subgroup.topEquiv.symm : R ≃* ↥(⊤ : Subgroup R)).toMonoidHom
      (Subgroup.topEquiv.symm).surjective
  have h3 : CFSG.Open.pRank 3 Θ.range ≤ 1 :=
    le_trans (CFSG.SectionRank.pRank_mono hp.one_lt le_top)
      (CFSG.SectionRank.pRank_le_one_of_isCyclic (S := (⊤ : Subgroup R)) hp hcyc)
  rw [hker] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Aut

end
