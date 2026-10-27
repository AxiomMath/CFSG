module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcUntw
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcChainsE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcChainsE8
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Six
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE6
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE8

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section Main


theorem noSylowNormalizesTwo_E6 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    NoSylowNormalizesTwo p (adjointGroup Tag.E6 K) := by
  classical
  haveI : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have hB : 12 < p * 6 := by omega
  refine noSylowNormalizesTwo_adjoint_of_chains .E6 hp (by omega) hpK he excE6Full
    parabolicSum_E6_univ_eq excE6Mask excE6Fac excE6Mask_cover parabolicSum_E6_coat_eq ?_ ?_ ?_
  · exact goodFactors_of_bound (by omega) hB (by decide)
  · intro i
    exact goodFactors_of_bound (by omega) hB (by fin_cases i <;> decide)
  · intro i
    fin_cases i <;> decide

theorem sylowTorus_of_degCount_E6 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ Nat.card K) {e : ℕ} (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hcnt : degCount Tag.E6 e = 2) :
    (e = 4 ∨ e = 6) ∧ SylowTorus (adjointGroup Tag.E6 K) p 2 := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) (by omega : 0 < degCount Tag.E6 e)
  have h46 : e = 4 ∨ e = 6 := by
    interval_cases e <;> first | (left; rfl) | (right; rfl) | exact absurd hcnt (by decide) | omega
  refine ⟨h46, ?_⟩
  rcases h46 with rfl | rfl
  · exact sylowTorus_E6_four K hp he
  · exact sylowTorus_E6_six K hp he

theorem pClosureOdd_adjointE6 (K : Type) [Field K] [Finite K] [CharP K 2] {f p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hne4 : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 4)
    (hrk1 : ¬ RankLE1 p (adjointGroup Tag.E6 K)) (hrk2 : RankLE2 p (adjointGroup Tag.E6 K)) :
    PClosureOdd p (adjointGroup Tag.E6 K) := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd'
    exact (by omega : p ≠ 2) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow hd'))
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  have h1 : 2 ≤ degCount Tag.E6 e := by
    by_contra h
    exact hrk1 (rankLE1_E6 K hp hpK (by rw [he]; omega))
  have h3 : degCount Tag.E6 e ≤ 2 := by
    by_contra h
    exact not_rankLE2_E6 K hp (by omega) hpK (by rw [he]; omega) hrk2
  obtain ⟨h46, hT⟩ := sylowTorus_of_degCount_E6 K hp hpK he (by omega)
  have h6 : e = 6 := by
    rcases h46 with h | h
    · exact absurd (he.trans h) hne4
    · exact h
  subst h6
  exact pClosureOdd_of_sylowTorus hp hT (noSylowNormalizesTwo_E6 hp hp5 hpK he)

theorem sylowTorus_of_degCount_E7 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ Nat.card K) {e : ℕ} (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hcnt : degCount Tag.E7 e = 2) : e = 4 ∧ SylowTorus (adjointGroup Tag.E7 K) p 2 := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle := le_thirty_of_degCount_pos (τ := Tag.E7) (by simp) (by omega : 0 < degCount Tag.E7 e)
  have h4 : e = 4 := by
    interval_cases e <;> first | rfl | exact absurd hcnt (by decide) | omega
  subst h4
  exact ⟨rfl, sylowTorus_E7_four K hp he⟩

theorem noSylowNormalizesTwo_E8 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (h : e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12) :
    NoSylowNormalizesTwo p (adjointGroup Tag.E8 K) := by
  classical
  haveI : Fintype (WeylGroup .E8) := Fintype.ofFinite _
  have hep : e < p := orderOf_lt_prime hp hpK he
  have hp6 : p ≠ 6 := by
    rintro rfl
    norm_num at hp
  have hB : 30 < p * e := by
    rcases h with rfl | rfl | rfl | rfl <;> omega
  refine noSylowNormalizesTwo_adjoint_of_chains .E8 hp (by omega) hpK he excE8Full
    parabolicSum_E8_univ_eq excE8Mask excE8Fac excE8Mask_cover parabolicSum_E8_coat_eq ?_ ?_ ?_
  · exact goodFactors_of_bound (by omega) hB (by decide)
  · intro i
    exact goodFactors_of_bound (by omega) hB (by fin_cases i <;> decide)
  · intro i
    rcases h with rfl | rfl | rfl | rfl <;> fin_cases i <;> decide

theorem sylowTorus_of_degCount_E8 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ Nat.card K) {e : ℕ} (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hcnt : degCount Tag.E8 e = 2) :
    (e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12) ∧ SylowTorus (adjointGroup Tag.E8 K) p 2 := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) (by omega : 0 < degCount Tag.E8 e)
  have h5 : e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
    interval_cases e <;> first | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) |
      (right; right; right; rfl) | exact absurd hcnt (by decide) | omega
  refine ⟨h5, ?_⟩
  rcases h5 with rfl | rfl | rfl | rfl
  · exact sylowTorus_E8_five K hp he
  · exact sylowTorus_E8_eight K hp he
  · exact sylowTorus_E8_ten K hp he
  · exact sylowTorus_E8_twelve K hp he

theorem pClosureOdd_adjointE8 (K : Type) [Field K] [Finite K] [CharP K 2] {f p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk1 : ¬ RankLE1 p (adjointGroup Tag.E8 K)) (hrk2 : RankLE2 p (adjointGroup Tag.E8 K)) :
    PClosureOdd p (adjointGroup Tag.E8 K) := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd'
    exact (by omega : p ≠ 2) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow hd'))
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  have h1 : 2 ≤ degCount Tag.E8 e := by
    by_contra h
    exact hrk1 (rankLE1_E8 K hp hpK (by rw [he]; omega))
  have h3 : degCount Tag.E8 e ≤ 2 := by
    by_contra h
    exact not_rankLE2_E8 K hp (by omega) hpK (by rw [he]; omega) hrk2
  obtain ⟨h5, hT⟩ := sylowTorus_of_degCount_E8 K hp hpK he (by omega)
  exact pClosureOdd_of_sylowTorus hp hT (noSylowNormalizesTwo_E8 hp hp5 hpK he h5)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
