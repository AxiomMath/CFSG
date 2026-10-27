module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.SubgroupLists.SL3Involutions
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Local

section Rank

theorem pRank_two_sl3_le_two {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E _ hE
  have hle : Nat.card (E.map Matrix.SpecialLinearGroup.toGL) ≤ 4 := by
    apply CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← sq, hE.2 x hx, map_one]
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
  rw [Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective] at hle
  norm_num
  exact hle

theorem pRank_two_le_two_of_PSL3 {A : Type} [Group A] [Finite A] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : LieModel A .PSL 3 p n) :
    CFSG.Open.pRank 2 (⊤ : Subgroup A) ≤ 2 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hA
  have hodd : Odd (Nat.card F) := hF ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd
  have hZ : ¬ 2 ∣ Nat.card (scalars 3 F) := by
    rw [card_scalars_eq_gcd F (by norm_num : 1 ≤ 3)]
    intro h
    have := Nat.dvd_trans h (Nat.gcd_dvd_left 3 (Nat.card F - 1))
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
    CFSG.SectionRank.pRank_quotient_eq (G := Matrix.SpecialLinearGroup (Fin 3) F)
      (scalars 3 F) hZ]
  exact pRank_two_sl3_le_two h2

theorem card_le_of_pRank {G : Type} [Group G] [Finite G] {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) :
    ∃ k : ℕ, Nat.card ↥E = 2 ^ k ∧ k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥E := fun x => ⟨1, by
    refine Subtype.ext ?_
    have := hE.2 x x.2
    simpa using this⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  exact ⟨k, hk, CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk⟩

end Rank

section Main

theorem card_elemAbelian_two_le_four_of_PSL3 {A : Type} [Group A] [Finite A] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : LieModel A .PSL 3 p n) (E : Subgroup A)
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card ↥E ≤ 4 := by
  obtain ⟨k, hk, hkr⟩ := card_le_of_pRank hE
  have hr := pRank_two_le_two_of_PSL3 hp hp2 hA
  rw [hk]
  have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkr.trans hr)
  omega

theorem card_elemAbelian_two_le_four_of_hat {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : LieModel (Hat K) .PSL 3 p n) (E : Subgroup Y)
    (hEK : E ≤ K) (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card ↥E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, -⟩ := card_le_of_pRank hE
  have hkK : k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hE.1.is_comm.comm
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) hk (Subgroup.inclusion hEK) (Subgroup.inclusion_injective hEK) le_top
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (pPrimeCore_coprime_card)
  have hq := CFSG.SectionRank.pRank_quotient_eq (G := ↥K) (pPrimeCore 2 ↥K) hN
  have hr := pRank_two_le_two_of_PSL3 hp hp2 hK
  change CFSG.Open.pRank 2 (⊤ : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) ≤ 2 at hr
  rw [hq] at hr
  rw [hk]
  have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkK.trans hr)
  omega

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
