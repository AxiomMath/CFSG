module

public import CFSG.RankThree.PartOne.S12.InputsSec15

import CFSG.GroupTheory.Fitting.PPrimeCoreGeneralizedFitting
import CFSG.GroupTheory.HuppertProduct.RankBound
import CFSG.Quasithin.Vol2.Ch1Sec3Solvable
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

@[expose] def AutMAt (p : ℕ) {X : Type*} [Group X] (N : Subgroup X) : Prop :=
  ∀ R : Subgroup X, R ≤ N → (∀ x ∈ R, x ^ 3 = 1) → 9 ≤ Nat.card R →
    Nat.card R = 9 ∧ ∃ r ∈ R, r ≠ 1 ∧ ∃ c ∈ CFSG.generalizedFitting X,
      c * r = r * c ∧ IsPGroup p (Subgroup.zpowers c) ∧ c ∉ N

@[expose] def AutMFor (p : ℕ) (L : Type*) [Group L] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (↥(CFSG.generalizedFitting X) ≃* L) →
    ∀ N : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded p N → AutMAt p N

theorem two_le_pRank_three_of_nine_le {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hexp : ∀ x ∈ A, x ^ 3 = 1) (h9 : 9 ≤ Nat.card A) : 2 ≤ CFSG.Open.pRank 3 A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.Quasithin.Ch1Sec3.two_le_pRank_of_pow_eq_one (p := 3) hexp (by simpa using h9)

theorem card_le_three_of_exponent_three_of_pRank_le_one {X : Type*} [Group X] [Finite X]
    {A : Subgroup X} (hexp : ∀ x ∈ A, x ^ 3 = 1) (hA : CFSG.Open.pRank 3 A ≤ 1) :
    Nat.card A ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA3
  by_contra h
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have hk1 : k ≤ 1 := by omega
    have h3k : 3 ^ k ≤ 3 := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 3) hk1
    omega
  have h9 : 9 ≤ Nat.card A := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hk2
  have := two_le_pRank_three_of_nine_le hexp h9
  omega

theorem card_le_nine_of_map_isCyclic {X Y : Type*} [Group X] [Group Y] [Finite X]
    {R : Subgroup X} (hexp : ∀ x ∈ R, x ^ 3 = 1) (φ : X →* Y)
    (hcyc : IsCyclic ↥(R.map φ)) (hker : Nat.card ↥(R ⊓ φ.ker) ≤ 3) :
    Nat.card R ≤ 9 := by
  let f : ↥R →* Y := φ.comp R.subtype
  have hkerf : Nat.card ↥(f.ker) = Nat.card ↥(R ⊓ φ.ker) := by
    have h1 : f.ker = φ.ker.subgroupOf R := by
      rw [← MonoidHom.comap_ker, Subgroup.comap_subtype]
    rw [h1, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hrange : f.range = R.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  haveI : Finite ↥(f.range) :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI : IsCyclic ↥(f.range) := hrange ▸ hcyc
  have hexpf : ∀ y ∈ f.range, y ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    simpa [f, map_pow] using congrArg φ (hexp x x.2)
  have hcardrange : Nat.card ↥(f.range) ≤ 3 := by
    have h := CFSG.GroupTheory.HuppertProduct.card_le_three_of_isCyclic
      (G := ↥(f.range)) (S := ⊤) (F := ⊤) (Subgroup.isCyclic ⊤) le_rfl
      (fun e _ => Subtype.ext (hexpf e.1 e.2))
    simpa using h
  have hcard := Subgroup.card_ker_mul_card_range f
  calc
    Nat.card R = Nat.card ↥(f.ker) * Nat.card ↥(f.range) := hcard.symm
    _ ≤ 3 * 3 := by
      rw [hkerf]
      exact Nat.mul_le_mul hker hcardrange
    _ = 9 := by norm_num

theorem autMAt_of_pRank_le_one (p : ℕ) {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : CFSG.Open.pRank 3 N ≤ 1) : AutMAt p N := by
  intro R hRN hexp h9
  exfalso
  have h2 : 2 ≤ CFSG.Open.pRank 3 R := two_le_pRank_three_of_nine_le hexp h9
  have hle : CFSG.Open.pRank 3 R ≤ CFSG.Open.pRank 3 N :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hRN
  omega

theorem autMAt_of_not_three_dvd (p : ℕ) {X : Type*} [Group X] [Finite X] (N : Subgroup X)
    (h3 : ¬ 3 ∣ Nat.card X) : AutMAt p N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro R _ hexp h9
  exfalso
  have hR3 : IsPGroup 3 R := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hdvdR : 3 ∣ Nat.card R := by
    rcases hR3.card_eq_or_dvd with h1 | h
    · omega
    · exact h
  exact h3 (hdvdR.trans (Subgroup.card_subgroup_dvd_card R))

theorem autMFor_of {p : ℕ} [Fact p.Prime] {L : Type*} [Group L] [IsSimpleGroup L]
    (hpL : p ∣ Nat.card L)
    (h : ∀ (X : Type) [Group X] [Finite X], CFSG.pPrimeCore p X = ⊥ →
      ∀ N : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded p N →
        (↥(CFSG.generalizedFitting X) ≃* L) → AutMAt p N) :
    AutMFor p L := by
  intro X _ _ ⟨e⟩ N hN
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting X) :=
    (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  have hpF : p ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
    rw [Nat.card_congr e.toEquiv]
    exact hpL
  exact h X (CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting inferInstance hpF)
    N hN e

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
