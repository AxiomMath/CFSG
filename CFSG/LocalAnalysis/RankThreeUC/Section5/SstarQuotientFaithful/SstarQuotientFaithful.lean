module


public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialBinaryActionCounterexample
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.SstarQuotientFaithful

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

theorem Xs_le_pCoreOf (T B : Subgroup G) (hB : B ≤ B ⊔ T) :
    twoCoreCommutator T B ≤ CFSG.Open.pCoreOf 2 (B ⊔ T) := by
  have hn : (CFSG.Open.pCore 2 ↥(B ⊔ T)).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : B = (B.subgroupOf (B ⊔ T)).map (B ⊔ T).subtype := by
    rw [Subgroup.subgroupOf_map_subtype]; simp [hB]
  have h2 : ⁅(CFSG.Open.pCore 2 ↥(B ⊔ T)).map (B ⊔ T).subtype,
      (B.subgroupOf (B ⊔ T)).map (B ⊔ T).subtype⁆ ≤
      (CFSG.Open.pCore 2 ↥(B ⊔ T)).map (B ⊔ T).subtype := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (Subgroup.commutator_le_left _ _)
  rw [← h1] at h2
  exact h2

theorem isPGroup {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (_h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    IsPGroup 2 (Sstar P T B) := by
  have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
  have hX : IsPGroup 2 (twoCoreCommutator T B) := hK.to_le (Xs_le_pCoreOf T B le_sup_left)
  exact (hX.comap_subtype (K := Subgroup.normalizer (P : Set G))).map (Subgroup.normalizerMonoidHom P)

theorem injective {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    Function.Injective
      ((CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.quotientHom ↥P).comp
        (Sstar P T B).subtype) := by
  refine CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.injective
    h.oddPrimeClassTwoAction.setting.prime ?_ h.extraspecial h.oddPrimeClassTwoAction.setting.exponent _ (isPGroup h)
  rintro rfl
  exact absurd h.oddPrimeClassTwoAction.setting.odd (by decide)

end CFSG.LocalAnalysis.RankThreeUC.Section5.SstarQuotientFaithful
