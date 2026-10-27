module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwBigAnyClasses
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyClassTriQuad
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyQuad

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice
open scoped Matrix

set_option linter.unusedSectionVars false


theorem model_le_Γ_ofFrobenius_E8 (w : WeylGroup Tag.E8) (K : Type) [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E8 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E8 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w) :
    (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).model ≤
      (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).Γ := by
  classical
  set D := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 with hDdef
  have hd := langDescent_ofFrobenius (Or.inr (Or.inr (Or.inr rfl))) w K hFr hg0C hg0
  have hD : D.Φ = Units.map (entrywiseHom Fr) := rfl
  have hrange : ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup Tag.E8 K).subtype).range =
      (adjointGroup Tag.E8 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hfixle : D.fix ≤ ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup Tag.E8 K).subtype).range := by
    have hfin := hd.finite_fix
    have h := (finite_fixed_subgroup_rational 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr D.fix
      (fun x hx => ((LangDatum.mem_fix D).1 hx).1)
      (fun x hx => by have := ((LangDatum.mem_fix D).1 hx).2; rwa [hD] at this)).1
    rw [Nat.dvd_one] at h
    rw [hrange]
    exact Subgroup.relIndex_eq_one.1 h
  rw [LangDescent.model_eq, hd.Γ_eq]
  exact Subgroup.map_mono hfixle

theorem e8PhiFourWeyl_sq_smul (δ : Fin Tag.E8.rank → ℤ) :
    e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ := by
  rw [wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, Matrix.mulVec_mulVec,
    e8FourMat_rel, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem bigAnyPBigAtFrobenius_E8_four_five :
    BigAnyPBigAtFrobenius .E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1 ∧ 4 ≤ q := by
  intro K _ _ Fr hFr g0 hg0C hg0 S hSD _
  have hq : S.D.q = Nat.card K := by rw [hSD]; rfl
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hq]; exact hFr c
  have hΦ : S.D.Φ = Units.map (entrywiseHom Fr) := by rw [hSD]; rfl
  have hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8PhiFourWeyl := by
    rw [hSD]; rfl
  have hMΓ : S.D.model ≤ S.Γ := by
    show S.D.model ≤ S.D.Γ
    rw [hSD]
    exact model_le_Γ_ofFrobenius_E8 e8PhiFourWeyl K hFr hg0C hg0
  exact bigAnyPBig_of_phi4_of_ne_two S hFr' hΦ hn (Or.inr (Or.inr (Or.inr rfl)))
    (fun δ _ => e8PhiFourWeyl_sq_smul δ) (by norm_num) hMΓ

end CFSG.HardMathSupport.Timmesfeld.CrossChar
