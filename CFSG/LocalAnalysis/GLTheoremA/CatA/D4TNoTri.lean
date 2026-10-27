module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TI117
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPDich
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremA.FP

theorem exists_D4_of_isD4two {i : TauCeti.CFSGIndex} (hi : S9.isD4two i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.card = 2 ∧
      i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ := by
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D n q =>
      rcases n with _ | _ | _ | _ | _ | n
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact ⟨q, hv, hi, rfl⟩
      · exact hi.elim
    | _ => exact hi.elim
  | _ => exact hi.elim

section Marking

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem noTrialityMarking_of_inner {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hD4 : catalogIs (PSimple 3 L) S9.isD4two) {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hin : InducesInnerMod 3 L b) :
    CFSG.Assembly.LargeEvenMarking (PQuot 3 L) fun lab R _ I F θ =>
      ∀ φ : MulAut R, LargeEvenInduces θ (CFSG.LocalAnalysis.GLTheoremA.S10.indRel 3 L b) φ →
        CentralMod I φ := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hq := isQuasisimple_pQuot_of_glaPComponent hp3 hL
  obtain ⟨i, hi, ⟨f⟩⟩ := hD4
  obtain ⟨q, hv, hq2, rfl⟩ := exists_D4_of_isD4two hi
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq2] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq2
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv f
  rw [hp, he] at hmodel
  have h0 := Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 (t := .POmegaPlus) (n := 4)
    (f := 1) (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmodel⟩)
  have h1 := canon_marking_and_labelAll_simple (P' := RawInnBody 3)
    (fun lab hlab => canonRawInn' hp3 (by norm_num) hlab) h0
  refine Canonical.largeEvenMarking_mono ?_ h1
  rintro lab R _ I F θ ⟨-, hmul, hinv, hinn, -⟩ φ hφ
  have e := (induces_indRel_iff hbN θ).1 hφ
  obtain ⟨s, hs⟩ := (indAut_mem_inner_iff hp3 hL hbN).2 hin
  have hφc : φ = MulAut.conj (θ s) := by rw [e, ← hs, MI.congr_conj]
  intro γ
  have h1 : γ * φ * γ⁻¹ * φ⁻¹ = MulAut.conj (γ (θ s)) * MulAut.conj (θ s)⁻¹ := by
    rw [hφc, ← map_inv]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [h1]
  exact hmul _ (hinn _) _ (hinn _)

@[expose] def NoTrialityBigAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple 3 B x L →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → IsChevSimple 2 (PSimple 3 L) →
    catalogIs (PSimple 3 L) isD4any → ¬ catalogIs (PSimple 3 L) S9.isD4two → ∀ b ∈ B,
      CFSG.Assembly.LargeEvenMarking (PQuot 3 L) fun lab R _ I F θ =>
        ∀ φ : MulAut R, LargeEvenInduces θ (CFSG.LocalAnalysis.GLTheoremA.S10.indRel 3 L b) φ →
          CentralMod I φ

theorem noTrialityAt_of_split {G : Type} [Group G] [Finite G] (h117 : I117At G)
    (h112 : D4TwoNormalizes G) (hbig : NoTrialityBigAt G) : FP.NoTrialityAt G := by
  intro B x L hS hK hchev hd4 b hb
  by_cases hD4 : catalogIs (PSimple 3 L) S9.isD4two
  · have hBel : IsElemAbelian 3 B := hS.1.1
    have hBC : B ≤ Subgroup.centralizer ({x} : Set G) :=
      CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_le_centralizer hBel hS.2.1.1
    have hrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B :=
      CFSG.SectionRank.le_pRank Nat.prime_three.one_lt (le_refl B) hBel hS.1.2.1
    have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
      h112 _ B L hK hBel hBC
        ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le Nat.prime_three _).trans
          hrank) hS.2.2 hD4
    exact noTrialityMarking_of_inner hS.2.2 hD4 (hBL hb)
      (h117 B x L hS.1 hS.2.1 hK hS.2.2 hBL hD4 b hb)
  · exact hbig B x L hS hK hchev hd4 hD4 b hb

end Marking

end CFSG.LocalAnalysis.GLTheoremA.D4T
