module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ClsRed
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrderBig
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lie_bounds lie_casework_le
  lieSylowExponent lieOrderNumerator lieOrderDivisor)

private theorem eq_d4three_of_card (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hX : CFSG.Blueprint.LieModel X t n 3 f)
    (hc : Nat.card X = 4952179814400) : t = .POmegaPlus ∧ n = 4 ∧ f = 1 := by
  have hadm := hX.admissible
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 12) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide +kernel
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide +kernel
  · rcases ht with rfl | rfl <;> revert hord <;> decide +kernel
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
      revert hord <;> decide +kernel

private theorem eq_g2three_of_card (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hX : CFSG.Blueprint.LieModel X t n 3 f)
    (hc : Nat.card X = 4245696) : t = .G2 ∧ n = 0 ∧ f = 1 := by
  have hadm := hX.admissible
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 6) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide +kernel
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide +kernel
  · rcases ht with rfl | rfl <;> revert hord <;> decide +kernel
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
      revert hord <;> decide +kernel

private theorem lieModel_of_outerLayer {t : StatedLieTag} {n f : ℕ} {X : Type} [Group X]
    (h : OuterLayerThree t n f X) (hX : ¬ Nat.card X ∣ 1512) :
    ∃ (t' : StatedLieTag) (n' f' : ℕ), OuterShapeThree t n f t' n' f' ∧
      CFSG.Blueprint.LieModel X t' n' 3 f' :=
  Or.resolve_right h fun h => hX h.2.2


private theorem catalogIs_d4_of_lieModel {S : Type} [Group S] {f r : ℕ}
    (hS : CFSG.Blueprint.LieModel S .POmegaPlus 4 3 f) (hr : 3 ^ f = r) :
    catalogIs S (S8.isD4of r) := by
  let q : TauCeti.PrimePower := ⟨3, f, Nat.prime_three, hS.admissible.2.1⟩
  have hv : (TauCeti.LieTypeIndex.D 4 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, not_false⟩
  have hY := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
    (CFSG.Models.lieModel_D 4 q hv (MulEquiv.refl _))
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique (by decide) (by trivial) hS hY
  exact ⟨.lie ⟨.D 4 q, hv⟩, show q.card = r by rw [TauCeti.PrimePower.card_def]; exact hr, ⟨e⟩⟩

private theorem catalogIs_g2_of_lieModel {S : Type} [Group S] {f r : ℕ}
    (hS : CFSG.Blueprint.LieModel S .G2 0 3 f) (hr : 3 ^ f = r) :
    catalogIs S (S8.isG2of r) := by
  have hadm := hS.admissible
  let q : TauCeti.PrimePower := ⟨3, f, Nat.prime_three, hadm.2.1⟩
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨?_, not_false⟩
    show 3 ≤ q.card
    rw [TauCeti.PrimePower.card_def]
    exact hadm.2.2.2
  have hY : CFSG.Blueprint.LieModel (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) .G2 0 3 f :=
    .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hadm,
      CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2 q hv
        (show (3 : ℕ) ≠ 2 by decide) (MulEquiv.refl _)⟩)
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique (by decide) (by trivial) hS hY
  exact ⟨.lie ⟨.G2 q, hv⟩, show q.card = r by rw [TauCeti.PrimePower.card_def]; exact hr, ⟨e⟩⟩

private theorem catalogIs_td4_of_lieModel {S : Type} [Group S] {f r : ℕ}
    (hS : CFSG.Blueprint.LieModel S .trialityD4 0 3 f) (hr : 3 ^ f = r) :
    catalogIs S (isTD4of r) := by
  have hadm := hS.admissible
  let q : TauCeti.PrimePower := ⟨3, f, Nat.prime_three, hadm.2.1⟩
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
  have hY : CFSG.Blueprint.LieModel (TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩)
      .trialityD4 0 3 f :=
    .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hadm,
      CFSG.TauCetiBridge.twistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q
        hv (show (3 : ℕ) ≠ 2 by decide) (by decide) (MulEquiv.refl _)⟩)
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique (by decide) (by trivial) hS hY
  refine ⟨.lie ⟨.trialityD4 q, hv⟩, ?_, ⟨e⟩⟩
  show q.card = r
  rw [TauCeti.PrimePower.card_def]
  exact hr

theorem i1432LieOut_of_fork (hb : LieOrderBridge) (hO : LieOrderFormulasInput)
    (hF : LieOuterThree) : I1432LieOut := by
  intro S _ _ d hc he α hα3 hα J hJ
  obtain ⟨e⟩ := he
  obtain ⟨t, n, f, hS⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.exists_blueprint_lieModel_of_odd d (by rw [hc]; decide) e
  rw [hc] at hS
  have hL := hF S t n f hS.admissible trivial hS α hα3 hα J hJ
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · have hc4 := ClsRed.card_d4three hb hT
    obtain ⟨t', n', f', hsh, hX⟩ := lieModel_of_outerLayer hL (by rw [hc4]; decide)
    obtain ⟨rfl, rfl, rfl⟩ := eq_d4three_of_card hO hX hc4
    rcases hsh with ⟨-, rfl, rfl, rfl⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩
    · exact catalogIs_d4_of_lieModel hS (by norm_num)
    all_goals exact absurd h (by decide)
  · have hc2 := ClsRed.card_g2three hb hT
    obtain ⟨t', n', f', hsh, hX⟩ := lieModel_of_outerLayer hL (by rw [hc2]; decide)
    obtain ⟨rfl, rfl, rfl⟩ := eq_g2three_of_card hO hX hc2
    rcases hsh with ⟨-, rfl, rfl, rfl⟩ | ⟨rfl, rfl, -, -, rfl⟩ | ⟨-, -, h, -⟩ | ⟨rfl, -, -, rfl⟩
    · exact .inl (catalogIs_g2_of_lieModel hS (by norm_num))
    · exact .inr (.inl (catalogIs_d4_of_lieModel hS (by norm_num)))
    · exact absurd h (by decide)
    · obtain rfl : n = 0 := hS.admissible.2.2
      exact .inr (.inr (.inl (catalogIs_td4_of_lieModel hS (by norm_num))))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
