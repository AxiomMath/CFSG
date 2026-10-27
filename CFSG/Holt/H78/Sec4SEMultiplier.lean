module

public import CFSG.Holt.H78.Sec4FinalB2
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate10007
public import Certificates.Certificate10008
import CFSG.Holt.H78.Schur
import CFSG.Adapters.LinearSmallCatalog
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Walter.PSL2Facts.Even
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
import CFSG.LieType.Steinberg.CentralExt.SuzukiMultiplier
import CFSG.LieType.Multipliers.Sz8
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.Holt.H78

open scoped MatrixGroups

section Families

variable {E X : Type} [Group E] [Finite E] [Group.IsPerfect E] [Group X]
  (ρ : E →* X) (hρ : Function.Surjective ρ) (hZ : ρ.ker ≤ Subgroup.center E)
  (h2 : IsPGroup 2 ρ.ker)
include hρ hZ h2

section Trivial


theorem ker_eq_bot_of_psl {f : ℕ} (hf : 3 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f)) :
    ρ.ker = ⊥ := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let e' : X ≃* SL(2, GaloisField 2 f) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have hk := MonoidHom.ker_mulEquiv_comp ρ e'
  rw [← hk]
  exact CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot f hf hcard
    _ (e'.surjective.comp hρ) (by rw [hk]; exact hZ) (by rw [hk]; exact h2)

theorem ker_eq_bot_of_sz {a : ℕ} (ha : 2 ≤ a) (e : X ≃* CFSG.Open.Sz a) : ρ.ker = ⊥ := by
  let e' := e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)
  have hk := MonoidHom.ker_mulEquiv_comp ρ e'
  rw [← hk]
  exact CFSG.LieType.Steinberg.CentralExt.SuzukiClosed.suzuki_two_cover_trivial ha _
    (e'.surjective.comp hρ) (by rw [hk]; exact hZ) (by rw [hk]; exact h2)

theorem ker_eq_bot_of_psu {f : ℕ} (hf : 2 ≤ f) (e : X ≃* CFSG.Open.PSU3 2 f) : ρ.ker = ⊥ := by
  have hk := MonoidHom.ker_mulEquiv_comp ρ e
  rw [← hk]
  exact CFSG.ShultStronglyClosedTI.unitaryCover_native_kernel_eq_bot f hf _
    (e.surjective.comp hρ) (by rw [hk]; exact hZ) (by rw [hk]; exact h2)

end Trivial

theorem card_ker_le_two_of_psl_four (e : X ≃* PSL(2, GaloisField 2 2)) :
    Nat.card ρ.ker ≤ 2 := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨eA⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hcard)
  let e' : X ≃* alternatingGroup (Fin 5) :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _)).trans eA
  have hk := MonoidHom.ker_mulEquiv_comp ρ e'
  rw [← hk]
  refine card_ker_le_two_of_alternating_stem le_rfl _ (e'.surjective.comp hρ)
    (by rw [hk]; exact hZ) ?_ (by rw [hk]; exact h2)
  rw [Group.IsPerfect.commutator_eq_top]
  exact le_top

omit [Finite E] h2 in
theorem card_ker_le_four_of_sz_one (e : X ≃* CFSG.Open.Sz 1) :
    Nat.card ρ.ker ≤ 4 ∧ Nat.card X = 29120 := by
  let eT : TauCeti.suzukiGroup 1 ≃* X := (CFSG.BenderSuzuki.Catalog.suzukiGroupEquiv 1).trans
    ((CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv 1).symm.trans e.symm)
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Sz8.multiplier_of_mulEquiv eT
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) = 4 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv,
      Nat.card_congr eM.toEquiv, Nat.card_prod]
    simp
  have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier X) :=
    Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [← hM]
    exact Nat.card_le_card_of_surjective _
      (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective ρ hρ hZ)
  · rw [← Nat.card_congr eT.toEquiv, CFSG.LieType.Multipliers.Sz8.card_suzukiGroup]

end Families

section Main

theorem card_ker_le_four_of_isNaturalSE {E Δ : Type} [Group E] [Finite E] [Group.IsPerfect E]
    {M : Subgroup (Equiv.Perm Δ)} (hM : IsNaturalSE M) (ρ : E →* M)
    (hρ : Function.Surjective ρ) (hZ : ρ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 ρ.ker) :
    Nat.card ρ.ker ≤ 4 ∧ (Nat.card ρ.ker = 4 → Nat.card M = 29120) := by
  obtain ⟨q, i, hB⟩ := hM
  have hbot : ρ.ker = ⊥ → Nat.card ρ.ker ≤ 4 ∧ (Nat.card ρ.ker = 4 → Nat.card M = 29120) := by
    intro h
    rw [h, Subgroup.card_bot]
    omega
  rcases hB.model with ⟨-, f, hf, -, ⟨e⟩⟩ | ⟨-, a, ha, -, ⟨e⟩⟩ | ⟨-, f, hf, -, ⟨e⟩⟩
  · have e' := Subgroup.topEquiv.symm.trans e
    rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
    · have h := card_ker_le_two_of_psl_four ρ hρ hZ h2 e'
      omega
    · exact hbot (ker_eq_bot_of_psl ρ hρ hZ h2 hf3 e')
  · have e' := Subgroup.topEquiv.symm.trans e
    rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · obtain ⟨h4, h29⟩ := card_ker_le_four_of_sz_one ρ hρ hZ e'
      exact ⟨h4, fun _ => h29⟩
    · exact hbot (ker_eq_bot_of_sz ρ hρ hZ h2 ha2 e')
  · exact hbot (ker_eq_bot_of_psu ρ hρ hZ h2 hf (Subgroup.topEquiv.symm.trans e))

theorem sETwoMultiplierBound : SETwoMultiplierBound := by
  intro E _ _ Δ _ π hM hZ hsq hperf
  have : Group.IsPerfect E := Group.isPerfect_def.mpr hperf
  have hk : π.rangeRestrict.ker = π.ker := MonoidHom.ker_rangeRestrict π
  have h2 : IsPGroup 2 π.rangeRestrict.ker := by
    rw [hk]
    intro z
    exact ⟨1, Subtype.ext (by rw [pow_one, sq]; exact hsq z z.2)⟩
  have h := card_ker_le_four_of_isNaturalSE hM π.rangeRestrict π.rangeRestrict_surjective
    (by rw [hk]; exact hZ) h2
  rwa [hk] at h

theorem seTwoCoverConj_of_szEight (h : SzEightTwoCoverConj) : SETwoCoverConj :=
  seTwoCoverConj_of sETwoMultiplierBound h

end Main

end CFSG.Holt.H78
