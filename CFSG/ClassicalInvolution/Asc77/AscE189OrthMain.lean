module

public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
public import CFSG.ClassicalInvolution.Asc77.AscE189Model
public import CFSG.ClassicalInvolution.Asc77.AscE189Comp
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.AscIHThm2
public import CFSG.ClassicalInvolution.Asc77.AscIHWitness
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem spinAction_mem_orthogonalGroup (x : spinGroup Q) :
    spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q x)

omit [Finite K] [FiniteDimensional K V] in
theorem spinAction_ne_one_of_moved {F : Subgroup (spinGroup Q)} {z g : spinGroup Q}
    (hz : IsUniqueInvolution F z) (h3 : conjSub (g * z * g⁻¹) F ≠ F) : spinAction Q z ≠ 1 := by
  intro h1
  have hz' : z ∈ (spinAction Q).ker := h1
  have hc : g * z * g⁻¹ = z := by
    have := Subgroup.mem_center_iff.mp (ker_spinAction_le_center Q hz') g
    rw [this]
    group
  apply h3
  rw [hc]
  exact conjSub_eq_self_of_mem hz.mem

omit [FiniteDimensional K V] in
theorem spinAction_involution_eq {F : Subgroup (spinGroup Q)} {fr : Frame Q}
    (hodd : Odd (Nat.card K)) (hL : F.map (spinAction Q) = fr.La.range) {z : spinGroup Q}
    (hz : IsUniqueInvolution F z) (hz1 : spinAction Q z ≠ 1) :
    spinAction Q z = fr.La (-1) := by
  have hmem : spinAction Q z ∈ fr.La.range := hL ▸ Subgroup.mem_map_of_mem _ hz.mem
  have hord : orderOf (spinAction Q z) = 2 := by
    refine orderOf_eq_prime ?_ hz1
    rw [pow_two, ← map_mul, hz.sq, map_one]
  exact (IsFundamental.of_frame fr).eq_of_orderOf_eq_two hodd hmem hord

theorem e189_commute_or_proj (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) (hZ : CenterScalar Q)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q)
    {N : Subgroup (spinGroup Q)} (hN : N ≤ Subgroup.center (spinGroup Q))
    {F₁ : Subgroup (spinGroup Q)} (hF₁ : F₁ ∈ 𝓕) {z₁ g : spinGroup Q}
    (hz₁ : IsUniqueInvolution F₁ z₁) (h1 : ⁅z₁, g * z₁ * g⁻¹⁆ ∈ N)
    (h3 : conjSub (g * z₁ * g⁻¹) F₁ ≠ F₁) :
    spinAction Q z₁ * spinAction Q (g * z₁ * g⁻¹) =
        spinAction Q (g * z₁ * g⁻¹) * spinAction Q z₁ ∨
      (Module.finrank K V = 8 ∧ spinAction Q z₁ * spinAction Q (g * z₁ * g⁻¹) * spinAction Q z₁ =
        LinearEquiv.neg K * spinAction Q (g * z₁ * g⁻¹)) := by
  set π := spinAction Q with hπ
  set t₁ : spinGroup Q := g * z₁ * g⁻¹ with ht₁
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨i₁', fr₁, hL₁, hi₁'⟩ := hcorr F₁ hF₁
  have hπz₁ : π z₁ = fr₁.La (-1) :=
    spinAction_involution_eq hodd hL₁ hz₁ (spinAction_ne_one_of_moved hz₁ h3)
  have hgO : π g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := spinAction_mem_orthogonalGroup g
  have hπt₁ : π t₁ = (fr₁.map hgO).La (-1) := by
    rw [Frame.map_La, ht₁, map_mul, map_mul, map_inv, hπz₁]
  have h₂' : IsFundamental Q (fr₁.map hgO).La.range ((fr₁.map hgO).La (-1)) :=
    IsFundamental.of_frame _
  have hi₁ : π z₁ * π z₁ = 1 := by rw [← map_mul, hz₁.sq, map_one]
  have hi₂ : π t₁ * π t₁ = 1 := by rw [← map_mul, (hz₁.conj g).sq, map_one]
  have hi₁inv : (π z₁)⁻¹ = π z₁ := inv_eq_of_mul_eq_one_right hi₁
  have hi₂inv : (π t₁)⁻¹ = π t₁ := inv_eq_of_mul_eq_one_right hi₂
  have hrange := range_spinAction_eq_elementaryGroup hQ (by omega) fr₁.orth
  set c := ⁅z₁, t₁⁆ with hc
  have hcmem : π c ∈ elementaryGroup Q := by
    rw [← hrange]
    exact ⟨c, rfl⟩
  have hcenter : (⟨π c, hcmem⟩ : ↥(elementaryGroup Q)) ∈ Subgroup.center ↥(elementaryGroup Q) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : (y : V ≃ₗ[K] V) ∈ π.range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    apply Subtype.ext
    show (y : V ≃ₗ[K] V) * π c = π c * (y : V ≃ₗ[K] V)
    rw [← hx, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hN h1) x]
  obtain ⟨s, hs0⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp (hZ hcenter))
  have hs : ∀ v, (π c) v = s • v := fun v => hs0 v
  have hπc : π c = π z₁ * π t₁ * π z₁ * π t₁ := by
    rw [hc, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hi₁inv, hi₂inv]
  have h6 : ∀ u, (π t₁) ((π t₁) u) = u := fun u => by
    have := LinearEquiv.congr_fun hi₂ u
    simpa using this
  have hB : ∀ u, (π z₁ * π t₁ * π z₁) u = s • π t₁ u := by
    intro u
    have h5 := hs (π t₁ u)
    rw [hπc] at h5
    simp only [LinearEquiv.mul_apply, h6] at h5
    simpa only [LinearEquiv.mul_apply] using h5
  have hBB : (π z₁ * π t₁ * π z₁) * (π z₁ * π t₁ * π z₁) = 1 := by
    calc (π z₁ * π t₁ * π z₁) * (π z₁ * π t₁ * π z₁)
        = π z₁ * π t₁ * (π z₁ * π z₁) * π t₁ * π z₁ := by group
      _ = π z₁ * (π t₁ * π t₁) * π z₁ := by rw [hi₁, mul_one]; group
      _ = 1 := by rw [hi₂, mul_one, hi₁]
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hss : s * s = 1 := by
    have h5 := LinearEquiv.congr_fun hBB v₀
    rw [LinearEquiv.mul_apply, hB v₀, map_smul, hB (π t₁ v₀), h6, smul_smul] at h5
    have h7 : (s * s - 1) • v₀ = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr (by simpa using h5)
    rcases smul_eq_zero.mp h7 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv₀
  rcases mul_self_eq_one_iff.mp hss with hs1 | hs1
  ·
    left
    have hB1 : π z₁ * π t₁ * π z₁ = π t₁ := LinearEquiv.ext fun u => by
      rw [hB, hs1, one_smul]
    calc π z₁ * π t₁ = π z₁ * π t₁ * (π z₁ * π z₁) := by rw [hi₁, mul_one]
      _ = (π z₁ * π t₁ * π z₁) * π z₁ := by group
      _ = π t₁ * π z₁ := by rw [hB1]
  ·
    right
    have hB1 : π z₁ * π t₁ * π z₁ = LinearEquiv.neg K * π t₁ := LinearEquiv.ext fun u => by
      rw [hB, hs1, neg_one_smul]
      rfl
    have hdim1 : Module.finrank K (negSpace (π z₁ * π t₁ * π z₁)) = 4 := by
      have h5 := finrank_negSpace_of_isFundamental hodd
        (IsFundamental.conj (spinAction_mem_orthogonalGroup z₁) (hπt₁ ▸ h₂'))
      rwa [hi₁inv] at h5
    rw [hB1, negSpace_neg_mul] at hdim1
    have h5 := finrank_negSpace_add_finrank_posSpace hodd (hπt₁ ▸ h₂' : IsFundamental Q _ (π t₁))
    rw [finrank_negSpace_of_isFundamental hodd (hπt₁ ▸ h₂' : IsFundamental Q _ (π t₁)), hdim1] at h5
    exact ⟨by omega, hB1⟩

theorem e189_commute_images (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) (hdim8 : Module.finrank K V ≠ 8) (hZ : CenterScalar Q)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q)
    {N : Subgroup (spinGroup Q)} (hN : N ≤ Subgroup.center (spinGroup Q))
    {F₁ : Subgroup (spinGroup Q)} (hF₁ : F₁ ∈ 𝓕) {z₁ g : spinGroup Q}
    (hz₁ : IsUniqueInvolution F₁ z₁) (h1 : ⁅z₁, g * z₁ * g⁻¹⁆ ∈ N)
    (h3 : conjSub (g * z₁ * g⁻¹) F₁ ≠ F₁) :
    spinAction Q z₁ * spinAction Q (g * z₁ * g⁻¹) =
      spinAction Q (g * z₁ * g⁻¹) * spinAction Q z₁ := by
  rcases e189_commute_or_proj hodd hQ hdim hZ 𝓕 hcorr hN hF₁ hz₁ h1 h3 with h | ⟨h8, -⟩
  · exact h
  · exact absurd h8 hdim8

theorem e189_orth_commuting (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) (𝓕 : Set (Subgroup (spinGroup Q)))
    (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R) (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕)
    (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q)
    {N : Subgroup (spinGroup Q)} {F₁ : Subgroup (spinGroup Q)} (hF₁ : F₁ ∈ 𝓕)
    {z₁ : spinGroup Q} (hz₁ : IsUniqueInvolution F₁ z₁) {g : spinGroup Q}
    (hN : N ≤ Subgroup.center (spinGroup Q)) (h1 : ⁅z₁, g * z₁ * g⁻¹⁆ ∈ N)
    (h3 : conjSub (g * z₁ * g⁻¹) F₁ ≠ F₁) (h4 : Commutes F₁ (conjSub (g * z₁ * g⁻¹) F₁))
    (hcom : spinAction Q z₁ * spinAction Q (g * z₁ * g⁻¹) =
      spinAction Q (g * z₁ * g⁻¹) * spinAction Q z₁) :
    ∃ x : spinGroup Q, ∃ M₂ ∈ 𝓕, M₂ ≠ conjSub x F₁ ∧ Commutes (conjSub x F₁) M₂ ∧
      (∃ y, M₂ = conjSub y F₁) ∧
      ∃ z₂, IsUniqueInvolution M₂ z₂ ∧ (x * z₁ * x⁻¹)⁻¹ * z₂ ∈ N ∧
        ∀ w ∈ conjSub x F₁ ⊔ M₂, ⁅w, z₁ * (g * z₁ * g⁻¹)⁆ ∈ N := by
  set π := spinAction Q with hπ
  set t₁ : spinGroup Q := g * z₁ * g⁻¹ with ht₁
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hker : π.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  obtain ⟨i₁', fr₁, hL₁, hi₁'⟩ := hcorr F₁ hF₁
  have hπz₁ : π z₁ = fr₁.La (-1) := by
    have hmem : π z₁ ∈ fr₁.La.range := hL₁ ▸ Subgroup.mem_map_of_mem π hz₁.mem
    have hord : orderOf (π z₁) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, ← map_mul, hz₁.sq, map_one]
      · intro h1'
        have hz : z₁ ∈ π.ker := h1'
        have hc : g * z₁ * g⁻¹ = z₁ := by
          have := Subgroup.mem_center_iff.mp (hker hz) g
          rw [this]
          group
        apply h3
        rw [show t₁ = z₁ from hc]
        exact conjSub_eq_self_of_mem hz₁.mem
    exact (IsFundamental.of_frame fr₁).eq_of_orderOf_eq_two hodd hmem hord
  have hgO : π g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := spinAction_mem_orthogonalGroup g
  set fr₂ : Frame Q := fr₁.map hgO with hfr₂
  have hπt₁ : π t₁ = fr₂.La (-1) := by
    rw [hfr₂, Frame.map_La, ht₁, map_mul, map_mul, map_inv, hπz₁]
  have h₁' : IsFundamental Q fr₁.La.range (fr₁.La (-1)) := IsFundamental.of_frame fr₁
  have h₂' : IsFundamental Q fr₂.La.range (fr₂.La (-1)) := IsFundamental.of_frame fr₂
  have hcom' : fr₁.La (-1) * fr₂.La (-1) = fr₂.La (-1) * fr₁.La (-1) := by
    rw [← hπz₁, ← hπt₁]
    exact hcom
  have hi₁O : fr₁.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (h₁'.le_elementaryGroup h₁'.mem)
  have hi₂O : fr₂.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (h₂'.le_elementaryGroup h₂'.mem)
  have hperf₁ : ⁅F₁, F₁⁆ = F₁ := hperf F₁ hF₁
  have hperf₂ : ⁅conjSub t₁ F₁, conjSub t₁ F₁⁆ = conjSub t₁ F₁ := hperf _ (hconj F₁ hF₁ t₁)
  have hnn : π t₁ ∉ Subgroup.normalizer (fr₁.La.range : Set (V ≃ₗ[K] V)) := by
    intro hn
    have h5 := conjSubgroup_eq_of_mem_normalizer hn
    apply h3
    refine eq_of_map_eq_of_isPerfect π hker hperf₂ hperf₁ ?_
    have h6 : (conjSub t₁ F₁).map π = conjSubgroup (π t₁) (F₁.map π) := by
      rw [conjSubgroup_eq_map]
      exact map_conj_map π t₁ F₁
    rw [h6, hL₁, h5]
  have hodd' : Odd (Module.finrank K ↥(negSpace (π z₁) ⊓ negSpace (π t₁))) := by
    have hne : ¬ Even (Module.finrank K ↥(negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1)))) := by
      intro he
      exact hnn (by rw [hπt₁]; exact (mem_normalizer_iff_even hodd h₁' h₂' hcom').mpr he)
    rw [hπz₁, hπt₁]
    exact Nat.not_even_iff_odd.mp hne
  have ht₁sq : t₁ * t₁ = 1 := (hz₁.conj g).sq
  obtain ⟨fr₀, c, hc2, hfr₀⟩ := exists_frame_scalar_of_commuting hodd hQ hdim
    (i₁ := π z₁) (i₂ := π t₁) (spinAction_mem_orthogonalGroup z₁)
    (spinAction_mem_orthogonalGroup t₁) (by rw [← map_mul, hz₁.sq, map_one])
    (by rw [← map_mul, ht₁sq, map_one]) hcom
    (by rw [hπz₁]; exact finrank_negSpace_of_isFundamental hodd h₁')
    (by rw [hπt₁]; exact finrank_negSpace_of_isFundamental hodd h₂') hodd'
  have hperp : 2 ≤ Module.finrank K fr₁.perp := by
    have := finrank_perp_add_four fr₁
    omega
  obtain ⟨y, hy⟩ := exists_spin_conj hodd hQ fr₁ fr₀ hperp
  have hM₂mem : conjSub (y * t₁) F₁ ∈ 𝓕 := hconj F₁ hF₁ _
  have hM₂ne : conjSub (y * t₁) F₁ ≠ conjSub y F₁ := by
    intro h
    apply h3
    rw [conjSub_mul] at h
    have := congrArg (conjSub y⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hM₁perf : ⁅conjSub y F₁, conjSub y F₁⁆ = conjSub y F₁ := hperf _ (hconj F₁ hF₁ y)
  have hM₂perf : ⁅conjSub (y * t₁) F₁, conjSub (y * t₁) F₁⁆ = conjSub (y * t₁) F₁ :=
    hperf _ hM₂mem
  have hM₁img : (conjSub y F₁).map π = fr₀.La.range := by
    have h6 : (conjSub y F₁).map π = (F₁.map π).map (MulAut.conj (π y)).toMonoidHom :=
      map_conj_map π y F₁
    rw [h6, hL₁, ← La_range_eq_map_conj hy]
  set z₂ : spinGroup Q := (y * t₁) * z₁ * (y * t₁)⁻¹ with hz₂def
  have hz₂ : IsUniqueInvolution (conjSub (y * t₁) F₁) z₂ := hz₁.conj (y * t₁)
  have hc3 : π t₁ * π z₁ * (π t₁)⁻¹ = π z₁ := by
    rw [← hcom]
    group
  have hπz₂ : π z₂ = fr₀.La (-1) := by
    have h6 : π z₂ = π y * (π t₁ * π z₁ * (π t₁)⁻¹) * (π y)⁻¹ := by
      rw [hz₂def]
      simp only [map_mul, map_inv]
      group
    rw [h6, hc3, hπz₁, ← hy (-1)]
  have hM₂img : (conjSub (y * t₁) F₁).map π = fr₀.swap.La.range := by
    obtain ⟨i', fr', hL', hi'⟩ := hcorr _ hM₂mem
    have hπz₂mem : π z₂ ∈ fr'.La.range := hL' ▸ Subgroup.mem_map_of_mem π hz₂.mem
    have hord : orderOf (π z₂) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, ← map_mul, hz₂.sq, map_one]
      · rw [hπz₂]
        exact (IsFundamental.of_frame fr₀).ne_one hodd
    have hπz₂' : π z₂ = fr'.La (-1) :=
      (IsFundamental.of_frame fr').eq_of_orderOf_eq_two hodd hπz₂mem hord
    have hinv : fr'.La (-1) = fr₀.La (-1) := hπz₂'.symm.trans hπz₂
    rcases Frame.La_range_eq_or_eq_swap h2 hinv with h | h
    · exfalso
      apply hM₂ne
      refine eq_of_map_eq_of_isPerfect π hker hM₂perf hM₁perf ?_
      rw [hL', h, hM₁img]
    · rw [hL', h]
  set a : spinGroup Q := z₁ * t₁ with ha
  have hπa : π a = π z₁ * π t₁ := map_mul π z₁ t₁
  have hcomm_a : ∀ A : SL(2, K), π a * fr₀.La A = fr₀.La A * π a ∧
      π a * fr₀.swap.La A = fr₀.swap.La A * π a := by
    intro A
    refine commute_La_of_scalar_on_span h2 (spinAction_mem_orthogonalGroup a) hc2 (fun x hx => ?_) A
    rw [hπa, LinearEquiv.mul_apply]
    exact hfr₀ x hx
  have hPperf : Group.IsPerfect ↥(conjSub y F₁ ⊔ conjSub (y * t₁) F₁) := by
    apply isPerfect_of_le_commutator
    exact sup_le (hM₁perf.ge.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
      (hM₂perf.ge.trans (Subgroup.commutator_mono le_sup_right le_sup_right))
  have hPcomm : Commutes ((conjSub y F₁ ⊔ conjSub (y * t₁) F₁).map π)
      ((Subgroup.zpowers a).map π) := by
    rw [Subgroup.map_sup, hM₁img, hM₂img, MonoidHom.map_zpowers]
    have hle : fr₀.La.range ⊔ fr₀.swap.La.range ≤
        Subgroup.centralizer ((Subgroup.zpowers (π a) : Subgroup (V ≃ₗ[K] V)) : Set _) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hC : Commute (π a) (fr₀.La A) := (hcomm_a A).1
        exact (hC.zpow_left k).eq
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hC : Commute (π a) (fr₀.swap.La A) := (hcomm_a A).2
        exact (hC.zpow_left k).eq
    intro u hu v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hle hu)) v hv).symm
  have hPc := RouteD.commutes_of_commutes_map π hker hPperf hPcomm
  have hzinv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁.sq
  have hN₂ : (y * z₁ * y⁻¹)⁻¹ * z₂ ∈ N := by
    have e0 : z₁⁻¹ * t₁ * z₁ * t₁⁻¹ = ⁅z₁, t₁⁆ := by
      rw [commutatorElement_def, hzinv]
    have e1 : (y * z₁ * y⁻¹)⁻¹ * z₂ = y * (z₁⁻¹ * t₁ * z₁ * t₁⁻¹) * y⁻¹ := by
      rw [hz₂def]
      group
    rw [e0] at e1
    have e2 : y * ⁅z₁, t₁⁆ * y⁻¹ = ⁅z₁, t₁⁆ :=
      mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp (hN h1) y)
    rw [e1, e2]
    exact h1
  refine ⟨y, conjSub (y * t₁) F₁, hM₂mem, hM₂ne, ?_, ⟨y * t₁, rfl⟩, z₂, hz₂, hN₂, ?_⟩
  · rw [conjSub_mul]
    exact h4.conjSub y
  · intro w hw
    have hwa : w * a = a * w := hPc w hw a (Subgroup.mem_zpowers a)
    have : ⁅w, z₁ * t₁⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hwa
    rw [this]
    exact N.one_mem

theorem e189AtFam_spin_of_ne8 (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) (hdim8 : Module.finrank K V ≠ 8) (hZ : CenterScalar Q)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕) (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q) :
    E189AtFam (spinGroup Q) 𝓕 := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 _ h3 h4 _
  right
  exact e189_orth_commuting hodd hQ hdim 𝓕 hperf hconj hcorr hF₁ hz₁ hN h1 h3 h4
    (e189_commute_images hodd hQ hdim hdim8 hZ 𝓕 hcorr hN hF₁ hz₁ h1 h3)

theorem e189AtFam_spin_of_noOrth (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) (hZ : CenterScalar Q)
    (hNoOrth : ∀ F₀ F₁ : Frame Q, F₁.span ≤ F₀.perp → False)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕) (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q) :
    E189AtFam (spinGroup Q) 𝓕 := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 _ h3 h4 _
  right
  rcases e189_commute_or_proj hodd hQ hdim hZ 𝓕 hcorr hN hF₁ hz₁ h1 h3 with hc | ⟨-, hB1⟩
  · exact e189_orth_commuting hodd hQ hdim 𝓕 hperf hconj hcorr hF₁ hz₁ hN h1 h3 h4 hc
  · exfalso
    have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
    obtain ⟨i₁', fr₁, hL₁, hi₁'⟩ := hcorr F₁ hF₁
    have hπz₁ : spinAction Q z₁ = fr₁.La (-1) :=
      spinAction_involution_eq hodd hL₁ hz₁ (spinAction_ne_one_of_moved hz₁ h3)
    have hO := spinAction_mem_orthogonalGroup (Q := Q) (g * z₁ * g⁻¹)
    refine hNoOrth fr₁ (fr₁.map hO) ?_
    rintro _ ⟨X, rfl⟩
    rw [Frame.map_incl, Frame.mem_perp_iff_fix fr₁ h2, ← hπz₁]
    have hx : fr₁.incl X ∈ fr₁.span := ⟨X, rfl⟩
    have e1 : spinAction Q z₁ (fr₁.incl X) = -(fr₁.incl X) := by
      rw [hπz₁]
      exact (Frame.mem_span_iff_inv fr₁ h2).mp hx
    have e2 := LinearEquiv.congr_fun hB1 (fr₁.incl X)
    simp only [LinearEquiv.mul_apply, e1, map_neg, LinearEquiv.neg_apply] at e2
    exact neg_injective e2

end CFSG.ClassicalInvolution.Asc77
