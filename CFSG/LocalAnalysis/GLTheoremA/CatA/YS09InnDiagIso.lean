module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial

private theorem indAut_zpow {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (k : ℤ)
    (hk : y ^ k ∈ Subgroup.normalizer (L : Set G)) :
    MI.indAut p L (y ^ k) hk = (MI.indAut p L y hy) ^ k := by
  unfold MI.indAut
  rw [← map_zpow]
  congr 1
  apply Subtype.ext
  simp [zpow_neg, inv_zpow']

theorem innDiagIsoAt_holds (G : Type) [Group G] [Finite G] (p : ℕ) : InnDiagIsoAt G p := by
  intro X X' J K y e hJ hK hch hyJ hyK hpres hdiag
  obtain ⟨hdJ, hcomm, lab, hlab, hraw⟩ := hdiag
  have hqK := MI.isQuasisimple_pQuot_any hK
  refine ⟨Subgroup.zpowers_le.2 hyK, ?_, lab, hlab, ?_⟩
  · exact hqK.1
  · refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    refine ⟨hs, hna, e.symm.trans θ, ?_⟩
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hθ a ha
    refine ⟨φ, hφI, ?_⟩
    have haJ : a ∈ Subgroup.normalizer (J : Set G) := hdJ ha
    have haK : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.2 hyK ha
    have key : MI.indAut p K y hyK = MulAut.congr e (MI.indAut p J y hyJ) := by
      refine MulEquiv.ext fun s => ?_
      obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm s)
      have hs : s = e (QuotientGroup.mk q) := by rw [hq, MulEquiv.apply_symm_apply]
      obtain ⟨q', hq'⟩ := MI.indRel_total (p := p) (L := J) hyJ q
      have h1 := MI.indAut_apply_mk hyJ hq'
      have h2 : indRelS p J y (QuotientGroup.mk q) (QuotientGroup.mk q') := ⟨q, q', hq', rfl, rfl⟩
      obtain ⟨r, r', hrr', hr, hr'⟩ := hpres _ _ h2
      have h4 := MI.indAut_apply_mk hyK hrr'
      rw [hs, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, h1, ← hr, h4, hr']
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hKa : MI.indAut p K (y ^ k) haK = MulAut.congr e (MI.indAut p J (y ^ k) haJ) := by
      rw [indAut_zpow hyK k haK, indAut_zpow hyJ k haJ, key, map_zpow]
    have hφ' := (MI.induces_indRel_iff (p := p) haJ θ).1 hφ
    refine (MI.induces_indRel_iff (p := p) haK (e.symm.trans θ)).2 ?_
    rw [hφ', hKa]
    ext r
    simp [MulAut.congr_apply]

private theorem pow_eq_one_of_mem_field_unitary {K : Type} [Field K] [Finite K] {d n : ℕ}
    (h : UnitaryFieldData 2 n K) (hd : 1 ≤ d) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    φ ^ (2 * n) = 1 := by
  obtain ⟨σ, hσ⟩ := RecipeFieldSU.congr_field_eq h hd hφ
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK'
  have hσm : σ ^ (2 * n) = 1 := hcard ▸ pow_card_eq_one'
  apply (MulAut.congr (InndiagSU.projEquiv h hd)).injective
  rw [map_pow, hσ, ← map_pow, hσm, map_one, map_one]

private theorem tag_of_marks6 {m : ℕ} (lab : LargeEvenLabel) (ht : markTag lab = .PSU)
    (hr : markRank lab = 6) (hn : markDeg lab = m) (h2 : markChar lab = 2) :
    lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = m := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp [markTag, markRank, markDeg, markChar] at ht hr hn h2 ⊢
  all_goals first
    | exact ⟨hr, hn⟩
    | (by_cases h3 : rank = 3 <;> by_cases h2' : rank = 2 <;> simp_all)

private theorem recipe_of_label6 {m : ℕ} {lab : LargeEvenLabel}
    (h : lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = m)
    {Q : LargeEvenRawCont} (hraw : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    LargeEvenRecipeUnitary (5 + 1) (2 ^ m) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  subst h1 h2 h3
  exact hraw

section Certified


private theorem label_of_markedModel6 {lab : LargeEvenLabel} {R : Type} [Group R] {m : ℕ}
    (hM : MarkedModel lab R) (hX : CFSG.Blueprint.LieModel R .PSU 6 2 m) :
    lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = m := by
  by_cases h2 : markChar lab = 2
  · have hM' : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
      have := hM
      unfold MarkedModel at this
      rwa [h2] at this
    obtain ⟨ht, hr, hn⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq (by norm_num) hX hM' rfl
    exact tag_of_marks6 lab ht hr hn h2
  · exfalso
    have hodd : CFSG.Blueprint.OddLieType R := by
      obtain ⟨tag, rank, n⟩ := lab
      cases tag <;> simp [markChar] at h2
      · have h : CFSG.Blueprint.LieModel R .PSL 2 3 2 := hM
        exact ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num,
          CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h, h⟩
      · have h : CFSG.Blueprint.LieModel R .PSU 3 3 1 := hM
        exact ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num,
          CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h, h⟩
    exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits hX (by decide)
      (by simp) (by simp) (by simp) hodd


theorem fieldU6ExpAt_holds (G : Type) [Group G] [Finite G] : FieldU6ExpAt G := by
  intro X L g m hL hFO hcat
  obtain ⟨-, lab, hlab, hraw⟩ := Canonical.largeEvenMarking_markedModel hFO.2
  have hX : CFSG.Blueprint.LieModel (PSimple 3 L) .PSU 6 2 m := by
    obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hcat
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      all_goals first | exact hP.elim | skip
      · have hm := lieModel_twistedA' 5 q hv e
        rw [hP.1, hP.2] at hm
        exact CFSG.Models.LieModel.toBlueprint (by decide) hm
    | _ => exact hP.elim
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, -, hM₀⟩ := hQ₀
  have hM : MarkedModel lab (PSimple 3 L) := MarkedModel.of_mulEquiv θ₀.symm hM₀
  have hlabel := label_of_markedModel6 hM hX
  have hm1 : 1 ≤ m := hlabel.2.2 ▸ hlab.1
  obtain ⟨K', _, _, hK', hQ⟩ := recipe_of_label6 hlabel hraw
  obtain ⟨hs, hna, θ, ⟨-, f, hf, u, hu, hord, hα⟩, -⟩ := hQ
  have hKc : Nat.card K' = (2 ^ m) ^ 2 := hK'
  have hUFD : UnitaryFieldData 2 m K' :=
    ⟨Nat.prime_two, hm1, by rw [hKc, ← pow_mul, mul_comm]⟩
  haveI := hUFD.finite
  have hf6 := pow_eq_one_of_mem_field_unitary hUFD (by norm_num) hm1 hKc hf
  have h3 : 3 ∣ 2 * m := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hf6
  omega

end Certified

end CFSG.LocalAnalysis.GLTheoremA
