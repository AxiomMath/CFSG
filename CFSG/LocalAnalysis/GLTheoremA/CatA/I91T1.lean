module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRRes168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XAsm2
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.Adapters.RankTwoModelTransports

theorem psu6_index {R : Type} [Group R] {p f : ℕ} (hadm : StatedLieAdmissible .PSU 6 p f)
    (h : StatedClassicalModel R .PSU 6 p f) :
    ∃ hv : (LieTypeIndex.twistedA 5 ⟨p, f, hadm.1, by have hf := hadm.2.1; omega⟩).Valid,
      Nonempty (R ≃* (CFSGIndex.lie ⟨_, hv⟩).Group) := by
  obtain ⟨hadm', K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hv := CFSG.ClassicalModels.unitaryCatalog_index_valid 6 p f hadm
  let _ : Fact p.Prime := ⟨hp⟩
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  let L := GaloisField p (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 6) φ) (glCongr_statedSU φ 6 (p ^ f))
    (glCongr_statedScalars φ)
  have hv' : (LieTypeIndex.twistedA 5 q).Valid := hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv'
  exact ⟨hv', ⟨(e.trans e1).trans eT.symm⟩⟩

theorem catalogIs_isU6n_of_lieModel {R : Type} [Group R] {m : ℕ} (hm : 1 ≤ m)
    (h : CFSG.Blueprint.LieModel R .PSU 6 2 m) : catalogIs R (isU6n m) := by
  rcases h with ⟨-, hS⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · obtain ⟨hv, ⟨e⟩⟩ := psu6_index hS.1 hS
    exact ⟨.lie ⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem lieModel_of_catalogIs_isU6n {R : Type} [Group R] {m : ℕ}
    (hcat : catalogIs R (isU6n m)) : CFSG.Blueprint.LieModel R .PSU 6 2 m := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex hcat
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    · have hm := lieModel_twistedA' 5 q hv e
      rw [hP.1, hP.2] at hm
      exact CFSG.Models.LieModel.toBlueprint (by decide) hm
  | _ => exact hP.elim


theorem tag_of_marks6 {m : ℕ} (lab : LargeEvenLabel) (ht : markTag lab = .PSU)
    (hr : markRank lab = 6) (hn : markDeg lab = m) (h2 : markChar lab = 2) :
    lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = m := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp [markTag, markRank, markDeg, markChar] at ht hr hn h2 ⊢
  all_goals first
    | exact ⟨hr, hn⟩
    | (by_cases h3 : rank = 3 <;> by_cases h2' : rank = 2 <;> simp_all)

section Certified


theorem label_of_markedModel6 {lab : LargeEvenLabel} {R : Type} [Group R] {m : ℕ}
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

end Certified

end I91T

end CFSG.LocalAnalysis.GLTheoremA
