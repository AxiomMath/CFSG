module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T4
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.Adapters.LinearCatalog
public import CFSG.Adapters.ClassicalCatalogReverse
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S9 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Adapters.RankTwoModelTransports
open CFSG.LocalAnalysis.GLTheoremA.CatB

theorem linear3_index_valid (f : ℕ) (hf : 2 ≤ f) (hp : Nat.Prime 2) (hadm : StatedLieAdmissible .PSL 3 2 f) :
    (LieTypeIndex.A 2 ⟨2, f, hp, by omega⟩).Valid := by
  apply CFSG.ClassicalModels.linearCatalog_index_valid 3 2 f hadm
  rw [LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [PrimePower.card_def]
  intro hdup
  rcases hdup with ⟨hr, -⟩ | ⟨hr, hq⟩ | ⟨hr, hq⟩
  · omega
  · have : (2 : ℕ) ^ f = 2 := hq
    have hf1 : f = 1 := Nat.pow_right_injective le_rfl (this.trans (pow_one 2).symm)
    omega
  · omega


theorem catalogIs_isL3char2_of_statedPSL {R : Type} [Group R] {f : ℕ} (hf : 2 ≤ f) (hfe : Even f)
    (h : StatedClassicalModel R .PSL 3 2 f) : catalogIs R S9.isL3char2 := by
  have hadm : StatedLieAdmissible .PSL 3 2 f := h.1
  obtain ⟨K, hfield, hfinite, hKcard, e⟩ := h.2
  obtain ⟨e⟩ := e
  let _ := hfield
  let _ := hfinite
  have hp : Nat.Prime 2 := Nat.prime_two
  let _ : Fact (Nat.Prime 2) := ⟨hp⟩
  let q : PrimePower := ⟨2, f, hp, by omega⟩
  have hv : (LieTypeIndex.A 2 q).Valid := linear3_index_valid f hf hp hadm
  have hmod : (2 : ℕ) ^ f % 3 = 1 := by
    obtain ⟨j, hj⟩ := hfe
    rw [hj, ← two_mul, pow_mul]
    norm_num [Nat.pow_mod]
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 2 f (by omega) hKcard
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv
  refine ⟨.lie ⟨_, hv⟩, ?_, ⟨(e.trans eK).trans eC.symm⟩⟩
  show q.p = 2 ∧ q.card % 3 = 1
  refine ⟨rfl, ?_⟩
  rw [PrimePower.card_def]
  exact hmod


theorem catalogIs_isU3char2_of_statedPSU {R : Type} [Group R] {f : ℕ} (hf : 3 ≤ f) (hfo : f % 2 = 1)
    (h : StatedClassicalModel R .PSU 3 2 f) : catalogIs R S9.isU3char2 := by
  have hadm : StatedLieAdmissible .PSU 3 2 f := h.1
  obtain ⟨K, hfield, hfinite, hK, ⟨e⟩⟩ := h.2
  let _ := hfield
  let _ := hfinite
  have hp : Nat.Prime 2 := Nat.prime_two
  let _ : Fact (Nat.Prime 2) := ⟨hp⟩
  have hv := CFSG.ClassicalModels.unitaryCatalog_index_valid 3 2 f hadm
  let q : PrimePower := ⟨2, f, hp, by omega⟩
  let L := GaloisField 2 (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 3) φ) (glCongr_statedSU φ 3 (2 ^ f))
    (glCongr_statedScalars φ)
  have hv' : (LieTypeIndex.twistedA 2 q).Valid := hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv'
  refine ⟨.lie ⟨_, hv'⟩, ?_, ⟨(e.trans e1).trans eT.symm⟩⟩
  show q.p = 2 ∧ q.card % 3 = 2
  refine ⟨rfl, ?_⟩
  rw [PrimePower.card_def]
  have hmod : (2 : ℕ) ^ f % 3 = 2 := by
    obtain ⟨j, hj⟩ : ∃ j, f = 2 * j + 1 := ⟨f / 2, by omega⟩
    rw [hj, pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  exact hmod

theorem catalogIs_isSp4eight_of_statedPSp {R : Type} [Group R] (h : StatedClassicalModel R .PSp 2 2 3) :
    catalogIs R S9.isSp4eight := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : Nat.Prime 2 := Nat.prime_two
  let q : PrimePower := ⟨2, 3, hp, by norm_num⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hq2 : (2 : ℕ) ^ 3 ≠ 2 := by norm_num
  have hv : (LieTypeIndex.B 2 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [PrimePower.card_def, true_and, le_refl]
    exact ⟨hq2, by norm_num⟩
  let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)
  have _ : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  let _ : Fintype Fd := Fintype.ofFinite Fd
  have hcard : Fintype.card K = Fintype.card Fd := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, q]
  let φ : K ≃+* Fd := FiniteField.ringEquivOfCardEq hcard
  let e1 := CFSG.ComponentClassification.ClassicalModelStatedBridge.statedProjCongr
    (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) φ)
    (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedSp 2 φ)
    (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedScalars φ)
  let eT := CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv
  refine ⟨.lie ⟨_, hv⟩, ?_, ⟨(θ.trans e1).trans eT.symm⟩⟩
  show q.card = 8
  rw [PrimePower.card_def]
  norm_num


theorem two_pow_mod_three_even {k : ℕ} (hk : Even k) : (2 : ℕ) ^ k % 3 = 1 := by
  obtain ⟨j, hj⟩ := hk
  rw [hj, ← two_mul, pow_mul]
  norm_num [Nat.pow_mod]

theorem two_pow_mod_three_odd {k : ℕ} (hk : Odd k) : (2 : ℕ) ^ k % 3 = 2 := by
  obtain ⟨j, hj⟩ := hk
  rw [hj, pow_succ, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

theorem lieModel_of_catalogIs_isL3char2 {R : Type} [Group R] (hc : catalogIs R S9.isL3char2) :
    ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ CFSG.Blueprint.LieModel R .PSL 3 2 k := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hc
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    · have hm := CFSG.Models.lieModel_A 2 q hv e
      have hq := hP.2
      have hev : Even q.exponent := by
        by_contra hodd
        have hodd' : Odd q.exponent := Nat.not_even_iff_odd.1 hodd
        have h2 : (2 : ℕ) ^ q.exponent % 3 = 2 := two_pow_mod_three_odd hodd'
        have hcard : q.card = 2 ^ q.exponent := by
          rw [PrimePower.card_def, hP.1]
        rw [hcard] at hq
        omega
      have hpos : 1 ≤ q.exponent := q.exponent_pos
      have hm' := hm.toBlueprint (by decide)
      rw [hP.1] at hm'
      refine ⟨q.exponent, ?_, hev, ?_⟩
      · obtain ⟨j, hj⟩ := hev
        omega
      · exact hm'
  | _ => exact hP.elim

theorem catalogIs_isL3char2_of_lieModel {R : Type} [Group R] {f : ℕ} (hf : 2 ≤ f) (hfe : Even f)
    (h : CFSG.Blueprint.LieModel R .PSL 3 2 f) : catalogIs R S9.isL3char2 := by
  rcases h with ⟨-, hS⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact catalogIs_isL3char2_of_statedPSL hf hfe hS
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem catalogIs_isU3char2_of_lieModel {R : Type} [Group R] {f : ℕ} (hf : 2 ≤ f) (hfo : Odd f)
    (h : CFSG.Blueprint.LieModel R .PSU 3 2 f) : catalogIs R S9.isU3char2 := by
  rcases h with ⟨-, hS⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact catalogIs_isU3char2_of_statedPSU (by obtain ⟨j, hj⟩ := hfo; omega) (Nat.odd_iff.1 hfo) hS
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem tag_of_marksA2 {k : ℕ} (lab : LargeEvenLabel) (ht : markTag lab = .PSL)
    (hr : markRank lab = 3) (hn : markDeg lab = k) (h2 : markChar lab = 2) :
    lab.tag = .A ∧ lab.rank = 2 ∧ lab.n = k := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp [markTag, markRank, markDeg, markChar] at ht hr hn h2 ⊢
  all_goals first
    | exact ⟨hr, hn⟩
    | (by_cases h3 : rank = 3 <;> by_cases h2' : rank = 2 <;> simp_all)

theorem tag_of_marksU2 {k : ℕ} (lab : LargeEvenLabel) (ht : markTag lab = .PSU)
    (hr : markRank lab = 3) (hn : markDeg lab = k) (h2 : markChar lab = 2) :
    lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = k := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp [markTag, markRank, markDeg, markChar] at ht hr hn h2 ⊢
  all_goals first
    | exact ⟨hr, hn⟩
    | (by_cases h3 : rank = 3 <;> by_cases h2' : rank = 2 <;> simp_all)

section Certified


theorem label_of_markedModel_L3 {lab : LargeEvenLabel} {R : Type} [Group R] {k : ℕ} (hk : 2 ≤ k)
    (hM : MarkedModel lab R) (hX : CFSG.Blueprint.LieModel R .PSL 3 2 k) :
    lab.tag = .A ∧ lab.rank = 2 ∧ lab.n = k := by
  by_cases h2 : markChar lab = 2
  · have hM' : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
      have := hM
      unfold MarkedModel at this
      rwa [h2] at this
    obtain ⟨ht, hr, hn⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) hX hM'
    exact tag_of_marksA2 lab ht hr hn h2
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
      (by simp) (by rintro ⟨-, -, h⟩; omega) (by simp) hodd

theorem label_of_markedModel_U3 {lab : LargeEvenLabel} {R : Type} [Group R] {k : ℕ}
    (hM : MarkedModel lab R) (hX : CFSG.Blueprint.LieModel R .PSU 3 2 k) :
    lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = k := by
  by_cases h2 : markChar lab = 2
  · have hM' : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
      have := hM
      unfold MarkedModel at this
      rwa [h2] at this
    obtain ⟨t1, t2, t3⟩ :=
      CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet R k _ _ _ hX hM'.admissible hM'
    exact tag_of_marksU2 lab t1 t2 t3 h2
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
