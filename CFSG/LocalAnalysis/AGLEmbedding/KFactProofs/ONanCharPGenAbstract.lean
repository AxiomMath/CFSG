module

public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.AGLEmbedding.CharPGen

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem glbCore_posUnipotent_eq_top
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) :
    GLBCore p 1 (posUnipotent D) = ⊤ := by
  have hU : IsPGroup p (posUnipotent D) := isPGroup_iSup_pos hext hX
  have hUne : posUnipotent D ≠ ⊥ := by
    intro h
    refine hext.ne_bot (Pi.single ⟨0, by omega⟩ 1)
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem ⟨0, by omega⟩) ?_
    rw [eq_bot_iff, ← h]
    exact rootGroup_le_posUnipotent
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem ⟨0, by omega⟩)
      (ht_single_pos _)
  have hB : borel D H ≤ GLBCore p 1 (posUnipotent D) :=
    (borel_le_normalizer_posUnipotent hct).trans
      (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 le_rfl
        (one_le_pRank_of_isPGroup_of_ne_bot hp hU hUne))
  have hn : ∀ i, n i ∈ GLBCore p 1 (posUnipotent D) := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin D.rank, j ≠ i := by
      by_cases hi : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hi; simp at hi⟩
      · exact ⟨⟨0, by omega⟩, fun h => hi (by rw [← h])⟩
    have hjmem : (Pi.single j 1 : Fin D.rank → ℤ) ∈
        (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j) hji (by simp)
    have hQ : posUnipotentExcept D i ≤ posUnipotent D := posUnipotentExcept_le_posUnipotent i
    have hQne : posUnipotentExcept D i ≠ ⊥ := by
      intro h
      refine hext.ne_bot (Pi.single j 1)
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j) ?_
      rw [eq_bot_iff, ← h]
      exact rootGroup_le_posUnipotentExcept hjmem
    have hnorm : n i ∈ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
      Subgroup.mem_normalizer_fintype fun u hu => conj_n_mem_posUnipotentExcept hct i hu
    exact CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 hQ
      (one_le_pRank_of_isPGroup_of_ne_bot hp (hU.to_le hQ) hQne) hnorm
  rw [eq_top_iff, ← closure_borel_union_range hct]
  exact (Subgroup.closure_le _).2 (Set.union_subset hB (Set.range_subset_iff.2 hn))

theorem eq_one_of_pow_char_pow_eq_one {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {c : F} {k : ℕ} (h : c ^ p ^ k = 1) : c = 1 := by
  have h1 : (c - 1) ^ p ^ k = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero) |>.1 h1)

theorem eq_one_of_mem_statedScalars_of_pow {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] {H : Subgroup (GL ι F)} {x : H}
    (hx : (x : GL ι F) ∈ CFSG.Assembly.LowTwoRank.StatedScalars ι F) {k : ℕ}
    (hk : x ^ p ^ k = 1) : x = 1 := by
  obtain ⟨c, hc⟩ := hx
  have h1 : Matrix.GeneralLinearGroup.scalar ι (c ^ p ^ k) = 1 := by
    rw [map_pow, hc]
    exact congrArg Subtype.val hk
  have h2 := congrArg (fun g : GL ι F => (g : Matrix ι ι F) i i) h1
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq, Units.val_pow_eq_pow_val] at h2
  have hc1 : c = 1 := Units.ext (eq_one_of_pow_char_pow_eq_one h2)
  exact Subtype.ext (by rw [← hc, hc1, map_one]; rfl)

theorem ne_bot_of_one_le_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 2 ≤ p)
    {Q : Subgroup G} (h : 1 ≤ Open.pRank p Q) : Q ≠ ⊥ := by
  rintro rfl
  have h0 : Open.pRank p (⊥ : Subgroup G) ≤ 0 := by
    refine csSup_le' ?_
    rintro k ⟨E, hE, -, hcard⟩
    rw [le_bot_iff.1 hE, Subgroup.card_bot] at hcard
    by_contra hk
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) (by omega)
    omega
  omega

theorem glbCore_map_eq_top {G L : Type*} [Group G] [Finite G] [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (f : G →* L) (hf : Function.Surjective f) {P : Subgroup G}
    (hP : IsPGroup p P) (hinj : ∀ x ∈ P, f x = 1 → x = 1) (hcore : GLBCore p 1 P = ⊤) :
    GLBCore p 1 (P.map f) = ⊤ := by
  have hle : GLBCore p 1 P ≤ (GLBCore p 1 (P.map f)).comap f := by
    rw [CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff]
    intro Q hQP hQ1 g hg
    have hQne : Q ≠ ⊥ := ne_bot_of_one_le_pRank hp.two_le hQ1
    obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
    have hfne : Q.map f ≠ ⊥ := by
      intro h
      have : f q ∈ Q.map f := ⟨q, hq, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact hq1 (Subtype.ext (hinj q (hQP hq) this))
    have hQp : IsPGroup p (Q.map f) := ((hP.to_le hQP).map f)
    exact CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 (Subgroup.map_mono hQP)
      (one_le_pRank_of_isPGroup_of_ne_bot hp hQp hfne) (Subgroup.le_normalizer_map f ⟨g, hg, rfl⟩)
  rw [eq_top_iff]
  intro l _
  obtain ⟨g, rfl⟩ := hf l
  exact hle (hcore ▸ Subgroup.mem_top g)

end CFSG.AGLEmbedding.CharPGen
