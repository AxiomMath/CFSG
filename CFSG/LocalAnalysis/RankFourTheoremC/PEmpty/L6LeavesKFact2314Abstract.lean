module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieWeakCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParND
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ClassicalInvolution.ModelFacts.RootLength
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Statements
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

theorem not_isCyclic_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {R X Y : Subgroup G} (hR : IsPGroup p R) (hXR : X ≤ R) (hYR : Y ≤ R) (hX : X ≠ ⊥)
    (hY : Y ≠ ⊥) (hXY : X ⊓ Y = ⊥) : ¬ IsCyclic R := by
  intro hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  have key : ∀ A B : Subgroup G, A ≤ R → B ≤ R → Nat.card A ≤ Nat.card B → A ≤ B := by
    intro A B hAR hBR hcard
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hR.to_le hAR)
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 (hR.to_le hBR)
    have hab : a ≤ b := by
      rw [ha, hb] at hcard
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
    have hdvd : Nat.card (A.subgroupOf R) ∣ Nat.card (B.subgroupOf R) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBR).toEquiv, ha, hb]
      exact pow_dvd_pow p hab
    intro x hx
    have h1 : (⟨x, hAR hx⟩ : R) ∈ A.subgroupOf R := Subgroup.mem_subgroupOf.2 hx
    exact Subgroup.mem_subgroupOf.1 (IsCyclic.subgroup_le_iff_card_dvd.2 hdvd h1)
  rcases le_total (Nat.card X) (Nat.card Y) with h | h
  · exact hX (by rw [← inf_eq_left.2 (key X Y hXR hYR h), hXY])
  · exact hY (by rw [← inf_eq_right.2 (key Y X hYR hXR h), hXY])

theorem two_le_pRank_of_not_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {R : Subgroup G} (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) :
    2 ≤ CFSG.Open.pRank p R := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p R) := ⟨hR⟩
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hE : CFSG.Open.IsElemAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hel
  have hE' : CFSG.Open.IsElemAbelian p (E.map R.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE R.subtype
  have hcard' : Nat.card (E.map R.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hcard]
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_subtype_le E) hE' hcard'

section Abstract

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem two_le_pRank_posUnipotentExcept (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) {i j : Fin D.rank}
    (hji : j ≠ i) (hij : D.cartan i j ≠ 0) :
    2 ≤ CFSG.Open.pRank p (posUnipotentExcept D i) := by
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hβ : reflection D.cartan i (Pi.single j 1) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i _ hα
  have hαj : (Pi.single j 1 : Fin D.rank → ℤ) j = 1 := by simp
  have hβj : reflection D.cartan i (Pi.single j 1) j = 1 := by
    rw [reflection_apply_of_ne D.cartan hji, hαj]
  have hαi : (Pi.single j 1 : Fin D.rank → ℤ) i = 0 := by simp [Pi.single_apply, hji.symm]
  have hβi : reflection D.cartan i (Pi.single j 1) i = - D.cartan i j := by
    rw [reflection_apply_coroot, Pi.sub_apply, hαi, coroot_single]
    simp
  have hαmem : (Pi.single j 1 : Fin D.rank → ℤ) ∈
      (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos hα hji
      (by rw [hαj]; exact one_pos)
  have hβmem : reflection D.cartan i (Pi.single j 1) ∈
      (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos hβ hji
      (by rw [hβj]; exact one_pos)
  have hne : (Pi.single j 1 : Fin D.rank → ℤ) ≠ reflection D.cartan i (Pi.single j 1) := by
    intro h
    have := congrFun h i
    rw [hαi, hβi] at this
    exact hij (by omega)
  have hd1 : ∀ δ ∈ D.roots, (Pi.single j 1 : Fin D.rank → ℤ) ≠ 2 • δ := by
    intro δ _ h
    have := congrFun h j
    simp only [hαj, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this
    omega
  have hd2 : ∀ δ ∈ D.roots, reflection D.cartan i (Pi.single j 1) ≠ 2 • δ := by
    intro δ _ h
    have := congrFun h j
    simp only [hβj, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this
    omega
  have hinf := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.rootGroup_inf_eq_bot hext hα hβ
    hαmem.1.2 hβmem.1.2 hd1 hd2 hne
  have hU : IsPGroup p (posUnipotent D) := isPGroup_iSup_pos hext hX
  have hU' : IsPGroup p (posUnipotentExcept D i) :=
    hU.to_le (posUnipotentExcept_le_posUnipotent i)
  exact two_le_pRank_of_not_isCyclic hp hp2 hU' <|
    not_isCyclic_of_inf_eq_bot hp hU'
      (rootGroup_le_posUnipotentExcept hαmem) (rootGroup_le_posUnipotentExcept hβmem)
      (hext.ne_bot _ hα) (hext.ne_bot _ hβ) hinf

theorem glbCore_two_posUnipotent_eq_top
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hadj : ∀ i, ∃ j, j ≠ i ∧ D.cartan i j ≠ 0) :
    GLBCore p 2 (posUnipotent D) = ⊤ := by
  have h2 : ∀ i, 2 ≤ CFSG.Open.pRank p (posUnipotentExcept D i) := fun i => by
    obtain ⟨j, hji, hij⟩ := hadj i
    exact two_le_pRank_posUnipotentExcept hext hp hp2 hX hji hij
  have hU2 : 2 ≤ CFSG.Open.pRank p (posUnipotent D) :=
    (h2 ⟨0, by omega⟩).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt (posUnipotentExcept_le_posUnipotent _))
  have hB : borel D H ≤ GLBCore p 2 (posUnipotent D) :=
    (borel_le_normalizer_posUnipotent hct).trans
      (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2 le_rfl hU2)
  have hn : ∀ i, n i ∈ GLBCore p 2 (posUnipotent D) := fun i =>
    CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2 (posUnipotentExcept_le_posUnipotent i) (h2 i)
      (Subgroup.mem_normalizer_fintype fun u hu => conj_n_mem_posUnipotentExcept hct i hu)
  rw [eq_top_iff, ← closure_borel_union_range hct]
  exact (Subgroup.closure_le _).2 (Set.union_subset hB (Set.range_subset_iff.2 hn))

end Abstract

theorem glbCore_map_eq_top_of_injOn {G L : Type*} [Group G] [Finite G] [Group L] [Finite L]
    {p k : ℕ} (hp : p.Prime) (f : G →* L) (hf : Function.Surjective f) {P : Subgroup G}
    (hinj : ∀ x ∈ P, f x = 1 → x = 1) (hcore : GLBCore p k P = ⊤) :
    GLBCore p k (P.map f) = ⊤ := by
  have hle : GLBCore p k P ≤ (GLBCore p k (P.map f)).comap f := by
    rw [CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff]
    intro Q hQP hQk g hg
    exact CFSG.AGLEmbeddingD2.normalizer_le_glbCore p k (Subgroup.map_mono hQP)
      (hQk.trans (CFSG.AGLEmbedding.P1Lie.pRank_le_pRank_map hp f hinj hQP))
      (Subgroup.le_normalizer_map f ⟨g, hg, rfl⟩)
  rw [eq_top_iff]
  intro l _
  obtain ⟨g, rfl⟩ := hf l
  exact hle (hcore ▸ Subgroup.mem_top g)

theorem exists_adj_of_isIrreducible {m : ℕ} {A : Matrix (Fin m) (Fin m) ℤ}
    (hirr : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible A) (hm : 2 ≤ m) (i : Fin m) :
    ∃ j, j ≠ i ∧ A i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hall := hirr {i} ⟨i, rfl⟩ (fun k hk j hkj => by
    have hk' : k = i := hk
    subst hk'
    by_contra hji
    exact hkj (hcon j hji))
  obtain ⟨j, hji⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases hi : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hi; simp at hi⟩
    · exact ⟨⟨0, by omega⟩, fun h => hi (by rw [← h])⟩
  exact hji (Set.mem_singleton_iff.1 (hall j))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314
