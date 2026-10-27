module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Fam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSpin
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Abstract

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

theorem exists_pGroup2_of_spin {G : Type} [Group G] [Finite G] {σ : Type} [Fintype σ]
    [DecidableEq σ] {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (i : σ) {Q : QuadraticForm F (σ → F)} {Q₀ : (σ → F) → F}
    (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hker : ∀ x ∈ (spinMatrix Q).ker, x ^ 2 = 1) [Finite (spinGroup Q)]
    {D : UniversalRootDatum (spinGroup Q)} {n : Fin D.rank → spinGroup Q}
    {H : Fin D.rank → Subgroup (spinGroup Q)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hadj : ∀ i, ∃ j, j ≠ i ∧ D.cartan i j ≠ 0) (e : G ≃* StatedProj (StatedOmega Q₀)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  have hU : IsPGroup p (posUnipotent D) := isPGroup_iSup_pos hext hX
  let π : spinGroup Q →* G := e.symm.toMonoidHom.comp (spinToStatedProj Q hR)
  have hπ : Function.Surjective π := e.symm.surjective.comp (spinToStatedProj_surjective Q hR)
  have hinj : ∀ x ∈ posUnipotent D, π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : spinToStatedProj Q hR x = 1 := e.symm.injective (by rw [map_one]; exact hx1)
    have hsc : spinMatrix Q x ∈ StatedScalars σ F :=
      Subgroup.mem_comap.1 ((ker_spinToStatedProj Q hR).le (MonoidHom.mem_ker.2 hmk))
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
    have hm1 : spinMatrix Q x = 1 :=
      CFSG.AGLEmbedding.CharPGen.eq_one_of_mem_statedScalars_of_pow_gl i hsc
        (by rw [← map_pow, hk', map_one])
    exact CFSG.AGLEmbedding.CharPGen.eq_one_of_sq_eq_one_of_pow_prime_pow hp2
      (hker x (MonoidHom.mem_ker.2 hm1)) hk'
  exact ⟨(posUnipotent D).map π, hU.map π,
    glbCore_map_eq_top_of_injOn Fact.out π hπ hinj
      (glbCore_two_posUnipotent_eq_top hct hext Fact.out hp2 hrank hX hadj)⟩

theorem exists_pGroup2_of_model_pomegaOdd {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  obtain ⟨⟨hp, -, hn, hp2⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have h2 : (2 : F) ≠ 0 := CFSG.AGLEmbedding.CharPGen.two_ne_zero_of_charP hp2
  have : Finite (spinGroup (quadOdd n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  exact exists_pGroup2_of_spin hp2 (Sum.inr (Sum.inr ())) (range_spinMatrix_quadOdd h2 hn)
    (fun x hx => CFSG.AGLEmbedding.CharPGen.sq_eq_one_of_eq_one_or_eq_neg_one
      ((mem_ker_spinMatrix_quadOdd_iff h2 x).1 hx))
    (D := oddDatum n F) (oddDatum_isCTGroupDatum n F (oddDatum_iSup_eq_top n F h2 hn))
    (oddDatum_steinbergExtras h2) (by show 2 ≤ n; omega)
    (fun γ hγ => isPGroup_of_isParametrization SpinOdd.isParametrization hγ)
    (exists_adj_of_isIrreducible (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanB
      (by omega : 0 < n)) (by omega : 2 ≤ n)) e

theorem exists_pGroup2_of_model_pomegaPlus {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel G .POmegaPlus n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  obtain ⟨⟨hp, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact exists_pGroup2_of_spin hp2 (Sum.inl ⟨0, by omega⟩) (range_spinMatrix_quadPlus hn3)
    (fun x hx => CFSG.AGLEmbedding.CharPGen.sq_eq_one_of_eq_one_or_eq_neg_one
      ((mem_ker_spinMatrix_quadPlus_iff x).1 hx))
    (D := plusDatum n F hn3) (plusDatum_isCTGroupDatum hn3 (plusDatum_iSup_eq_top n F hn3))
    (plusDatum_steinbergExtras hn3) (by show 2 ≤ n; omega)
    (fun γ hγ => isPGroup_of_isParametrization (SpinPlus.isParametrization (K := F) hn3) hγ)
    (exists_adj_of_isIrreducible (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanD hn3)
      (by omega : 2 ≤ n)) e

theorem exists_pGroup2_of_model_pomegaMinus {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel G .POmegaMinus n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  obtain ⟨⟨hp, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact exists_pGroup2_of_spin hp2 (Sum.inr (Sum.inr 0)) (range_spinMatrix_quadMinus hn hirr)
    (fun x hx => CFSG.AGLEmbedding.CharPGen.sq_eq_one_of_eq_one_or_eq_neg_one
      ((mem_ker_spinMatrix_quadMinus_iff hirr x).1 hx))
    (D := Twisted.minusDatum n hirr) (Twisted.minusDatum_isCTGroupDatum n hirr hn)
    (Twisted.minusDatum_steinbergExtras n hirr) (by show 2 ≤ n - 1; omega)
    (fun γ hγ => isPGroup_minusRootGroup hirr hγ)
    (exists_adj_of_isIrreducible (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanB
      (by omega : 0 < n - 1)) (by omega : 2 ≤ n - 1)) e

theorem charPGen2At_bOdd : CharPGen2At CFSG.AGLEmbedding.IsBOddIndex := by
  refine charPGen2At_of_pGroup ?_
  intro K _ _ d ⟨r, q, hr, hd⟩ e p hp hp2 hchar
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  exact exists_pGroup2_of_model_pomegaOdd
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr e)

theorem charPGen2At_d : CharPGen2At CFSG.AGLEmbedding.IsDIndex := by
  refine charPGen2At_of_pGroup ?_
  intro K _ _ d ⟨r, q, hd⟩ e p hp hp2 hchar
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  exact exists_pGroup2_of_model_pomegaPlus hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)

theorem charPGen2At_twistedD : CharPGen2At CFSG.AGLEmbedding.IsTwistedDIndex := by
  refine charPGen2At_of_pGroup ?_
  intro K _ _ d ⟨r, q, hd⟩ e p hp hp2 hchar
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  exact exists_pGroup2_of_model_pomegaMinus hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314
