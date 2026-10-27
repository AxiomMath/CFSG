module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnLinNum
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearInner
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.CALinearPrimary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCLinPlane
  CFSG.RankThree.PartOne.KCUnitary CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf

namespace Up34Chev2

section Factors

variable {n : ℕ} {k : Type} [Field k] [Finite k]

theorem exists_card_adjoinRoot_eq_pow_c2 {p f : ℕ} (hp : p.Prime) (hk : Nat.card k = p ^ f)
    {h : k[X]} [Fact (Irreducible h)] : ∃ f' : ℕ, 1 ≤ f' ∧ Nat.card (AdjoinRoot h) = p ^ f' := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype k := Fintype.ofFinite k
  haveI : CharP k p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hk)
  haveI : CharP (AdjoinRoot h) p :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot h)).injective p
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite k
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card (AdjoinRoot h) p
  exact ⟨m, m.pos, by rw [Nat.card_eq_fintype_card, hm]⟩

theorem nonempty_specialFactor_equiv_sl_c2 {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) {h : k[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k))) :
    Nonempty (↥(specialFactor A h) ≃* Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h)) (AdjoinRoot h)) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have : Finite (AdjoinRoot h) := Module.finite_of_finite k
  let b : Module.Basis (Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h))
      (AdjoinRoot h) (primaryComponent (glA A : Module.End k (Fin n → k)) h) :=
    Module.finBasisOfFinrankEq _ _ rfl
  have hle : linearSpecialBlock (glA A) h ≤ (slGL n k).range := fun _ hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  have hmap : (specialFactor A h).map (slGL n k) = linearSpecialBlock (glA A) h := by
    rw [specialFactor, Subgroup.map_comap_eq, inf_eq_right]
    exact hle
  let e₁ : linearSpecialBlock (glA A) h ≃*
      _root_.SpecialLinearGroup (AdjoinRoot h)
        (primaryComponent (glA A : Module.End k (Fin n → k)) h) :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict (glA A) h)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  exact ⟨((Subgroup.equivMapOfInjective _ (slGL n k) slGL_injective).trans
    (MulEquiv.subgroupCongr hmap)).trans (e₁.trans (Matrix.SpecialLinearGroup.toLin_equiv b).symm)⟩

end Factors

theorem lieModel_centerQuotient_of_equiv_SL_c2 {G : Type} [Group G] {m : ℕ} {E : Type} [Field E]
    [Finite E] {p f : ℕ} (hadm : StatedLieAdmissible .PSL m p f) (hE : Nat.card E = p ^ f)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin m) E) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .PSL m p f := by
  refine (lieModel_classical_iff (by decide)).mpr ⟨hadm, E, inferInstance, inferInstance, hE, ?_⟩
  exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)⟩

theorem block_central_of_isLThreeFour (hO : LieOrderFormulasInput)
    {F : Type} [Group F] {m : ℕ} {E : Type} [Field E] [Finite E] {e' : ℕ}
    (hE : Nat.card E = 2 ^ e') (e1 : F ≃* Matrix.SpecialLinearGroup (Fin m) E)
    (hadm : StatedLieAdmissible .PSL m 2 e') (hL : IsLThreeFour (F ⧸ Subgroup.center F)) :
    m = 3 ∧ Nat.card E = 4 ∧ ∃ z : F, z ∈ Subgroup.center F ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  have hmodel := lieModel_centerQuotient_of_equiv_SL_c2 hadm hE e1
  rcases isLThreeFour_cases_psl_two hO hmodel hL with ⟨hm, he⟩ | ⟨hm, he⟩
  · subst hm
    subst he
    have hE4 : Nat.card E = 4 := by rw [hE]; norm_num
    exact ⟨rfl, hE4, exists_central_three_sl_three_four hE4 e1⟩
  · subst hm
    subst he
    have hE2 : Nat.card E = 2 := by rw [hE]; norm_num
    exact absurd hL (not_isLThreeFour_sl_four_two hE2 e1)

theorem isSolvable_pi_of_finite_c2 {ι : Type*} [Finite ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  cases nonempty_fintype ι
  have hle : ∀ m : ℕ, derivedSeries (∀ i, G i) m ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (G i) m) := by
    intro m
    induction m with
    | zero =>
      simp only [derivedSeries_zero]
      rw [Subgroup.pi_top]
    | succ m ih =>
      rw [derivedSeries_succ]
      calc ⁅derivedSeries (∀ i, G i) m, derivedSeries (∀ i, G i) m⁆
          ≤ ⁅Subgroup.pi Set.univ (fun i => derivedSeries (G i) m),
              Subgroup.pi Set.univ (fun i => derivedSeries (G i) m)⁆ :=
            Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.pi Set.univ (fun i => ⁅derivedSeries (G i) m, derivedSeries (G i) m⁆) :=
            Subgroup.commutator_pi_pi_le _ _
        _ = Subgroup.pi Set.univ (fun i => derivedSeries (G i) (m + 1)) := by
            simp_rw [derivedSeries_succ]
  choose d hd using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup d, ?_⟩⟩
  rw [eq_bot_iff]
  refine (hle _).trans ?_
  rw [le_bot_iff, Subgroup.pi_eq_bot_iff]
  intro i
  rw [eq_bot_iff, ← hd i]
  exact derivedSeries_antitone (G i) (Finset.le_sup (f := d) (Finset.mem_univ i))

section Scalar

variable {n e : ℕ} {k : Type} [Field k] [Finite k]

theorem proj_ne_one_of_block (hk : Nat.card k = 2 ^ e) (hn : 4 ≤ n) {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) {h : k[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k)))
    (hm3 : primaryMultiplicity (glA A : Module.End k (Fin n → k)) h = 3)
    (hE4 : Nat.card (AdjoinRoot h) = 4)
    {z : Matrix.SpecialLinearGroup (Fin n) k} (hzF : z ∈ specialFactor A h) (hz1 : z ≠ 1) :
    LinearFlag.proj n k z ≠ 1 := by
  intro hproj
  obtain ⟨c, hcn, hzc⟩ := LinearFlag.proj_eq_one_iff.1 hproj
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    rw [hzc]
    simp
  have hF : slGL n k z ∈ linearSpecialBlock (glA A) h := hzF
  obtain ⟨hgc, ht, hd⟩ := hF
  have hact : ∀ v : Fin n → k, ((slGL n k z : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k)) v = (c : k) • v := by
    intro v
    rw [coe_slGL, Matrix.toLin'_apply, hzc, Matrix.scalar_apply]
    funext i
    simp [Matrix.mulVec_diagonal]
  have hother : ∀ j ∈ primaryFactors (glA A : Module.End k (Fin n → k)), j = h := by
    intro j hj
    by_contra hjh
    apply primaryComponent_ne_bot hsq hj
    rw [eq_bot_iff]
    intro v hv
    have h1 := ht j hj hjh v hv
    rw [hact] at h1
    have h2 : ((c : k) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h0 | h0
    · exact absurd (Units.ext (sub_eq_zero.1 h0)) hc1
    · rw [h0]
      exact Submodule.zero_mem _
  have hsum := finrank_eq_sum_degree_mul_multiplicity hsq
  rw [Module.finrank_fin_fun] at hsum
  have hn3 : n = h.natDegree * 3 := by
    rw [hsum, Finset.sum_eq_single (⟨h, hh⟩ : ↥(primaryFactors (glA A : Module.End k (Fin n → k))))
      (fun b _ hb => absurd (Subtype.ext (hother b b.2)) hb)
      (fun h' => absurd (Finset.mem_univ _) h')]
    show h.natDegree * primaryMultiplicity (glA A : Module.End k (Fin n → k)) h = h.natDegree * 3
    rw [hm3]
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hcard := natCard_adjoinRoot (K := k) h
  rw [hE4, hk, ← pow_mul] at hcard
  haveI : Fintype k := Fintype.ofFinite k
  have hk3 : 2 < Fintype.card k := by
    rw [Fintype.two_lt_card_iff]
    refine ⟨0, 1, (c : k), zero_ne_one, ?_, ?_⟩
    · exact (Units.ne_zero c).symm
    · exact fun h' => hc1 (Units.ext h'.symm)
  rw [← Nat.card_eq_fintype_card, hk] at hk3
  have he2 : 2 ≤ e := by
    by_contra hlt
    push Not at hlt
    interval_cases e <;> simp at hk3
  have hd1 : 1 ≤ h.natDegree := Irreducible.natDegree_pos Fact.out
  have hed : e * h.natDegree = 2 :=
    Nat.pow_right_injective (le_refl 2) (by simpa using hcard.symm)
  have hd : h.natDegree = 1 := by nlinarith
  omega

end Scalar

section Block

variable {n e : ℕ} {k : Type} [Field k] [Finite k]

theorem exists_central_of_isLThreeFour_specialFactor (hO : LieOrderFormulasInput)
    (hk : Nat.card k = 2 ^ e) (hn : 4 ≤ n) {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) {h : k[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k))) (hgood : IsGoodFactor A h)
    (hL : IsLThreeFour (↥(specialFactor A h) ⧸ Subgroup.center ↥(specialFactor A h))) :
    ∃ z : Matrix.SpecialLinearGroup (Fin n) k, z ∈ specialFactor A h ∧
      (∀ g ∈ specialFactor A h, g * z = z * g) ∧ z ^ 3 = 1 ∧ LinearFlag.proj n k z ≠ 1 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite k
  obtain ⟨e', he'1, hE⟩ := exists_card_adjoinRoot_eq_pow_c2 (p := 2) Nat.prime_two hk (h := h)
  obtain ⟨e1⟩ := nonempty_specialFactor_equiv_sl_c2 hsq hh
  have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h := by
    unfold IsGoodFactor at hgood
    omega
  have hadm : StatedLieAdmissible .PSL (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h)
      2 e' := by
    refine ⟨Nat.prime_two, he'1, hm2, fun hc => ?_, fun hc => ?_⟩
    · have h1 := (Prod.mk.inj hc).1
      have h2 := (Prod.mk.inj hc).2
      unfold IsGoodFactor at hgood
      rw [hE] at hgood
      omega
    · have h1 := (Prod.mk.inj hc).1
      have h2 := (Prod.mk.inj hc).2
      unfold IsGoodFactor at hgood
      rw [hE] at hgood
      omega
  obtain ⟨hm3, hE4, z, hzc, hz3, hz1⟩ := block_central_of_isLThreeFour hO hE e1 hadm hL
  refine ⟨(z : Matrix.SpecialLinearGroup (Fin n) k), z.2, fun g hg => ?_,
    congrArg Subtype.val hz3, ?_⟩
  · have := Subgroup.mem_center_iff.1 hzc ⟨g, hg⟩
    exact congrArg Subtype.val this
  · refine proj_ne_one_of_block hk hn hsq hh hm3 hE4 z.2 ?_
    intro h1
    exact hz1 (Subtype.ext h1)

end Block

section Main

variable {n e : ℕ} {K : Type} [Field K] [Finite K]

theorem noL34Layer_conjAut_psl_two (hO : LieOrderFormulasInput)
    (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ e) {A : GL (Fin n) K} {c : Kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    NoL34Layer (LinearFlag.conjAut n K A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hpk : ((3 : ℕ) : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K 2 3).1 h0
    omega
  have hsq := squarefree_minpoly_glA hpk hA
  haveI : ∀ b : {b : primaryFactors (glA A : Module.End K (Fin n → K)) // ¬ IsGoodFactor A b},
      Group.IsSolvable (blockGL (glA A : Module.End K (Fin n → K)) b.1.1) := fun b =>
    isSolvable_blockGL_of_not_good b.1.2 b.2
  haveI : Group.IsSolvable ((b : primaryFactors (glA A : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) := inferInstance
  haveI : Group.IsSolvable ((b : {b : primaryFactors (glA A : Module.End K (Fin n → K)) //
      ¬ IsGoodFactor A b}) → blockGL (glA A : Module.End K (Fin n → K)) b.1.1) :=
    isSolvable_pi_of_finite_c2
  exact noL34Layer_of_centralQuotient_two (LinearFlag.proj n K) (LinearFlag.proj_surjective n K)
    (by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_center n K)
    (CatalogueBHigherLinearAction.slConjugation n K A) (LinearFlag.conjAut n K A)
    (fun x => (LinearFlag.conjAut_proj A x).symm)
    (fun h : {h : primaryFactors (glA A : Module.End K (Fin n → K)) // IsGoodFactor A h} =>
      specialFactor A h.1.1)
    (fun h => specialFactor_le_fixSubgroup A _) (fun h c' hc g hg => conj_mem_specialFactor hc hg)
    (fun h => isQuasisimple_specialFactor hsq h.1.2 h.2) (blockDetHom hsq)
    (mem_iSup_specialFactor_of_blockDetHom_eq_one hsq)
    (fun h hL => exists_central_of_isLThreeFour_specialFactor hO hK hn hsq h.1.2 h.2 hL)

end Main

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
