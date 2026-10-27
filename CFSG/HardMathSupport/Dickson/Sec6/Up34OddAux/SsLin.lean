module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.CoreQuot
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.CALinearPrimary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.PartOne.KCUnitary CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Factors

variable {n : ℕ} {k : Type} [Field k] [Finite k]

theorem charP_of_natCard_eq_prime_pow {p f : ℕ} (hp : p.Prime) (hk : Nat.card k = p ^ f) :
    CharP k p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype k := Fintype.ofFinite k
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hk)

theorem exists_card_adjoinRoot_eq_pow {p f : ℕ} (hp : p.Prime) (hk : Nat.card k = p ^ f)
    {h : k[X]} [Fact (Irreducible h)] : ∃ f' : ℕ, 1 ≤ f' ∧ Nat.card (AdjoinRoot h) = p ^ f' := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := charP_of_natCard_eq_prime_pow hp hk
  haveI : CharP (AdjoinRoot h) p :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot h)).injective p
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite k
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card (AdjoinRoot h) p
  exact ⟨m, m.pos, by rw [Nat.card_eq_fintype_card, hm]⟩

theorem nonempty_specialFactor_equiv_sl {A : GL (Fin n) k}
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

theorem not_isLThreeFour_centerQuotient_of_sl (hO : LieOrderFormulasInput) {F : Type} [Group F]
    {m : ℕ} (hm : 2 ≤ m) {E : Type} [Field E] [Finite E] {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) (hE : Nat.card E = p ^ f) (e : F ≃* Matrix.SpecialLinearGroup (Fin m) E) :
    ¬ IsLThreeFour (F ⧸ Subgroup.center F) := by
  have hp2 : p ≠ 2 := by omega
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hadm : StatedLieAdmissible .PSL m p f :=
    ⟨hp, hf, hm, fun hc => by have := (Prod.mk.inj hc).2; omega,
      fun hc => by have := (Prod.mk.inj hc).2; omega⟩
  let e1 : F ⧸ Subgroup.center F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin m) E :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hmodel : LieModel (F ⧸ Subgroup.center F) .PSL m p f :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, E, inferInstance, inferInstance, hE,
        ⟨e1.trans (projectiveSpecialLinearGroupEquivStatedProj m E)⟩⟩
  exact not_isLThreeFour_of_lieModel_odd hO hp2 hmodel

private theorem isSolvable_pi_of_finite_up34 {ι : Type*} [Finite ι] {G : ι → Type*}
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

section Core

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem not_isLThreeFour_specialFactor (hO : LieOrderFormulasInput) {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK : Nat.card K = p ^ f) {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K (Fin n → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hgood : IsGoodFactor A h) :
    ¬ IsLThreeFour (↥(specialFactor A h) ⧸ Subgroup.center ↥(specialFactor A h)) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨f', hf', hE⟩ := exists_card_adjoinRoot_eq_pow (k := K) hp hK (h := h)
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End K (Fin n → K)) h := by
    unfold IsGoodFactor at hgood
    omega
  obtain ⟨e⟩ := nonempty_specialFactor_equiv_sl hsq hh
  exact not_isLThreeFour_centerQuotient_of_sl hO hm hp hp5 hf' hE e

theorem noL34Layer_conjAut_psl (hO : LieOrderFormulasInput) {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK : Nat.card K = p ^ f) {A : GL (Fin n) K} {c : Kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    NoL34Layer (LinearFlag.conjAut n K A) := by
  haveI : CharP K p := charP_of_natCard_eq_prime_pow hp hK
  have hpk : ((3 : ℕ) : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 3).1 h0
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hsq := squarefree_minpoly_glA hpk hA
  haveI : ∀ b : {b : primaryFactors (glA A : Module.End K (Fin n → K)) // ¬ IsGoodFactor A b},
      Group.IsSolvable (blockGL (glA A : Module.End K (Fin n → K)) b.1.1) := fun b =>
    isSolvable_blockGL_of_not_good b.1.2 b.2
  haveI : Group.IsSolvable ((b : primaryFactors (glA A : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) := inferInstance
  haveI : Group.IsSolvable ((b : {b : primaryFactors (glA A : Module.End K (Fin n → K)) //
      ¬ IsGoodFactor A b}) → blockGL (glA A : Module.End K (Fin n → K)) b.1.1) :=
    isSolvable_pi_of_finite_up34
  exact noL34Layer_of_centralQuotient (LinearFlag.proj n K) (LinearFlag.proj_surjective n K)
    (by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_center n K)
    (CatalogueBHigherLinearAction.slConjugation n K A) (LinearFlag.conjAut n K A)
    (fun x => (LinearFlag.conjAut_proj A x).symm)
    (fun h : {h : primaryFactors (glA A : Module.End K (Fin n → K)) // IsGoodFactor A h} =>
      specialFactor A h.1.1)
    (fun h => specialFactor_le_fixSubgroup A _) (fun h c' hc g hg => conj_mem_specialFactor hc hg)
    (fun h => isQuasisimple_specialFactor hsq h.1.2 h.2) (blockDetHom hsq)
    (mem_iSup_specialFactor_of_blockDetHom_eq_one hsq)
    (fun h => not_isLThreeFour_specialFactor hO hp hp5 hK hsq h.1.2 h.2)

end Core

section Glue

variable {K : Type} [Field K] [Finite K]

theorem exists_scalar_of_conjAut_eq_one_two {A : GL (Fin 2) K} (h : LinearFlag.conjAut 2 K A = 1) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c = A := by
  have hc : MulAut.congr (psl2Equiv K) (pglAction K (Matrix.ProjGenLinGroup.mk A)) =
      LinearFlag.conjAut 2 K A := congr_pglAction_mk A
  have h1 : pglAction K (Matrix.ProjGenLinGroup.mk A) = 1 := by
    apply (MulAut.congr (psl2Equiv K)).injective
    rw [hc, h, map_one]
  have h2 : Matrix.ProjGenLinGroup.mk A = 1 :=
    pglAction_injective K (h1.trans (map_one _).symm)
  have h3 : A ∈ Subgroup.center (GL (Fin 2) K) := Matrix.ProjGenLinGroup.mk_eq_one.1 h2
  rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3

theorem exists_scalar_of_conjAut_eq_one {n : ℕ} (hn : 2 ≤ n) {A : GL (Fin n) K}
    (h : LinearFlag.conjAut n K A = 1) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = A := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    exact exists_scalar_of_conjAut_eq_one_two h
  · exact (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff h3 A).1 h

theorem noL34Layer_of_mem_linearAutGroup (hO : LieOrderFormulasInput) {n : ℕ} (hn : 2 ≤ n)
    {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = p ^ f)
    {ψ : MulAut (LinearFlag.projectiveSL n K)} (hψ : ψ ∈ LinearFlag.linearAutGroup n K)
    (hψ3 : ψ ^ 3 = 1) : NoL34Layer ψ := by
  obtain ⟨A, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.1 hψ
  have h1 : LinearFlag.conjAut n K (A ^ 3) = 1 := by rw [map_pow]; exact hψ3
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one hn h1
  exact noL34Layer_conjAut_psl hO hp hp5 hK hc.symm

end Glue

theorem noL34InnAt_psl (hO : LieOrderFormulasInput) :
    NoL34InnAt (fun t n _ _ => t = .PSL ∧ 2 ≤ n) := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, hn⟩ := hF
  have hC : StatedClassicalModel P .PSL n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : P ≃* LinearFlag.projectiveSL n K := e0.trans (statedProjEquiv n K)
  haveI : Finite (LinearFlag.projectiveSL n K) := Finite.of_equiv P e.toEquiv
  refine noL34Layer_congr e ?_
  have hψ3' : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hψi : MulAut.congr e ψ ∈ inner (LinearFlag.projectiveSL n K) :=
    (CFSG.HardMathSupport.Dickson.Sec6.I923.congr_mem_inner_iff_of_equiv e ψ).mpr hψ
  exact noL34Layer_of_mem_linearAutGroup hO hn hadm.1 hp5 hK
    (CFSG.RankThree.PartTwo.KFacts.innAut_le_linearAutGroup n K hψi) hψ3'

theorem noL34InnAt_pslTwo (hO : LieOrderFormulasInput) : NoL34InnAt I923.FamPslTwo :=
  fun P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ =>
    noL34InnAt_psl hO P t n p f hadm ht ⟨hF.1, hF.2.ge⟩ hp5 hm ψ hψ3 hψ

theorem noL34InnAt_pslGood (hO : LieOrderFormulasInput) : NoL34InnAt I923.FamPslGood :=
  fun P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ =>
    noL34InnAt_psl hO P t n p f hadm ht ⟨hF.1, by have := hF.2.1; omega⟩ hp5 hm ψ hψ3 hψ

theorem noL34InnAt_pslBad (hO : LieOrderFormulasInput) : NoL34InnAt I923.FamPslBad :=
  fun P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ =>
    noL34InnAt_psl hO P t n p f hadm ht ⟨hF.1, by have := hF.2.1; omega⟩ hp5 hm ψ hψ3 hψ

end CFSG.HardMathSupport.Dickson.Sec6
