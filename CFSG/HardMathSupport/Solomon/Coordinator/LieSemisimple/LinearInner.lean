module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.CentralQuotient
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary

variable {n : ℕ} {k : Type*} [Field k] [Finite k]

@[expose] noncomputable def blockDetHom {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) :
    ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)) →*
      ((b : primaryFactors (glA A : Module.End k (Fin n → k))) → (AdjoinRoot (b : k[X]))ˣ) ×
      ((b : {b : primaryFactors (glA A : Module.End k (Fin n → k)) // ¬ IsGoodFactor A b}) →
        blockGL (glA A : Module.End k (Fin n → k)) b.1.1) :=
  (MonoidHom.prod
    (MonoidHom.piMap fun b : primaryFactors (glA A : Module.End k (Fin n → k)) =>
      Units.map (LinearMap.det : Module.End (AdjoinRoot (b : k[X]))
        (primaryComponent (glA A : Module.End k (Fin n → k)) (b : k[X])) →* AdjoinRoot (b : k[X])))
    (MonoidHom.pi fun b : {b : primaryFactors (glA A : Module.End k (Fin n → k)) //
        ¬ IsGoodFactor A b} => Pi.evalMonoidHom _ b.1)).comp
    ((glCentralizerEquivPi (x := glA A) hsq).toMonoidHom.comp
      (((slGL n k).comp (fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)).subtype
        ).codRestrict (gl_centralizer (glA A)) fun g => mem_fixSubgroup_slConjugation_iff.1 g.2))

private noncomputable def fixBlockPiHom {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) :
    ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)) →*
      ((b : primaryFactors (glA A : Module.End k (Fin n → k))) →
        blockGL (glA A : Module.End k (Fin n → k)) b) :=
  (glCentralizerEquivPi (x := glA A) hsq).toMonoidHom.comp
    (((slGL n k).comp (fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)).subtype
      ).codRestrict (gl_centralizer (glA A)) fun g => mem_fixSubgroup_slConjugation_iff.1 g.2)

private theorem symm_mulSingle_mem_linearSpecialBlock {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {x : LinearMap.GeneralLinearGroup K V}
    [DecidableEq (primaryFactors (x : Module.End K V))]
    (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (b : primaryFactors (x : Module.End K V)) (c : blockGL (x : Module.End K V) (b : K[X]))
    (hc : LinearMap.det (c : Module.End (AdjoinRoot (b : K[X]))
      (primaryComponent (x : Module.End K V) (b : K[X]))) = 1) :
    (((glCentralizerEquivPi hsq).symm (Pi.mulSingle b c) : gl_centralizer x) :
      LinearMap.GeneralLinearGroup K V) ∈ linearSpecialBlock x (b : K[X]) := by
  set g := (glCentralizerEquivPi hsq).symm (Pi.mulSingle b c) with hgdef
  have hgapp : ∀ (j : primaryFactors (x : Module.End K V)) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (j : K[X])),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        blockApply ((Pi.mulSingle b c : (j : primaryFactors (x : Module.End K V)) →
          blockGL (x : Module.End K V) (j : K[X])) j) v hv := by
    intro j v hv
    rw [← blockApply_glCentralizerEquivPi hsq g j v hv, hgdef, MulEquiv.apply_symm_apply]
  refine ⟨g.2, fun j hj hjh v hv => ?_, ?_⟩
  · rw [hgapp ⟨j, hj⟩ v hv, Pi.mulSingle_eq_of_ne (fun h' => hjh (congrArg Subtype.val h'))]
    rfl
  · have heq : commutantRestrict (b : K[X]) ⟨((g : LinearMap.GeneralLinearGroup K V) :
        Module.End K V), mem_commutant_of_mem_gl_centralizer g.2⟩ =
        (c : Module.End (AdjoinRoot (b : K[X]))
          (primaryComponent (x : Module.End K V) (b : K[X]))) :=
      LinearMap.ext fun v => Subtype.ext
        ((hgapp b v v.2).trans (by rw [Pi.mulSingle_eq_same]; rfl))
    rw [heq]
    exact hc

omit [Finite k] in
private theorem fixBlockPiHom_apply {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) :
    fixBlockPiHom hsq g = glCentralizerEquivPi hsq
      ⟨slGL n k (g : SpecialLinearGroup (Fin n) k), mem_fixSubgroup_slConjugation_iff.1 g.2⟩ :=
  rfl

omit [Finite k] in
private theorem fixBlockPiHom_injective {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) :
    Function.Injective (fixBlockPiHom hsq) := by
  intro g₁ g₂ h
  rw [fixBlockPiHom_apply, fixBlockPiHom_apply] at h
  have h1 := congrArg Subtype.val ((glCentralizerEquivPi hsq).injective h)
  exact Subtype.ext (slGL_injective h1)

theorem mem_iSup_specialFactor_of_blockDetHom_eq_one {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)))
    (hg : blockDetHom hsq g = 1) :
    (g : SpecialLinearGroup (Fin n) k) ∈
      ⨆ h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h},
        specialFactor A h.1.1 := by
  classical
  have hdet : ∀ b : primaryFactors (glA A : Module.End k (Fin n → k)),
      LinearMap.det ((fixBlockPiHom hsq g b : blockGL (glA A : Module.End k (Fin n → k)) b) :
        Module.End (AdjoinRoot (b : k[X]))
          (primaryComponent (glA A : Module.End k (Fin n → k)) (b : k[X]))) = 1 := by
    intro b
    exact congrArg Units.val (congrFun (congrArg Prod.fst hg) b)
  have hbad : ∀ b : {b : primaryFactors (glA A : Module.End k (Fin n → k)) //
      ¬ IsGoodFactor A b}, fixBlockPiHom hsq g b.1 = 1 := fun b =>
    congrFun (congrArg Prod.snd hg) b
  set W : Subgroup (SpecialLinearGroup (Fin n) k) :=
    ⨆ h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h},
      specialFactor A h.1.1
  have key : fixBlockPiHom hsq g ∈ (W.subgroupOf
      (fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))).map
        (fixBlockPiHom hsq) := by
    refine Subgroup.pi_mem_of_mulSingle_mem _ fun b => ?_
    by_cases hb : IsGoodFactor A b
    · have hγ := symm_mulSingle_mem_linearSpecialBlock (x := glA A) hsq b
        (fixBlockPiHom hsq g b) (hdet b)
      obtain ⟨s, hs⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq b.2 hγ)
      have hsmem : s ∈ specialFactor A b := by
        rw [specialFactor, Subgroup.mem_comap, hs]
        exact hγ
      have hsfix : s ∈ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A) :=
        mem_fixSubgroup_slConjugation_iff.2 (by rw [hs]; exact hγ.1)
      have hθs : fixBlockPiHom hsq ⟨s, hsfix⟩ = Pi.mulSingle b (fixBlockPiHom hsq g b) := by
        rw [fixBlockPiHom_apply]
        exact (glCentralizerEquivPi hsq).eq_symm_apply.1 (Subtype.ext hs)
      rw [← hθs]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_iSup_of_mem ⟨b, hb⟩ hsmem))
    · rw [hbad ⟨b, hb⟩, Pi.mulSingle_one]
      exact one_mem _
  obtain ⟨w, hw, hwg⟩ := key
  rw [← fixBlockPiHom_injective hsq hwg]
  exact Subgroup.mem_subgroupOf.1 hw

private theorem isSolvable_pi_of_finite' {ι : Type*} [Finite ι] {G : ι → Type*}
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

theorem perfectInLayer_conjAut {p : ℕ} (hpk : (p : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    PerfectInLayer (LinearFlag.conjAut n k A) := by
  have hsq := squarefree_minpoly_glA hpk hA
  haveI : ∀ b : {b : primaryFactors (glA A : Module.End k (Fin n → k)) // ¬ IsGoodFactor A b},
      Group.IsSolvable (blockGL (glA A : Module.End k (Fin n → k)) b.1.1) := fun b =>
    isSolvable_blockGL_of_not_good b.1.2 b.2
  haveI : Group.IsSolvable ((b : primaryFactors (glA A : Module.End k (Fin n → k))) →
      (AdjoinRoot (b : k[X]))ˣ) := inferInstance
  haveI : Group.IsSolvable ((b : {b : primaryFactors (glA A : Module.End k (Fin n → k)) //
      ¬ IsGoodFactor A b}) → blockGL (glA A : Module.End k (Fin n → k)) b.1.1) :=
    isSolvable_pi_of_finite'
  exact perfectInLayer_of_centralQuotient (LinearFlag.proj n k) (LinearFlag.proj_surjective n k)
    (by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_center n k)
    (CatalogueBHigherLinearAction.slConjugation n k A) (LinearFlag.conjAut n k A)
    (fun x => (LinearFlag.conjAut_proj A x).symm)
    (fun h : {h : primaryFactors (glA A : Module.End k (Fin n → k)) // IsGoodFactor A h} =>
      specialFactor A h.1.1)
    (fun h => specialFactor_le_fixSubgroup A _) (fun h c' hc g hg => conj_mem_specialFactor hc hg)
    (fun h => isQuasisimple_specialFactor hsq h.1.2 h.2) (blockDetHom hsq)
    (mem_iSup_specialFactor_of_blockDetHom_eq_one hsq)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
