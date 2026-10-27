module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadKey
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShellGl
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadEigen
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

section Lift

variable {K : Type} [Field K] [Finite K]

theorem conjAut_eq_one_iff {n : ℕ} (hn : 3 ≤ n) {B : GL (Fin n) K} :
    conjAut n K B = 1 ↔ ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = B := by
  constructor
  · intro h
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn B 1 (by rw [map_one, mul_one, h])).2
  · rintro ⟨c, rfl⟩
    exact conjAut_scalar c

theorem lift_cube_scalar {n : ℕ} (hn : 3 ≤ n) {g : GL (Fin n) K} (h3 : conjAut n K g ^ 3 = 1) :
    ∃ ν : Kˣ, g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) ν := by
  obtain ⟨ν, hν⟩ := (conjAut_eq_one_iff hn).1 (by rw [map_pow]; exact h3)
  exact ⟨ν, hν.symm⟩

theorem lift_commutator_scalar {n : ℕ} (hn : 3 ≤ n) {g h : GL (Fin n) K}
    (hc : conjAut n K h * conjAut n K g = conjAut n K g * conjAut n K h) :
    ∃ ζ : Kˣ, h * g * h⁻¹ * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) ζ := by
  have : conjAut n K (h * g * h⁻¹ * g⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  obtain ⟨ζ, hζ⟩ := (conjAut_eq_one_iff hn).1 this
  exact ⟨ζ, hζ.symm⟩

theorem glA_scalar_apply {n : ℕ} (ν : Kˣ) (v : Fin n → K) :
    ((glA (Matrix.GeneralLinearGroup.scalar (Fin n) ν) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = (ν : K) • v := by
  show (Matrix.toLin' ((Matrix.GeneralLinearGroup.scalar (Fin n) ν : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) v = (ν : K) • v
  rw [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem injective_of_glUnit {W : Type*} [AddCommGroup W] [Module K W]
    (u : LinearMap.GeneralLinearGroup K W) : Function.Injective (u : Module.End K W) := by
  intro a b hab
  have h1 : ((u⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)
      ((u : Module.End K W) a) = a := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  have h2 : ((u⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)
      ((u : Module.End K W) b) = b := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  rw [← h1, ← h2, hab]

theorem commute_of_good {g h : GL (Fin 3) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin 3 → K)))) {f : K[X]}
    (hf : f ∈ primaryFactors (glA g : Module.End K (Fin 3 → K))) (hgood : IsGoodFactor g f)
    {ζ : Kˣ} (hζ : h * g * h⁻¹ * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) :
    h * g = g * h := by
  by_cases hz : (ζ : K) = 1
  · have hζ1 : ζ = 1 := Units.ext hz
    have : h * g * h⁻¹ * g⁻¹ = 1 := by rw [hζ, hζ1, map_one]
    calc h * g = (h * g * h⁻¹ * g⁻¹) * g * h := by group
      _ = g * h := by rw [this]; group
  · exfalso
    obtain ⟨c, hc⟩ := exists_eigenspace_two_of_good hsq hf hgood
    have hhg : h * g = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * g * h := by
      calc h * g = (h * g * h⁻¹ * g⁻¹) * g * h := by group
        _ = _ := by rw [hζ]
    let G : Module.End K (Fin 3 → K) := (glA g : LinearMap.GeneralLinearGroup K (Fin 3 → K))
    let H : Module.End K (Fin 3 → K) := (glA h : LinearMap.GeneralLinearGroup K (Fin 3 → K))
    have key : ∀ v, G (H v) = (ζ : K)⁻¹ • H (G v) := by
      intro v
      have h1 := congrArg (fun u : GL (Fin 3) K =>
        ((glA u : LinearMap.GeneralLinearGroup K (Fin 3 → K)) : Module.End K (Fin 3 → K)) v) hhg
      simp only [map_mul, Units.val_mul, Module.End.mul_apply, glA_scalar_apply] at h1
      have hz0 : (ζ : K) ≠ 0 := ζ.ne_zero
      show G (H v) = (ζ : K)⁻¹ • H (G v)
      have h2 : H (G v) = (ζ : K) • G (H v) := h1
      rw [h2, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    exact eigen_twist_false G (injective_of_glUnit _) (by simp) (M := H)
      (injective_of_glUnit _) (μ := (ζ : K)⁻¹) (fun h1 => hz (inv_eq_one.1 h1)) key hc

theorem twistfree_of_good {g : GL (Fin 3) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin 3 → K)))) {f : K[X]}
    (hf : f ∈ primaryFactors (glA g : Module.End K (Fin 3 → K))) (hgood : IsGoodFactor g f) :
    ∀ y : projectiveSL 3 K, conjAut 3 K g y = y ↔
      y ∈ (fixSubgroup (slConjugation 3 K g)).map (proj 3 K) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := proj_surjective 3 K y
    rw [conjAut_proj] at hy
    refine ⟨x, ?_, rfl⟩
    have hz : slConjugation 3 K g x * x⁻¹ ∈ scalars 3 K := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
    obtain ⟨c, hc3, hzc⟩ := mem_scalars.1 hz
    set z := slConjugation 3 K g x * x⁻¹ with hzdef
    have hzx : slConjugation 3 K g x = z * x := by rw [hzdef]; group
    by_cases hc1 : (c : K) = 1
    · have hz1 : z = 1 := Subtype.ext (by rw [hzc, hc1, map_one]; rfl)
      rw [SetLike.mem_coe, mem_fixSubgroup, hzx, hz1, one_mul]
    · exfalso
      obtain ⟨c2, hc2⟩ := exists_eigenspace_two_of_good hsq hf hgood
      let G : Module.End K (Fin 3 → K) := (glA g : LinearMap.GeneralLinearGroup K (Fin 3 → K))
      let M : Module.End K (Fin 3 → K) := (slGL 3 K x : LinearMap.GeneralLinearGroup K (Fin 3 → K))
      have e1 : slGL 3 K (slConjugation 3 K g x) = glA g * slGL 3 K x * (glA g)⁻¹ := by
        simp only [slGL, MonoidHom.comp_apply, toGL_slConjugation, map_mul, map_inv]
        rfl
      have hZl : ∀ w, ((slGL 3 K z : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
          Module.End K (Fin 3 → K)) w = (c : K) • w := by
        intro w
        rw [coe_slGL, Matrix.toLin'_apply, hzc, Matrix.scalar_apply]
        funext i
        rw [Matrix.mulVec_diagonal]
        rfl
      have h2 : glA g * slGL 3 K x = slGL 3 K z * slGL 3 K x * glA g := by
        have h3 : glA g * slGL 3 K x * (glA g)⁻¹ = slGL 3 K z * slGL 3 K x := by
          rw [← e1, hzx, map_mul]
        calc glA g * slGL 3 K x = (glA g * slGL 3 K x * (glA g)⁻¹) * glA g := by group
          _ = _ := by rw [h3]
      have key : ∀ v, G (M v) = (c : K) • M (G v) := by
        intro v
        have h4 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin 3 → K) =>
          (u : Module.End K (Fin 3 → K)) v) h2
        simp only [Units.val_mul, Module.End.mul_apply] at h4
        rw [hZl] at h4
        exact h4
      exact eigen_twist_false G (injective_of_glUnit _) (by simp) (M := M)
        (injective_of_glUnit _) (μ := (c : K)) hc1 key hc2
  · rintro ⟨x, hx, rfl⟩
    rw [conjAut_proj, mem_fixSubgroup.1 (SetLike.mem_coe.1 hx)]

theorem commutator_central_mul_left' {G : Type*} [Group G] {z a b : G} (hz : ∀ y, z * y = y * z) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc z * a * b * (a⁻¹ * z⁻¹) * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹) * z * z⁻¹ * b⁻¹ := by rw [hz (a * b * a⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_central_mul_right' {G : Type*} [Group G] {z a b : G} (hz : ∀ y, z * y = y * z) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc a * (z * b) * a⁻¹ * (b⁻¹ * z⁻¹) = (a * z) * b * a⁻¹ * (b⁻¹ * z⁻¹) := by group
    _ = (z * a) * b * a⁻¹ * (b⁻¹ * z⁻¹) := by rw [← hz a]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [hz (a * b * a⁻¹ * b⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem isSolvable_fixSub_of_no_good {g : GL (Fin 3) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin 3 → K))))
    (hno : ∀ h ∈ primaryFactors (glA g : Module.End K (Fin 3 → K)), ¬ IsGoodFactor g h) :
    Group.IsSolvable ↥(Lemma510Ns.fixSub (conjAut 3 K g)) := by
  classical
  set C := fixSubgroup (slConjugation 3 K g) with hC
  set X := Lemma510Ns.fixSub (conjAut 3 K g) with hX
  have hCs : Group.IsSolvable ↥C := isSolvable_centralizer_of_no_good hsq hno
  set X₀ : Subgroup (projectiveSL 3 K) := C.map (proj 3 K) with hX₀
  haveI : Group.IsSolvable ↥X₀ :=
    Group.isSolvable_of_surjective (f := (proj 3 K).subgroupMap C)
      ((proj 3 K).subgroupMap_surjective C)
  have hX₀X : X₀ ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hX, Lemma510Ns.mem_fixSub, conjAut_proj, mem_fixSubgroup.1 (SetLike.mem_coe.1 hx)]
  have hlift : ∀ a ∈ X, ∃ x : Matrix.SpecialLinearGroup (Fin 3) K, proj 3 K x = a ∧
      slConjugation 3 K g x * x⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    intro a ha
    obtain ⟨x, rfl⟩ := proj_surjective 3 K a
    refine ⟨x, rfl, scalars_le_center 3 K ?_⟩
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← conjAut_proj]
    have : conjAut 3 K g (proj 3 K x) = proj 3 K x := (Lemma510Ns.mem_fixSub).1 ha
    rw [this, mul_inv_cancel]
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ X₀ := by
    intro a ha b hb
    obtain ⟨xa, rfl, hza⟩ := hlift a ha
    obtain ⟨xb, rfl, hzb⟩ := hlift b hb
    refine ⟨⁅xa, xb⁆, ?_, (map_commutatorElement (proj 3 K) xa xb).symm⟩
    rw [SetLike.mem_coe, mem_fixSubgroup, map_commutatorElement]
    set za := slConjugation 3 K g xa * xa⁻¹ with hzadef
    set zb := slConjugation 3 K g xb * xb⁻¹ with hzbdef
    have hxa : slConjugation 3 K g xa = za * xa := by rw [hzadef]; group
    have hxb : slConjugation 3 K g xb = zb * xb := by rw [hzbdef]; group
    rw [hxa, hxb, commutator_central_mul_left' (fun y => (Subgroup.mem_center_iff.mp hza y).symm),
      commutator_central_mul_right' (fun y => (Subgroup.mem_center_iff.mp hzb y).symm)]
  set N : Subgroup ↥X := X₀.subgroupOf X with hN
  haveI : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hX₀X).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hX₀X).injective
  have hbase : derivedSeries ↥X 1 ≤ N := by
    rw [derivedSeries_succ, derivedSeries_zero]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [hN, Subgroup.mem_subgroupOf]
    exact hcomm a a.2 b b.2
  have hstep : ∀ k : ℕ, derivedSeries ↥X (k + 1) ≤ (derivedSeries ↥N k).map N.subtype := by
    intro k
    induction k with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hbase
    | succ k ih =>
      rw [derivedSeries_succ, derivedSeries_succ ↥N k, Subgroup.map_commutator]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨d, hd⟩ := (inferInstance : Group.IsSolvable ↥N).solvable
  refine ⟨⟨d + 1, ?_⟩⟩
  have := hstep d
  rw [hd, Subgroup.map_bot] at this
  exact le_bot_iff.1 this

theorem s1431_false_psl_bad_three (hpk : (3 : K) ≠ 0)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {A : Subgroup (MulAut (projectiveSL 3 K))} {ψ : MulAut (projectiveSL 3 K)}
    {J : Subgroup (projectiveSL 3 K)} {q : ℕ} (c : S1431Cfg (projectiveSL 3 K) A ψ J q)
    (hq : 10 ≤ q) (hA : ∀ a ∈ A, a ∈ linearAutGroup 3 K) : False := by
  classical
  refine s1431_false_of_lift_blocks_gl (proj 3 K) (proj_surjective 3 K)
    (by rw [ker_proj]; exact scalars_le_center 3 K) (slConjugation 3 K) (conjAut 3 K)
    (fun g x => (conjAut_proj g x).symm) c (fun a ha => mem_linearAutGroup_iff.1 (hA a ha)) ?_
  intro g hg3 hg1
  obtain ⟨ν, hν⟩ := lift_cube_scalar (by norm_num) hg3
  have hsq : Squarefree (minpoly K (glA g : Module.End K (Fin 3 → K))) :=
    squarefree_minpoly_glA (p := 3) (by simpa using hpk) hν
  by_cases hgood : ∃ f ∈ primaryFactors (glA g : Module.End K (Fin 3 → K)), IsGoodFactor g f
  · right
    obtain ⟨f0, hf0, hgood0⟩ := hgood
    refine ⟨{h : primaryFactors (glA g : Module.End K (Fin 3 → K)) // IsGoodFactor g h},
      inferInstance, fun h => specialFactor g h.1.1, twistfree_of_good hsq hf0 hgood0,
      fun h => specialFactor_le_fixSubgroup g h.1.1,
      fun h x hx m hm => conj_mem_specialFactor hx hm,
      fun h => isQuasisimple_specialFactor hsq h.1.2 h.2, goodBlocks_derived hsq, ?_⟩
    intro h hT h' h'3 hcomm
    obtain ⟨ν', hν'⟩ := lift_cube_scalar (by norm_num) h'3
    obtain ⟨ζ, hζ⟩ := lift_commutator_scalar (by norm_num) hcomm
    have hhg : h' * g = g * h' := commute_of_good hsq hf0 hgood0 hζ
    have hm2 := specialFactor_multiplicity_eq_two hO hsq h.1.2 h.2 hq hT
    exact key_specialFactor hsq h.1.2 hm2 hhg hν'
  · left
    exact isSolvable_fixSub_of_no_good hsq (fun f hf hgf => hgood ⟨f, hf, hgf⟩)

end Lift

end CFSG.HardMathSupport.Dickson.Sec6.I1431
