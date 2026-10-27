module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearInner

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

section Psl

variable {n : ℕ} {K : Type} [Field K] [Finite K]

@[expose] noncomputable def pslBlock (a : SpecialLinearGroup (Fin n) K) (h : K[X]) :
    Subgroup (projectiveSL n K) :=
  ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map (proj n K)

abbrev PslIdx (a : SpecialLinearGroup (Fin n) K) : Type :=
  {h : primaryFactors ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) //
    3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (h : K[X]) ∨
    (2 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (h : K[X]) ∧ 4 ≤ Nat.card (AdjoinRoot (h : K[X])))}

variable {a : SpecialLinearGroup (Fin n) K}

theorem mem_fixSubgroup_slConjugation_toGL_iff {g : SpecialLinearGroup (Fin n) K} :
    g ∈ fixSubgroup (slConjugation n K (SpecialLinearGroup.toGL a)) ↔
      g ∈ Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin n) K)) := by
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply SpecialLinearGroup.toGL_injective
    have h1 := congrArg SpecialLinearGroup.toGL h
    rw [toGL_slConjugation] at h1
    rw [map_mul, map_mul]
    have : SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL a =
        SpecialLinearGroup.toGL a * SpecialLinearGroup.toGL g := by
      calc SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL a
          = (SpecialLinearGroup.toGL a * SpecialLinearGroup.toGL g *
              (SpecialLinearGroup.toGL a)⁻¹) * SpecialLinearGroup.toGL a := by rw [h1]
        _ = SpecialLinearGroup.toGL a * SpecialLinearGroup.toGL g := by group
    exact this
  · intro h
    apply SpecialLinearGroup.toGL_injective
    rw [toGL_slConjugation]
    have : SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL a =
        SpecialLinearGroup.toGL a * SpecialLinearGroup.toGL g := by
      rw [← map_mul, ← map_mul, h]
    calc SpecialLinearGroup.toGL a * SpecialLinearGroup.toGL g * (SpecialLinearGroup.toGL a)⁻¹
        = SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL a *
            (SpecialLinearGroup.toGL a)⁻¹ := by rw [this]
      _ = SpecialLinearGroup.toGL g := by group

variable (hZ : ∀ z ∈ scalars n K, z ^ 3 = 1 → z = 1) (hap : a ^ 3 = 1)
include hZ hap

theorem centralizer_proj_eq_map :
    Subgroup.centralizer ({proj n K a} : Set (projectiveSL n K)) =
      (Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin n) K))).map (proj n K) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, rfl⟩ := proj_surjective n K z
    refine ⟨y, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h1 : proj n K (y * a * y⁻¹) = proj n K a := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hz
      rw [map_mul, map_mul, map_inv, hz, mul_inv_cancel_right]
    have h2 := conj_eq_of_proj_eq_of_scalars hZ hap h1
    calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [h2]
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]

omit hZ hap in
theorem pslBlock_le_centralizer (h : K[X]) :
    pslBlock a h ≤ Subgroup.centralizer ({proj n K a} : Set (projectiveSL n K)) := by
  rintro _ ⟨g, hg, rfl⟩
  have hga := Subgroup.mem_centralizer_singleton_iff.mp (comap_linearSpecialBlock_le_centralizer h hg)
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hga]

theorem pslBlock_normal (h : K[X]) :
    ∀ c ∈ Subgroup.centralizer ({proj n K a} : Set (projectiveSL n K)), ∀ m ∈ pslBlock a h,
      c * m * c⁻¹ ∈ pslBlock a h := by
  intro c hc m hm
  rw [centralizer_proj_eq_map hZ hap] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨g, hg, rfl⟩ := hm
  exact ⟨c' * g * c'⁻¹, conj_mem_comap_linearSpecialBlock hc' hg, by simp⟩

omit hZ hap in
theorem isQuasisimple_pslBlock (hpk : (3 : K) ≠ 0) (hap : a ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (hgood : 3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) h ∨
      (2 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) h ∧ 4 ≤ Nat.card (AdjoinRoot h))) :
    CFSG.IsQuasisimple (pslBlock a h) := by
  have hsq := squarefree_minpoly_slGL hpk hap
  obtain ⟨eF⟩ := comap_linearSpecialBlock_mulEquiv hsq hh
  have hFq : CFSG.IsQuasisimple ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eF.symm (isQuasisimple_linearSpecialBlock hsq hh hgood)
  refine CFSG.LocalCores.isQuasisimple_map hFq (proj n K) fun hle => ?_
  have hFc : ∀ g ∈ (linearSpecialBlock (slGL n K a) h).comap (slGL n K),
      g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := fun g hg =>
    scalars_le_center n K (proj_eq_one_iff.mp (hle hg))
  have hZF : Subgroup.center ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_center_iff]
    intro g'
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hFc g g.2)) g')
  obtain ⟨u, w, huw⟩ := hFq.2.2
  apply huw
  induction u using QuotientGroup.induction_on with
  | H u =>
    induction w using QuotientGroup.induction_on with
    | H w =>
      rw [(QuotientGroup.eq_one_iff u).mpr (by rw [hZF]; exact Subgroup.mem_top u),
        (QuotientGroup.eq_one_iff w).mpr (by rw [hZF]; exact Subgroup.mem_top w)]

omit hZ hap in
theorem t6psl_isSolvable_pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
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

omit hZ hap in
theorem t6psl_derived_le_ker {G Q : Type*} [Group G] [Group Q] [Group.IsSolvable Q]
    (f : G →* Q) : ∃ k : ℕ, derivedSeries G k ≤ f.ker := by
  obtain ⟨k, hk⟩ := (inferInstance : Group.IsSolvable Q).solvable
  refine ⟨k, fun g hg => ?_⟩
  rw [MonoidHom.mem_ker]
  have h1 : f g ∈ (derivedSeries G k).map f := ⟨g, hg, rfl⟩
  have h2 := map_derivedSeries_le_derivedSeries f k h1
  rw [hk] at h2
  exact h2

theorem pslBlocks_derived (hpk : (3 : K) ≠ 0) :
    ∃ k : ℕ, ∀ x ∈ derivedSeries
        ↥(Subgroup.centralizer ({proj n K a} : Set (projectiveSL n K))) k,
      (x : projectiveSL n K) ∈ ⨆ h : PslIdx a, pslBlock a h.1.1 := by
  classical
  set A : GL (Fin n) K := SpecialLinearGroup.toGL a with hA
  have hsq : Squarefree (minpoly K (glA A : Module.End K (Fin n → K))) :=
    squarefree_minpoly_slGL hpk hap
  set C := fixSubgroup (slConjugation n K A) with hC
  set f := blockDetHom hsq with hf
  haveI : ∀ b : {b : primaryFactors (glA A : Module.End K (Fin n → K)) // ¬ IsGoodFactor A b},
      Group.IsSolvable (blockGL (glA A : Module.End K (Fin n → K)) b.1.1) := fun b =>
    isSolvable_blockGL_of_not_good b.1.2 b.2
  haveI : Group.IsSolvable ((b : primaryFactors (glA A : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) := inferInstance
  haveI : Group.IsSolvable ((b : {b : primaryFactors (glA A : Module.End K (Fin n → K)) //
      ¬ IsGoodFactor A b}) → blockGL (glA A : Module.End K (Fin n → K)) b.1.1) :=
    t6psl_isSolvable_pi
  obtain ⟨k, hk⟩ := t6psl_derived_le_ker f
  set X := Subgroup.centralizer ({proj n K a} : Set (projectiveSL n K)) with hX
  have hmemX : ∀ g : ↥C, (proj n K) (g : SpecialLinearGroup (Fin n) K) ∈ X := by
    intro g
    have hg : (g : SpecialLinearGroup (Fin n) K) ∈
        Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin n) K)) :=
      mem_fixSubgroup_slConjugation_toGL_iff.1 g.2
    rw [hX, centralizer_proj_eq_map hZ hap]
    exact ⟨_, hg, rfl⟩
  let π' : ↥C →* ↥X := ((proj n K).comp C.subtype).codRestrict X hmemX
  have hπ's : Function.Surjective π' := by
    intro z
    have hz : (z : projectiveSL n K) ∈
        (Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin n) K))).map (proj n K) := by
      rw [← centralizer_proj_eq_map hZ hap]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := hz
    exact ⟨⟨y, mem_fixSubgroup_slConjugation_toGL_iff.2 hy⟩, Subtype.ext hyz⟩
  refine ⟨k, fun x hx => ?_⟩
  rw [← map_derivedSeries_eq hπ's k] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  have hg1 : f g = 1 := MonoidHom.mem_ker.1 (hk hg)
  have hmem := mem_iSup_specialFactor_of_blockDetHom_eq_one hsq g hg1
  have h2 : (proj n K) (g : SpecialLinearGroup (Fin n) K) ∈
      (⨆ h : {h : primaryFactors (glA A : Module.End K (Fin n → K)) // IsGoodFactor A h},
        specialFactor A h.1.1).map (proj n K) := ⟨_, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  refine (iSup_le fun h => ?_ : _ ≤ ⨆ h : PslIdx a, pslBlock a h.1.1) h2
  exact le_iSup (fun h : PslIdx a => pslBlock a h.1.1) ⟨h.1, h.2⟩

end Psl

end CFSG.HardMathSupport.Dickson.Sec6.I1431
