module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.HardMathSupport.Curtis.Coordinator
open scoped commutatorElement

section LinGL

variable {K : Type} [Field K]

theorem le_range_toGL_of_perfect {n : ℕ} {P : Subgroup (GL (Fin n) K)} (hP : ⁅P, P⁆ = P) :
    P ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
  intro g hg
  rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.2 hP
  exact CFSG.RankThree.PartOne.KCUnitary.eq_one_of_perfect_of_comm this
    (fun u v : Kˣ => mul_comm u v)
    ((GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp P.subtype) ⟨g, hg⟩

theorem exists_perfect_centralizer_gl_of_pow_scalar [Finite K] {n : ℕ} (hK : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) (a : GL (Fin n) K) (l : K) (hl : l ≠ 0) (h3 : (3 : K) ≠ 0)
    (ha : (a : Matrix (Fin n) (Fin n) K) ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ P : Subgroup (GL (Fin n) K), P ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) ∧
      ⁅P, P⁆ = P ∧ ¬ ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := by
  classical
  set x : Module.End K (Fin n → K) := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) with hxdef
  have hx3 : aeval x (X ^ 3 - C l : K[X]) = 0 := by
    have hX : x = Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) :=
      (toLinAlgEquiv'_eq_toLin' _).symm
    rw [hX]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [← map_pow, ha]
    simp [Algebra.algebraMap_eq_smul_one]
  have hsep : (X ^ 3 - C l : K[X]).Separable := by
    simpa using separable_X_pow_sub_C l (by simpa using h3) hl
  have hx : Squarefree (minpoly K x) :=
    squarefree_minpoly_of_aeval_eq_zero hsep.squarefree hx3
  have hex : ∃ b : primaryFactors x, 2 ≤ mult x b := by
    by_contra hcon
    push Not at hcon
    have hdvd : minpoly K x ∣ (X ^ 3 - C l : K[X]) := minpoly.dvd K x hx3
    have hne : (X ^ 3 - C l : K[X]) ≠ 0 := hsep.ne_zero
    have hdeg : (minpoly K x).natDegree ≤ 3 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      have h3' : (X ^ 3 - C l : K[X]).natDegree = 3 := by
        rw [natDegree_sub_C]; simp
      omega
    have hprod : (minpoly K x).natDegree = ∑ b ∈ primaryFactors x, b.natDegree := by
      rw [← prod_primaryFactors hx]
      rw [natDegree_prod_of_monic _ _ (fun b hb => monic_of_mem_primaryFactors hb)]
    have hsum := finrank_eq_sum_degree_mul_multiplicity hx
    rw [Module.finrank_fin_fun] at hsum
    have hle : n ≤ ∑ b ∈ primaryFactors x, b.natDegree := by
      refine hsum.le.trans ?_
      rw [← Finset.sum_coe_sort (primaryFactors x) (fun b => b.natDegree)]
      refine Finset.sum_le_sum fun b _ => ?_
      have : primaryMultiplicity x (b : K[X]) ≤ 1 := by
        have := hcon b
        change primaryMultiplicity x (b : K[X]) < 2 at this
        omega
      calc (b : K[X]).natDegree * primaryMultiplicity x (b : K[X])
          ≤ (b : K[X]).natDegree * 1 := Nat.mul_le_mul_left _ this
        _ = (b : K[X]).natDegree := mul_one _
    omega
  obtain ⟨b, hb⟩ := hex
  have hperf := isPerfect_blockImage hx hK b hb
  refine ⟨blockImage hx b, ?_, ?_, ?_⟩
  · refine (blockImage_le_range hx b).trans (le_of_eq ?_)
    exact range_commutantUnitsToGL_eq_centralizer a rfl
  · have : Group.IsPerfect (blockImage hx b) := hperf
    exact Subgroup.isPerfect_iff.1 this
  · intro hab
    have hq := isQuasisimple_blockImage hx hK b hb
    obtain ⟨-, -, c, d, hcd⟩ := hq
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨d', rfl⟩ := QuotientGroup.mk_surjective d
    apply hcd
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hab _ c'.2 _ d'.2)

end LinGL

section Proj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_perfect_centralizer_proj
    (h : (4 ≤ Nat.card K ∧ 4 ≤ n) ∨ (Nat.card K = 2 ∧ 5 ≤ n))
    (t : SpecialLinearGroup (Fin n) K) (ht : t ^ 3 ∈ scalars n K) :
    ∃ W : Subgroup (projectiveSL n K), ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧
      W ≤ Subgroup.centralizer ({proj n K t} : Set (projectiveSL n K)) := by
  classical
  obtain ⟨c, -, hc⟩ := mem_scalars.1 ht
  set a : GL (Fin n) K := SpecialLinearGroup.toGL t with ha
  have ha3 : (a : Matrix (Fin n) (Fin n) K) ^ 3 = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    have h1 : (a : Matrix (Fin n) (Fin n) K) = ((t : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := rfl
    have hc' : ((t : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
        scalar (Fin n) (c : K) := by
      rw [← hc]; exact (Matrix.SpecialLinearGroup.coe_pow t 3).symm
    rw [h1, hc']
    simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have h3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have : (3 : K) = 1 := by
      have : (3 : K) = 2 + 1 := by norm_num
      rw [this, h2, zero_add]
    rw [this]; exact one_ne_zero
  obtain ⟨P, hPc, hPp, hPne⟩ : ∃ P : Subgroup (GL (Fin n) K),
      P ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) ∧ ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
    rcases h with ⟨hK, hn⟩ | ⟨hK, hn⟩
    · obtain ⟨P, hPc, hPp, hab⟩ := exists_perfect_centralizer_gl_of_pow_scalar hK hn a c c.ne_zero h3 ha3
      refine ⟨P, hPc, hPp, ?_⟩
      rintro rfl
      exact hab fun g hg h hh => by
        rw [Subgroup.mem_bot] at hg hh; subst hg; subst hh; rfl
    · have hc1 : (c : K) = 1 := by
        have : Subsingleton Kˣ := by
          refine ⟨fun u v => Units.ext ?_⟩
          have hu := CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hK u
          have hv := CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hK v
          rcases hu with hu | hu <;> rcases hv with hv | hv
          · rw [hu, hv]
          · exact absurd hu u.ne_zero
          · exact absurd hv v.ne_zero
          · rw [hu, hv]
        rw [Subsingleton.elim c 1]; rfl
      have ha1 : a ^ 3 = 1 := by
        refine Units.ext ?_
        rw [Units.val_pow_eq_pow_val, ha3, hc1]
        simp
      obtain ⟨P, hPc, hPp, h3P⟩ :=
        exists_perfect_three_dvd_centralizer_gl_two hK hn a ha1
      refine ⟨P, hPc, hPp, ?_⟩
      rintro rfl
      have : Nat.card (⊥ : Subgroup (GL (Fin n) K)) = 1 := by simp
      rw [this] at h3P
      omega
  have hPrange := le_range_toGL_of_perfect hPp
  set P' : Subgroup (SpecialLinearGroup (Fin n) K) :=
    P.comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K) with hP'
  have hmap : P'.map (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K)
      = P := Subgroup.map_comap_eq_self hPrange
  have hinj : Function.Injective
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K) :=
    fun x y hxy => Subtype.ext (by
      simpa using congrArg (fun g : GL (Fin n) K => (Units.val g : Matrix (Fin n) (Fin n) K)) hxy)
  have hP'p : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hmap, hPp]
  have hP'ne : P' ≠ ⊥ := by
    rintro h0
    apply hPne
    rw [← hmap, h0, Subgroup.map_bot]
  refine ⟨P'.map (proj n K), ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hP'p]
  · intro hW
    apply hP'ne
    have hle : P' ≤ scalars n K := by
      intro g hg
      rw [← ker_proj, MonoidHom.mem_ker]
      have : proj n K g ∈ (⊥ : Subgroup (projectiveSL n K)) := hW ▸ ⟨g, hg, rfl⟩
      exact this
    have hcen : P' ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
      hle.trans (scalars_le_center n K)
    rw [eq_bot_iff, ← hP'p]
    refine Subgroup.commutator_le.2 fun g hg g' hg' => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact Subgroup.mem_center_iff.1 (hcen hg') g
  · rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : SpecialLinearGroup.toGL g * a = a * SpecialLinearGroup.toGL g :=
      Subgroup.mem_centralizer_singleton_iff.1 (hPc hg)
    have h2 : g * t = t * g := hinj (by simpa [ha] using h1)
    rw [← map_mul, ← map_mul, h2]

end Proj

end CFSG.HardMathSupport.Curtis.UnitaryLevi
