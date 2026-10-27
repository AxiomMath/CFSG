module

public import CFSG.LieType.Chevalley.GraphFixedBorelOvergroups
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.MinimalBorelOvergroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (t K σ) in
@[expose] def graphFixedOppositeBorel :
    Subgroup (ModGL t.tag K) :=
  graphFixedRootTorus t K σ ⊔ graphFixedNegUnipotent t K σ

variable (t K σ) in
@[expose] def graphFixedOppositeMinimalParabolic
    (a : Fin t.foldedTag.rank) :
    Subgroup (ModGL t.tag K) :=
  graphFixedOppositeBorel t K σ ⊔
    Subgroup.closure (Set.range fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K))

variable (hσ : Function.Surjective σ)
include hσ

theorem graphFixedParabolic_le_iff
    {J J' : Set (Fin t.foldedTag.rank)} :
    graphFixedParabolic t K σ J ≤ graphFixedParabolic t K σ J' ↔ J ⊆ J' :=
  ⟨fun h _ ha => (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff hσ).1
      (h ((canonicalRep_orbitReflection_mem_graphFixedParabolic_iff hσ).2 ha)),
    fun h => sup_le_sup_left (Subgroup.closure_mono (Set.image_mono h)) _⟩

theorem graphFixedParabolic_injective
    : Function.Injective (graphFixedParabolic t K σ) :=
  fun _ _ h => Set.Subset.antisymm ((graphFixedParabolic_le_iff hσ).1 h.le)
    ((graphFixedParabolic_le_iff hσ).1 h.ge)

theorem graphFixedRootBorel_lt_graphFixedParabolic
    {J : Set (Fin t.foldedTag.rank)}
    (hJ : J.Nonempty) : graphFixedRootBorel t K σ < graphFixedParabolic t K σ J := by
  refine lt_of_le_of_ne (graphFixedRootBorel_le_graphFixedParabolic t K σ J) fun h => ?_
  rw [← graphFixedParabolic_empty] at h
  exact hJ.ne_empty (graphFixedParabolic_injective hσ h).symm

omit hσ in
theorem nonempty_of_graphFixedRootBorel_lt
    {J : Set (Fin t.foldedTag.rank)}
    (h : graphFixedRootBorel t K σ < graphFixedParabolic t K σ J) : J.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [graphFixedParabolic_empty] at h
  exact lt_irrefl _ h

theorem graphFixedRootBorel_covBy_iff
    {A : Subgroup (ModGL t.tag K)}
    (hA : A ≤ graphFixedRootGroup t K σ) :
    graphFixedRootBorel t K σ ⋖ A ↔ ∃ a, A = graphFixedParabolic t K σ {a} := by
  constructor
  · rintro ⟨hlt, hmin⟩
    have hJ := eq_graphFixedParabolic_of_le hσ hlt.le hA
    set J := {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A}
    obtain ⟨a, ha⟩ := nonempty_of_graphFixedRootBorel_lt (hJ ▸ hlt)
    refine ⟨a, ?_⟩
    have hle : graphFixedParabolic t K σ {a} ≤ A := hJ ▸
      (graphFixedParabolic_le_iff hσ).2 (Set.singleton_subset_iff.2 ha)
    by_contra hne
    exact hmin (graphFixedRootBorel_lt_graphFixedParabolic hσ (Set.singleton_nonempty a))
      (lt_of_le_of_ne hle fun h => hne h.symm)
  · rintro ⟨a, rfl⟩
    refine ⟨graphFixedRootBorel_lt_graphFixedParabolic hσ (Set.singleton_nonempty a),
      fun A' hBA' hA'P => ?_⟩
    have hJ' := eq_graphFixedParabolic_of_le hσ hBA'.le
      (hA'P.le.trans (graphFixedParabolic_le t K σ _))
    set J' := {b | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) ∈ A'}
    have hsub : J' ⊆ {a} := (graphFixedParabolic_le_iff hσ).1 (hJ' ▸ hA'P.le)
    obtain ⟨b, hb⟩ := nonempty_of_graphFixedRootBorel_lt (hJ' ▸ hBA')
    have hJ'a : J' = {a} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 (by
      have := hsub hb
      rw [Set.mem_singleton_iff] at this
      exact this ▸ hb))
    rw [hJ', hJ'a] at hA'P
    exact lt_irrefl _ hA'P

omit hσ

theorem mem_foldedParabolicWeylGroup_singleton
    {a : Fin t.foldedTag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ foldedParabolicWeylGroup t {a}) : w = 1 ∨ w = t.orbitReflection a := by
  rw [foldedParabolicWeylGroup, Set.image_singleton] at hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 hw
  have hsq : t.orbitReflection a * t.orbitReflection a = 1 := t.orbitReflection_mul_self a
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, hsq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hsq, one_zpow, one_mul, zpow_one]

theorem inversionSet_orbitReflection
    (a : Fin t.foldedTag.rank) :
    inversionSet (t.orbitReflection a) = simpleOrbitRoots t a := by
  ext β
  constructor
  · rintro ⟨hβ, hpos, -, hneg⟩
    obtain ⟨j, hj, rfl⟩ := t.eq_single_of_height_orbitReflection_smul_neg hβ hpos hneg
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨isRoot_single _ j, by rw [height_single]; exact one_pos, ?_, ?_⟩
    · rw [t.orbitReflection_smul_single hj]
      exact IsRoot.neg (isRoot_single _ j)
    · rw [t.orbitReflection_smul_single hj, height_neg, height_single]
      omega

theorem mem_rootSpan_negSimpleOrbitRoots_iff
    (a : Fin t.foldedTag.rank) {g : ModGL t.tag K} :
    g ∈ rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ ↔
      ∃ c : orbitField t K σ a, (orbitY t K σ a c : ModGL t.tag K) = g := by
  refine ⟨fun hg => ⟨Multiplicative.toAdd ((orbitYEquiv t σ a).symm ⟨g, hg⟩), ?_⟩, ?_⟩
  · rw [← coe_orbitYEquiv t σ a, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    rw [← coe_orbitYEquiv t σ a c]
    exact (orbitYEquiv t σ a (Multiplicative.ofAdd c)).2

theorem coe_rootSpan_negSimpleOrbitRoots_inf
    (a : Fin t.foldedTag.rank) :
    ((rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) =
      Set.range fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K) :=
  Set.ext fun _ => mem_rootSpan_negSimpleOrbitRoots_iff a

theorem coe_rootSpan_simpleOrbitRoots_inf
    (a : Fin t.foldedTag.rank) :
    ((rootSpan t.tag K (simpleOrbitRoots t a) ⊓ twistedFixedGroup t K σ :
        Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) =
      Set.range fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K) :=
  Set.ext fun _ => mem_rootSpan_simpleOrbitRoots_iff σ a

theorem closure_range_orbitX
    (a : Fin t.foldedTag.rank) :
    Subgroup.closure (Set.range fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K)) =
      rootSpan t.tag K (simpleOrbitRoots t a) ⊓ twistedFixedGroup t K σ :=
  le_antisymm ((Subgroup.closure_le _).2 fun _ ⟨c, hc⟩ =>
      (mem_rootSpan_simpleOrbitRoots_iff σ a).2 ⟨c, hc⟩)
    fun _ hg => Subgroup.subset_closure ((mem_rootSpan_simpleOrbitRoots_iff σ a).1 hg)

theorem orbitY_mem_graphFixedParabolic
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) ∈ graphFixedParabolic t K σ {a} := by
  rw [← canonicalRep_orbitReflection_conj_orbitX t σ a c]
  have hn : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      graphFixedParabolic t K σ {a} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, Set.mem_singleton a, rfl⟩)
  exact mul_mem (mul_mem hn (graphFixedRootBorel_le_graphFixedParabolic t K σ _
    (graphFixedPosUnipotent_le_graphFixedRootBorel
      (orbitX_mem_graphFixedPosUnipotent t σ a (-c))))) (inv_mem hn)

theorem graphFixedParabolic_singleton_eq
    (a : Fin t.foldedTag.rank) :
    graphFixedParabolic t K σ {a} = graphFixedRootBorel t K σ ⊔
      (rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ) := by
  refine le_antisymm (sup_le le_sup_left ((Subgroup.closure_le _).2 ?_))
    (sup_le (graphFixedRootBorel_le_graphFixedParabolic t K σ _) fun g hg => ?_)
  · rintro _ ⟨b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [SetLike.mem_coe]
    dsimp only
    rw [canonicalRep_orbitReflection_eq_orbitN t σ b, orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    have hx : ∀ c, (orbitX t K σ b c : ModGL t.tag K) ∈ graphFixedRootBorel t K σ ⊔
        (rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit b)) ⊓
          twistedFixedGroup t K σ) := fun c =>
      Subgroup.mem_sup_left (graphFixedPosUnipotent_le_graphFixedRootBorel
        (orbitX_mem_graphFixedPosUnipotent t σ b c))
    exact mul_mem (mul_mem (hx _) (Subgroup.mem_sup_right
      ((mem_rootSpan_negSimpleOrbitRoots_iff b).2 ⟨_, rfl⟩))) (hx _)
  · obtain ⟨c, rfl⟩ := (mem_rootSpan_negSimpleOrbitRoots_iff a).1 hg
    exact orbitY_mem_graphFixedParabolic a c

theorem mul_canonicalRep_orbitReflection_not_mem
    (a : Fin t.foldedTag.rank) {b : ModGL t.tag K}
    (hb : b ∈ graphFixedRootBorel t K σ) :
    b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∉
      graphFixedNegUnipotent t K σ := by
  intro hv
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hw₀ := mem_relWeylTwist_of_forall_length_le hmax
  rw [← map_conj_graphFixedPosUnipotent (K := K) (σ := σ) hmax] at hv
  obtain ⟨u, hu, hvu⟩ := hv
  have hvu' : canonicalRep (coxeterSystem t.tag) K w₀ * u *
      (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹ =
        b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) := hvu
  have e : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
      b⁻¹ * (canonicalRep (coxeterSystem t.tag) K w₀ * u *
        (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹) := by
    rw [hvu', inv_mul_cancel_left]
  have hbB := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1
  have huB : u ∈ borelGroup t.tag K := Subgroup.mem_sup_right (Subgroup.mem_inf.1 hu).1
  have h₁ : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      canonicalRep (coxeterSystem t.tag) K w₀ ∈ bruhatCell t.tag K w₀ := by
    refine mem_bruhatCell.2 ⟨b⁻¹, inv_mem hbB, u, huB, ?_⟩
    rw [e]
    group
  obtain ⟨h, hh, hrep⟩ := exists_canonicalRep_mul_eq (K := K) (σ := σ)
    (t.orbitReflection_mem a) hw₀
  have hhB := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1
    (graphFixedRootTorus_le_graphFixedRootBorel hh)).1).1
  have h₂ : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      canonicalRep (coxeterSystem t.tag) K w₀ ∈
        bruhatCell t.tag K (t.orbitReflection a * w₀) := by
    rw [hrep]
    exact mem_bruhatCell.2 ⟨1, one_mem _, h, hhB, by rw [one_mul]⟩
  have hne : t.orbitReflection a * w₀ ≠ w₀ := fun he =>
    t.orbitReflection_ne_one a (mul_right_cancel (he.trans (one_mul w₀).symm))
  exact Set.disjoint_left.1 (disjoint_bruhatCell (K := K) hne) h₂ h₁

variable (hσ : Function.Surjective σ)
include hσ

theorem coe_graphFixedParabolic_singleton_inf_negUnipotent
    (a : Fin t.foldedTag.rank) :
    ((graphFixedParabolic t K σ {a} ⊓ graphFixedNegUnipotent t K σ : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) =
      Set.range fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K) := by
  refine Set.Subset.antisymm (fun v hv => ?_) ?_
  · obtain ⟨hvP, hvV⟩ := Subgroup.mem_inf.1 hv
    have hvP' : v ∈ graphFixedParabolicCells t K σ {a} := by
      rw [← graphFixedParabolic_eq_cells hσ]
      exact hvP
    obtain ⟨w, hw, hvw⟩ := hvP'
    rcases mem_foldedParabolicWeylGroup_singleton hw with rfl | rfl
    ·
      obtain ⟨b, hb, b', hb', hbb⟩ := mem_graphFixedRootBruhatCell.1 hvw
      rw [canonicalRep_one, mul_one] at hbb
      have hmem : v ∈ graphFixedRootBorel t K σ ⊓ graphFixedNegUnipotent t K σ :=
        Subgroup.mem_inf.2 ⟨hbb ▸ mul_mem hb hb', hvV⟩
      rw [graphFixedRootBorel_inf_graphFixedNegUnipotent, Subgroup.mem_bot] at hmem
      rw [hmem]
      exact (mem_rootSpan_negSimpleOrbitRoots_iff (σ := σ) a).1 (one_mem _)
    ·
      obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ :=
        (bijOn_graphFixedRootBruhatCell hσ (t.orbitReflection_mem a)).surjOn hvw
      have hu' : u ∈ rootSpan t.tag K (simpleOrbitRoots t a) ⊓ twistedFixedGroup t K σ := by
        rw [← inversionSet_orbitReflection]
        exact hu
      obtain ⟨c, rfl⟩ := (mem_rootSpan_simpleOrbitRoots_iff σ a).1 hu'
      simp only at hvV ⊢
      by_cases hc : c = 0
      · subst hc
        rw [orbitX_zero, Subgroup.coe_one, mul_one] at hvV
        exact absurd hvV (mul_canonicalRep_orbitReflection_not_mem a hb)
      · obtain ⟨-, -, b', hb', hb'eq⟩ := (fixed_simple_rank_one_Bruhat_identity t K σ).2 a
          (Units.mk0 c hc)
        rw [Units.val_mk0] at hb'eq
        rw [mul_assoc, hb'eq, ← mul_assoc] at hvV ⊢
        have hy := orbitY_mem_graphFixedNegUnipotent t σ a
          (((Units.mk0 c hc)⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)
        have hbb : b * b' ∈ graphFixedRootBorel t K σ ⊓ graphFixedNegUnipotent t K σ := by
          refine Subgroup.mem_inf.2 ⟨mul_mem hb hb', ?_⟩
          have := mul_mem hvV (inv_mem hy)
          rwa [mul_inv_cancel_right] at this
        rw [graphFixedRootBorel_inf_graphFixedNegUnipotent, Subgroup.mem_bot] at hbb
        exact ⟨(((Units.mk0 c hc)⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a),
          by rw [hbb, one_mul]⟩
  · rintro _ ⟨c, rfl⟩
    exact Subgroup.mem_inf.2 ⟨orbitY_mem_graphFixedParabolic a c,
      orbitY_mem_graphFixedNegUnipotent t σ a c⟩

theorem graphFixedParabolic_singleton_inf_negUnipotent
    (a : Fin t.foldedTag.rank) :
    graphFixedParabolic t K σ {a} ⊓ graphFixedNegUnipotent t K σ =
      rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ :=
  SetLike.coe_injective (by
    rw [coe_graphFixedParabolic_singleton_inf_negUnipotent hσ,
      coe_rootSpan_negSimpleOrbitRoots_inf])

omit hσ

section Opposition

variable
    {w₀ : WeylGroup t.tag} {j : Fin t.tag.rank → Fin t.tag.rank}
  (hj : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (j i) 1)
include hj

theorem perm_pow_apply_eq_of_smul_single
    (hw₀ : w₀ ∈ relWeylTwist t) (k : ℕ)
    (i : Fin t.tag.rank) : j ((t.perm ^ k) i) = (t.perm ^ k) (j i) := by
  have h := t.permLattice_pow_smul hw₀ k (Pi.single i 1)
  rw [hj, permLattice_neg_single, permLattice_single, hj] at h
  exact t.single_one_injective (neg_injective h).symm

theorem orbitIndex_apply_eq_of_smul_single
    (hw₀ : w₀ ∈ relWeylTwist t) {i i' : Fin t.tag.rank}
    (h : t.orbitIndex i' = t.orbitIndex i) : t.orbitIndex (j i') = t.orbitIndex (j i) := by
  have hi' : i' ∈ t.orbit (t.orbitIndex i) := (t.mem_orbit_iff).2 h
  rw [t.orbit_orbitIndex, Finset.mem_image] at hi'
  obtain ⟨k, -, rfl⟩ := hi'
  rw [perm_pow_apply_eq_of_smul_single hj hw₀]
  exact (t.mem_orbit_iff).1 (t.perm_pow_mem_orbit (t.mem_orbit_orbitIndex (j i)) k)

theorem apply_apply_eq_of_smul_single (hsq : w₀ * w₀ = 1) (i : Fin t.tag.rank) : j (j i) = i := by
  have h1 : w₀ • (w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) = Pi.single i 1 := by
    rw [smul_smul, hsq, one_smul]
  rw [hj i, smul_neg, hj (j i), neg_neg] at h1
  exact t.single_one_injective h1

theorem orbitIndex_apply_orbitMin_involutive
    (hw₀ : w₀ ∈ relWeylTwist t) (hsq : w₀ * w₀ = 1)
    (a : Fin t.foldedTag.rank) :
    t.orbitIndex (j (t.orbitMin (t.orbitIndex (j (t.orbitMin a))))) = a := by
  rw [orbitIndex_apply_eq_of_smul_single hj hw₀ (i := j (t.orbitMin a)) (t.orbitIndex_orbitMin _),
    apply_apply_eq_of_smul_single hj hsq, t.orbitIndex_orbitMin]

theorem image_smul_negSimpleOrbitRoots
    (hw₀ : w₀ ∈ relWeylTwist t) (a : Fin t.foldedTag.rank) :
    (fun α => w₀ • α) '' ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) =
      simpleOrbitRoots t (t.orbitIndex (j (t.orbitMin a))) := by
  ext β
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨j i, (t.mem_orbit_iff).2 (orbitIndex_apply_eq_of_smul_single hj hw₀ ?_), ?_⟩
    · rw [(t.mem_orbit_iff).1 hi, t.orbitIndex_orbitMin]
    · change Pi.single (j i) 1 = w₀ • -(Pi.single i 1 : Fin t.tag.rank → ℤ)
      rw [smul_neg, hj, neg_neg]
  · rintro ⟨i', hi', rfl⟩
    have h1 : i' ∈ t.orbit (t.orbitIndex (j (t.orbitMin a))) := hi'
    rw [t.orbit_orbitIndex, Finset.mem_image] at h1
    obtain ⟨k, -, rfl⟩ := h1
    refine ⟨_, ⟨(t.perm ^ k) (t.orbitMin a), t.perm_pow_mem_orbit (t.orbitMin_mem a) k, rfl⟩, ?_⟩
    change w₀ • -(Pi.single ((t.perm ^ k) (t.orbitMin a)) 1 : Fin t.tag.rank → ℤ) =
      Pi.single ((t.perm ^ k) (j (t.orbitMin a))) 1
    rw [smul_neg, hj, neg_neg, perm_pow_apply_eq_of_smul_single hj hw₀]

theorem map_conj_rootSpan_negSimpleOrbitRoots
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (a : Fin t.foldedTag.rank) :
    (rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      rootSpan t.tag K (simpleOrbitRoots t (t.orbitIndex (j (t.orbitMin a)))) ⊓
        twistedFixedGroup t K σ := by
  have hw₀ := mem_relWeylTwist_of_forall_length_le hmax
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw₀)
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport t.tag K).1 w₀ _ ?_, image_smul_negSimpleOrbitRoots hj hw₀,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rintro _ ⟨i, -, rfl⟩
  exact isRoot_neg_single _ i

end Opposition

theorem map_conj_graphFixedNegUnipotent
    {w₀ : WeylGroup t.tag}
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    (graphFixedNegUnipotent t K σ).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      graphFixedPosUnipotent t K σ := by
  have h₀ := reversesSigns_of_forall_length_le hmax
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ
      ((mem_relWeylTwist t).1 (mem_relWeylTwist_of_forall_length_le hmax))
  have hV := (canonical_weyl_root_transport t.tag K).1 w₀ {α | IsRoot t.tag α ∧ height α < 0}
    fun α hα => hα.1
  have himage : (fun α => w₀ • α) '' {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ height α < 0} =
      {α | IsRoot t.tag α ∧ 0 < height α} := by
    ext γ
    constructor
    · rintro ⟨β, ⟨hβ, hβn⟩, rfl⟩
      exact ⟨IsRoot.smul hβ w₀, h₀.height_smul_pos hβ hβn⟩
    · rintro ⟨hγ, hγp⟩
      exact ⟨w₀⁻¹ • γ, ⟨IsRoot.smul hγ w₀⁻¹, h₀.inv _ hγ hγp⟩, smul_inv_smul w₀ γ⟩
  rw [himage] at hV
  rw [graphFixedNegUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective]
  change (negUnipotent t.tag K).map _ ⊓ _ = posUnipotent t.tag K ⊓ _
  rw [negUnipotent, hV, map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rfl

variable (t K σ) in
theorem exists_fixed_opposite_data
    (hσ : Function.Surjective σ) :
    ∃ (n₀ : ModGL t.tag K) (δ : Fin t.foldedTag.rank → Fin t.foldedTag.rank),
      n₀ ∈ graphFixedRootGroup t K σ ∧ (∀ a, δ (δ a) = a) ∧
      (graphFixedRootBorel t K σ).map (MulAut.conj n₀).toMonoidHom =
        graphFixedOppositeBorel t K σ ∧
      (graphFixedNegUnipotent t K σ).map (MulAut.conj n₀).toMonoidHom =
        graphFixedPosUnipotent t K σ ∧
      ∀ a, (rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
          twistedFixedGroup t K σ).map (MulAut.conj n₀).toMonoidHom =
        rootSpan t.tag K (simpleOrbitRoots t (δ a)) ⊓ twistedFixedGroup t K σ := by
  obtain ⟨w₀, hmax, -, -, hsq, -, -⟩ := weyl_longest_element t.tag
  have hw₀ := mem_relWeylTwist_of_forall_length_le hmax
  have hsq' : w₀ * w₀ = 1 := by rw [← pow_two]; exact hsq
  choose j hj using exists_smul_single_eq_neg (reversesSigns_of_forall_length_le hmax) hsq'
  exact ⟨canonicalRep (coxeterSystem t.tag) K w₀, fun a => t.orbitIndex (j (t.orbitMin a)),
    canonicalRep_mem_graphFixedRootGroup hw₀, orbitIndex_apply_orbitMin_involutive hj hw₀ hsq',
    map_conj_graphFixedRootBorel hmax hσ, map_conj_graphFixedNegUnipotent hmax,
    map_conj_rootSpan_negSimpleOrbitRoots hj hmax⟩

theorem exceptional_fixed_minimal_Borel_intersections
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) :
    (∀ A : Subgroup (ModGL t.tag K), A ≤ graphFixedRootGroup t K σ.toRingHom →
      (graphFixedRootBorel t K σ.toRingHom ⋖ A ↔
        ∃ a, A = graphFixedParabolic t K σ.toRingHom {a})) ∧
    Function.Injective
      (fun a : Fin t.foldedTag.rank => graphFixedParabolic t K σ.toRingHom {a}) ∧
    (∀ a, ((graphFixedParabolic t K σ.toRingHom {a} ⊓ graphFixedNegUnipotent t K σ.toRingHom :
        Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) =
      Set.range fun c : orbitField t K σ.toRingHom a =>
        (orbitY t K σ.toRingHom a c : ModGL t.tag K)) ∧
    (∀ A : Subgroup (ModGL t.tag K), A ≤ graphFixedRootGroup t K σ.toRingHom →
      (graphFixedOppositeBorel t K σ.toRingHom ⋖ A ↔
        ∃ a, A = graphFixedOppositeMinimalParabolic t K σ.toRingHom a)) ∧
    Function.Injective (graphFixedOppositeMinimalParabolic t K σ.toRingHom) ∧
    ∀ a, ((graphFixedOppositeMinimalParabolic t K σ.toRingHom a ⊓
        graphFixedPosUnipotent t K σ.toRingHom : Subgroup (ModGL t.tag K)) :
          Set (ModGL t.tag K)) =
      Set.range fun c : orbitField t K σ.toRingHom a =>
        (orbitX t K σ.toRingHom a c : ModGL t.tag K) := by
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hPinj : Function.Injective
      (fun a : Fin t.foldedTag.rank => graphFixedParabolic t K σ.toRingHom {a}) :=
    fun _ _ h => Set.singleton_injective (graphFixedParabolic_injective hσ h)
  obtain ⟨n₀, δ, hn₀, hδδ, hB, hV, hY⟩ := exists_fixed_opposite_data t K σ.toRingHom hσ
  set φ : ModGL t.tag K →* ModGL t.tag K := (MulAut.conj n₀).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj n₀).injective
  have hφsurj : Function.Surjective φ := (MulAut.conj n₀).surjective
  have hP : ∀ a, (graphFixedParabolic t K σ.toRingHom {a}).map φ =
      graphFixedOppositeMinimalParabolic t K σ.toRingHom (δ a) := fun a => by
    rw [graphFixedParabolic_singleton_eq, Subgroup.map_sup, hB, hY,
      graphFixedOppositeMinimalParabolic, closure_range_orbitX]
  have hQ : ∀ b, graphFixedOppositeMinimalParabolic t K σ.toRingHom b =
      (graphFixedParabolic t K σ.toRingHom {δ b}).map φ := fun b => by rw [hP, hδδ]
  refine ⟨fun A hA => graphFixedRootBorel_covBy_iff hσ hA, hPinj,
    fun a => coe_graphFixedParabolic_singleton_inf_negUnipotent hσ a, fun A hA => ?_,
    fun a b h => ?_, fun b => ?_⟩
  · have hAc : (A.comap φ).map φ = A := Subgroup.map_comap_eq_self_of_surjective hφsurj A
    have hAcC : A.comap φ ≤ graphFixedRootGroup t K σ.toRingHom := fun x hx => by
      have h1 : n₀ * x * n₀⁻¹ ∈ graphFixedRootGroup t K σ.toRingHom := hA hx
      have h2 := mul_mem (mul_mem (inv_mem hn₀) h1) hn₀
      simpa [mul_assoc] using h2
    rw [← hB, ← hAc, covBy_map_conj_iff, graphFixedRootBorel_covBy_iff hσ hAcC]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨δ a, by rw [ha, hP]⟩
    · rintro ⟨b, hb⟩
      refine ⟨δ b, Subgroup.map_injective hφinj ?_⟩
      rw [hb, hQ]
  · rw [hQ, hQ] at h
    have := hPinj (Subgroup.map_injective hφinj h)
    rw [← hδδ a, ← hδδ b]
    exact congrArg δ this
  · rw [hQ, ← hV, ← Subgroup.map_inf_eq _ _ φ hφinj,
      graphFixedParabolic_singleton_inf_negUnipotent hσ, hY, hδδ,
      coe_rootSpan_simpleOrbitRoots_inf]

end CFSG.LieType.Chevalley
