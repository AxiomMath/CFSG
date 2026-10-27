module

public import CFSG.LargeExtraspecial.S8CBF3D4Root
public import CFSG.LieType.Chevalley.TrialityFieldTwoRoots
public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.TrialityFieldTwo CFSG.LieType.Chevalley.ExceptionalCover
open scoped commutatorElement

section Coord

variable {K : Type} [Field K] [Finite K]

theorem rootCoord_pinnedX_eq
    {τ : Tag}
    {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α ∧ 0 < height α) (hβ : IsRoot τ β ∧ 0 < height β)
    (hh : height α ≤ height β) (c : K) :
    rootCoord hα (pinnedX τ K β c) = if β = α then c else 0 := by
  split_ifs with h
  · subst h
    exact rootCoord_self hα c
  · exact rootCoord_pinnedX_of_ne hα hβ hh h c

theorem rootCoord_of_mem_succ
    {τ : Tag}
    {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α ∧ 0 < height α) {g : ModGL τ K}
    (hg : g ∈ heightSeries τ K (height α + 1)) : rootCoord hα g = 0 :=
  rootCoord_of_mem_coordKer hα (heightSeries_succ_le_coordKer α hg)

end Coord

theorem trialityRoot_pos (j : Fin 6) :
    IsRoot TwistTag.D4.tag (trialityRoot j) ∧ 0 < height (trialityRoot j) :=
  isRoot_trialityRoot j 0

section Members

variable {K : Type} [Field K]

theorem root_four_five_mem :
    trialityRoot 4 ∈ heightSet TwistTag.D4.tag 4 ∧ trialityRoot 5 ∈ heightSet TwistTag.D4.tag 5 :=
  ⟨mem_heightSet_of (by decide +kernel) (by decide +kernel),
    mem_heightSet_of (by decide +kernel) (by decide +kernel)⟩

variable (σ : K →+* K)

theorem x₁_mem (a : K) :
    (trialityX₁ K σ a : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 1 := by
  obtain ⟨m0, m1, m2⟩ := orbit_zero_mem
  rw [trialityX₁, coe_trialityOrbitProd]
  exact mul_mem (mul_mem (pinnedX_mem_heightSeries m0 _) (pinnedX_mem_heightSeries m1 _))
    (pinnedX_mem_heightSeries m2 _)

theorem x₂_mem
    (b : trialityFixedField K σ) :
    (trialityX₂ K σ b : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 1 :=
  pinnedX_mem_heightSeries root_one_mem _

theorem x₃_mem (c : K) :
    (trialityX₃ K σ c : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 2 := by
  obtain ⟨m0, m1, m2⟩ := orbit_two_mem
  rw [trialityX₃, coe_trialityOrbitProd]
  exact mul_mem (mul_mem (pinnedX_mem_heightSeries m0 _) (pinnedX_mem_heightSeries m1 _))
    (pinnedX_mem_heightSeries m2 _)

theorem x₄_mem (d : K) :
    (trialityX₄ K σ d : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 3 := by
  obtain ⟨m0, m1, m2⟩ := orbit_three_mem
  rw [trialityX₄, coe_trialityOrbitProd]
  exact mul_mem (mul_mem (pinnedX_mem_heightSeries m0 _) (pinnedX_mem_heightSeries m1 _))
    (pinnedX_mem_heightSeries m2 _)

theorem x₅_mem
    (e : trialityFixedField K σ) :
    (trialityX₅ K σ e : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 4 :=
  pinnedX_mem_heightSeries root_four_five_mem.1 _

theorem x₆_mem
    (f : trialityFixedField K σ) :
    (trialityX₆ K σ f : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 5 :=
  pinnedX_mem_heightSeries root_four_five_mem.2 _

theorem heightSeries_le_of_le
    {h h' : ℤ} (hh : h ≤ h') :
    heightSeries TwistTag.D4.tag K h' ≤ heightSeries TwistTag.D4.tag K h :=
  rootSpan_mono fun _ hα => ⟨hα.1, hα.2.1, hh.trans hα.2.2⟩

theorem tail_mem (c d : K)
    (e f : trialityFixedField K σ) :
    (trialityX₃ K σ c : ModGL TwistTag.D4.tag K) * (trialityX₄ K σ d : ModGL TwistTag.D4.tag K) *
      (trialityX₅ K σ e : ModGL TwistTag.D4.tag K) * (trialityX₆ K σ f : ModGL TwistTag.D4.tag K) ∈
        heightSeries TwistTag.D4.tag K 2 :=
  mul_mem (mul_mem (mul_mem (x₃_mem σ c)
    (heightSeries_le_of_le (show (2 : ℤ) ≤ 3 by norm_num) (x₄_mem σ d)))
    (heightSeries_le_of_le (show (2 : ℤ) ≤ 4 by norm_num) (x₅_mem σ e)))
    (heightSeries_le_of_le (show (2 : ℤ) ≤ 5 by norm_num) (x₆_mem σ f))

theorem orbitProd_zero (j : Fin 6) :
    (trialityOrbitProd K σ (trialityRoot j) 0 : ModGL TwistTag.D4.tag K) = 1 := by
  rw [coe_trialityOrbitProd, map_zero, map_zero, pinnedX_zero, pinnedX_zero, pinnedX_zero,
    mul_one, mul_one]

theorem x₂_zero :
    (trialityX₂ K σ 0 : ModGL TwistTag.D4.tag K) = 1 :=
  pinnedX_zero _ _ _

end Members

section Param


variable {K : Type} [Field K] [Finite K] (σ : K →+* K)

theorem rootCoord_orbitProd {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α ∧ 0 < height α) {j : Fin 6}
    (hh : height α ≤ height (trialityRoot j)) (c : K) :
    rootCoord hα (trialityOrbitProd K σ (trialityRoot j) c : ModGL TwistTag.D4.tag K) =
      (if trialityRoot j = α then c else 0) + (if ρL (trialityRoot j) = α then σ c else 0) +
        (if ρL2 (trialityRoot j) = α then σ (σ c) else 0) := by
  have h0 := trialityRoot_pos j
  have h1 := isRoot_trialityRoot j 1
  have h2 := isRoot_trialityRoot j 2
  rw [pow_one] at h1
  have hh1 : height α ≤ height (ρL (trialityRoot j)) := by
    rw [height_permLattice]
    exact hh
  have hh2 : height α ≤ height (ρL2 (trialityRoot j)) := by
    rw [height_permLattice]
    exact hh
  have m0 : pinnedX TwistTag.D4.tag K (trialityRoot j) c ∈
      heightSeries TwistTag.D4.tag K (height α) := pinnedX_mem_heightSeries ⟨h0.1, h0.2, hh⟩ c
  have m1 : pinnedX TwistTag.D4.tag K (ρL (trialityRoot j)) (σ c) ∈
      heightSeries TwistTag.D4.tag K (height α) := pinnedX_mem_heightSeries ⟨h1.1, h1.2, hh1⟩ _
  have m2 : pinnedX TwistTag.D4.tag K (ρL2 (trialityRoot j)) (σ (σ c)) ∈
      heightSeries TwistTag.D4.tag K (height α) := pinnedX_mem_heightSeries ⟨h2.1, h2.2, hh2⟩ _
  rw [coe_trialityOrbitProd, rootCoord_mul hα (mul_mem m0 m1) m2, rootCoord_mul hα m0 m1,
    rootCoord_pinnedX_eq hα h0 hh, rootCoord_pinnedX_eq hα h1 hh1, rootCoord_pinnedX_eq hα h2 hh2]

theorem rootCoord_tail_four (d : K) (e f : trialityFixedField K σ) :
    rootCoord (trialityRoot_pos 3) ((trialityX₄ K σ d : ModGL TwistTag.D4.tag K) *
      (trialityX₅ K σ e : ModGL TwistTag.D4.tag K) *
        (trialityX₆ K σ f : ModGL TwistTag.D4.tag K)) = d := by
  have h3 : height (trialityRoot 3) = 3 := by decide
  have m4 := x₄_mem σ d
  have m5 := heightSeries_le_of_le (K := K) (show (3 : ℤ) ≤ 4 by norm_num) (x₅_mem σ e)
  have m6 := heightSeries_le_of_le (K := K) (show (3 : ℤ) ≤ 5 by norm_num) (x₆_mem σ f)
  rw [← h3] at m4 m5 m6
  rw [rootCoord_mul _ (mul_mem m4 m5) m6, rootCoord_mul _ m4 m5,
    rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 3) + 1 ≤ 4 by
      rw [h3]; norm_num) (x₅_mem σ e)),
    rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 3) + 1 ≤ 5 by
      rw [h3]; norm_num) (x₆_mem σ f)), add_zero, add_zero, trialityX₄,
    rootCoord_orbitProd σ _ le_rfl, ite_eq_left rfl, ite_eq_right (by decide +kernel),
    ite_eq_right (by decide +kernel), add_zero, add_zero]

theorem rootCoord_tail_three (c d : K) (e f : trialityFixedField K σ) :
    rootCoord (trialityRoot_pos 2) ((trialityX₃ K σ c : ModGL TwistTag.D4.tag K) *
      (trialityX₄ K σ d : ModGL TwistTag.D4.tag K) *
        (trialityX₅ K σ e : ModGL TwistTag.D4.tag K) *
          (trialityX₆ K σ f : ModGL TwistTag.D4.tag K)) = c := by
  have h2 : height (trialityRoot 2) = 2 := by decide
  have hs : ∀ {h : ℤ}, height (trialityRoot 2) + 1 ≤ h → ∀ {g : ModGL TwistTag.D4.tag K},
      g ∈ heightSeries TwistTag.D4.tag K h → rootCoord (trialityRoot_pos 2) g = 0 :=
    fun hh _ hg => rootCoord_of_mem_succ _ (heightSeries_le_of_le hh hg)
  have m3 := x₃_mem σ c
  have m4 := heightSeries_le_of_le (K := K) (show (2 : ℤ) ≤ 3 by norm_num) (x₄_mem σ d)
  have m5 := heightSeries_le_of_le (K := K) (show (2 : ℤ) ≤ 4 by norm_num) (x₅_mem σ e)
  have m6 := heightSeries_le_of_le (K := K) (show (2 : ℤ) ≤ 5 by norm_num) (x₆_mem σ f)
  rw [← h2] at m3 m4 m5 m6
  rw [rootCoord_mul _ (mul_mem (mul_mem m3 m4) m5) m6, rootCoord_mul _ (mul_mem m3 m4) m5,
    rootCoord_mul _ m3 m4, hs (by rw [h2]; norm_num) (x₄_mem σ d),
    hs (by rw [h2]; norm_num) (x₅_mem σ e), hs (by rw [h2]; norm_num) (x₆_mem σ f), add_zero,
    add_zero, add_zero, trialityX₃, rootCoord_orbitProd σ _ le_rfl, ite_eq_left rfl,
    ite_eq_right (by decide +kernel), ite_eq_right (by decide +kernel), add_zero, add_zero]

@[expose] noncomputable def paramProd (a : K) (b : trialityFixedField K σ) (c d : K)
    (e f : trialityFixedField K σ) : ModGL TwistTag.D4.tag K :=
  (trialityX₁ K σ a : ModGL TwistTag.D4.tag K) * (trialityX₂ K σ b : ModGL TwistTag.D4.tag K) *
    ((trialityX₃ K σ c : ModGL TwistTag.D4.tag K) * (trialityX₄ K σ d : ModGL TwistTag.D4.tag K) *
      (trialityX₅ K σ e : ModGL TwistTag.D4.tag K) * (trialityX₆ K σ f : ModGL TwistTag.D4.tag K))

theorem rootCoord_paramProd (a : K) (b : trialityFixedField K σ) (c d : K)
    (e f : trialityFixedField K σ) :
    rootCoord (trialityRoot_pos 0) (paramProd σ a b c d e f) = a ∧
      rootCoord (trialityRoot_pos 1) (paramProd σ a b c d e f) = b := by
  have h0 : height (trialityRoot 0) = 1 := by decide
  have h1 : height (trialityRoot 1) = 1 := by decide
  have m1 := x₁_mem σ a
  have m2 := x₂_mem σ b
  have mt := heightSeries_le_of_le (K := K) (show (1 : ℤ) ≤ 2 by norm_num) (tail_mem σ c d e f)
  have hr1 := trialityRoot_pos 1
  constructor
  · rw [← h0] at m1 m2 mt
    rw [paramProd, rootCoord_mul _ (mul_mem m1 m2) mt, rootCoord_mul _ m1 m2,
      rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 0) + 1 ≤ 2 by
        rw [h0]; norm_num) (tail_mem σ c d e f)), add_zero, trialityX₁,
      rootCoord_orbitProd σ _ le_rfl, ite_eq_left rfl, ite_eq_right (by decide +kernel),
      ite_eq_right (by decide +kernel), add_zero, add_zero]
    change a + rootCoord _ (pinnedX TwistTag.D4.tag K (trialityRoot 1) b) = a
    rw [rootCoord_pinnedX_eq _ hr1 (by rw [h0, h1]), ite_eq_right (by decide +kernel), add_zero]
  · rw [← h1] at m1 m2 mt
    rw [paramProd, rootCoord_mul _ (mul_mem m1 m2) mt, rootCoord_mul _ m1 m2,
      rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 1) + 1 ≤ 2 by
        rw [h1]; norm_num) (tail_mem σ c d e f)), add_zero, trialityX₁,
      rootCoord_orbitProd σ _ (by rw [h0, h1]), ite_eq_right (by decide +kernel),
      ite_eq_right (by decide +kernel), ite_eq_right (by decide +kernel), add_zero, add_zero]
    change 0 + rootCoord _ (pinnedX TwistTag.D4.tag K (trialityRoot 1) b) = b
    rw [rootCoord_pinnedX_eq _ hr1 le_rfl, ite_eq_left rfl, zero_add]

variable [CharP K 2]

theorem exists_paramProd (σ' : K ≃+* K) (hσ : σ' ^ 3 = 1) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom) :
    ∃ (a : K) (b : trialityFixedField K σ'.toRingHom) (c d : K)
      (e f : trialityFixedField K σ'.toRingHom), g = paramProd σ'.toRingHom a b c d e f := by
  obtain ⟨-, -, -, -, -, -, hbij, -⟩ :=
    even_triality_positive_orbit_parametrization K σ' (TrialityCover.toRingHom_pow_three σ' hσ)
  obtain ⟨p, -, hp⟩ := hbij.surjOn hg
  refine ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, ?_⟩
  rw [← hp, paramProd]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem xs_mem_graphFixedPosUnipotent (σ' : K ≃+* K) (hσ : σ' ^ 3 = 1) :
    (∀ a, (trialityX₁ K σ'.toRingHom a : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom) ∧
    (∀ b, (trialityX₂ K σ'.toRingHom b : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom) ∧
    (∀ c, (trialityX₃ K σ'.toRingHom c : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom) ∧
    (∀ d, (trialityX₄ K σ'.toRingHom d : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom) ∧
    (∀ e, (trialityX₅ K σ'.toRingHom e : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom) ∧
    (∀ f, (trialityX₆ K σ'.toRingHom f : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom) := by
  obtain ⟨⟨f1, -, h1⟩, ⟨f2, -, h2⟩, ⟨f3, -, h3⟩, ⟨f4, -, h4⟩, ⟨f5, -, h5⟩, ⟨f6, -, h6⟩, -⟩ :=
    even_triality_positive_orbit_parametrization K σ' (TrialityCover.toRingHom_pow_three σ' hσ)
  exact ⟨fun a => h1 a ▸ (f1 (Multiplicative.ofAdd a)).2,
    fun b => h2 b ▸ (f2 (Multiplicative.ofAdd b)).2,
    fun c => h3 c ▸ (f3 (Multiplicative.ofAdd c)).2,
    fun d => h4 d ▸ (f4 (Multiplicative.ofAdd d)).2,
    fun e => h5 e ▸ (f5 (Multiplicative.ofAdd e)).2,
    fun f => h6 f ▸ (f6 (Multiplicative.ofAdd f)).2⟩

theorem exists_param_of_mem_middle (σ' : K ≃+* K) (hσ : σ' ^ 3 = 1)
    {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedParabolicRadical TwistTag.D4 K σ'.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}) :
    ∃ (a c d : K) (e f : trialityFixedField K σ'.toRingHom),
      g = paramProd σ'.toRingHom a 0 c d e f := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ :=
    exists_paramProd σ' hσ (graphFixedParabolicRadical_le TwistTag.D4 K σ'.toRingHom _ hg)
  have hb : rootCoord (trialityRoot_pos 1) (paramProd σ'.toRingHom a b c d e f) = 0 := by
    refine rootCoord_of_mem_coordKer _ ?_
    have hQ := (mem_inf.1 hg).1
    rw [orbitUnion_middle] at hQ
    refine rootSpan_mono (fun α hα => ?_) hQ
    obtain ⟨⟨hαr, hαp⟩, hαA⟩ := hα
    refine ⟨hαr, hαp, ?_, ?_⟩
    · have h1 : height (trialityRoot 1) = 1 := by decide
      rw [h1]
      exact hαp
    · rintro rfl
      apply hαA
      refine ⟨⟨hαr, fun i hi => ?_⟩, hαr, hαp⟩
      rw [Set.mem_singleton_iff] at hi
      revert hi
      revert i
      decide
  rw [(rootCoord_paramProd σ'.toRingHom a b c d e f).2] at hb
  have hb0 : b = 0 := Subtype.ext hb
  exact ⟨a, c, d, e, f, by rw [hb0]⟩

theorem exists_param_of_mem_three (σ' : K ≃+* K) (hσ : σ' ^ 3 = 1)
    {g : ModGL TwistTag.D4.tag K} (hg3 : g ∈ heightSeries TwistTag.D4.tag K 3)
    (hgΓ : g ∈ twistedFixedGroup TwistTag.D4 K σ'.toRingHom) :
    ∃ (d : K) (e f : trialityFixedField K σ'.toRingHom),
      g = (trialityX₄ K σ'.toRingHom d : ModGL TwistTag.D4.tag K) *
        (trialityX₅ K σ'.toRingHom e : ModGL TwistTag.D4.tag K) *
          (trialityX₆ K σ'.toRingHom f : ModGL TwistTag.D4.tag K) := by
  have hgU : g ∈ graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom :=
    mem_inf.2 ⟨heightSeries_le_posUnipotent 3 hg3, hgΓ⟩
  obtain ⟨a, b, c, d, e, f, rfl⟩ := exists_paramProd σ' hσ hgU
  have h0 : height (trialityRoot 0) = 1 := by decide
  have h1 : height (trialityRoot 1) = 1 := by decide
  have h2 : height (trialityRoot 2) = 2 := by decide
  obtain ⟨ha, hb⟩ := rootCoord_paramProd σ'.toRingHom a b c d e f
  rw [rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 0) + 1 ≤ 3 by
    rw [h0]; norm_num) hg3)] at ha
  rw [rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 1) + 1 ≤ 3 by
    rw [h1]; norm_num) hg3)] at hb
  have hb0 : b = 0 := Subtype.ext hb.symm
  subst hb0
  rw [← ha] at hg3 ⊢
  have e1 : paramProd σ'.toRingHom 0 0 c d e f =
      (trialityX₃ K σ'.toRingHom c : ModGL TwistTag.D4.tag K) *
        (trialityX₄ K σ'.toRingHom d : ModGL TwistTag.D4.tag K) *
          (trialityX₅ K σ'.toRingHom e : ModGL TwistTag.D4.tag K) *
            (trialityX₆ K σ'.toRingHom f : ModGL TwistTag.D4.tag K) := by
    rw [paramProd, trialityX₁, orbitProd_zero, x₂_zero, one_mul, one_mul]
  rw [e1] at hg3 ⊢
  have hc := rootCoord_tail_three σ'.toRingHom c d e f
  rw [rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 2) + 1 ≤ 3 by
    rw [h2]; norm_num) hg3)] at hc
  rw [← hc, trialityX₃, orbitProd_zero, one_mul]
  exact ⟨d, e, f, rfl⟩

theorem exists_param_of_mem_four (σ' : K ≃+* K) (hσ : σ' ^ 3 = 1)
    {g : ModGL TwistTag.D4.tag K} (hg4 : g ∈ heightSeries TwistTag.D4.tag K 4)
    (hgΓ : g ∈ twistedFixedGroup TwistTag.D4 K σ'.toRingHom) :
    ∃ e f : trialityFixedField K σ'.toRingHom,
      g = (trialityX₅ K σ'.toRingHom e : ModGL TwistTag.D4.tag K) *
          (trialityX₆ K σ'.toRingHom f : ModGL TwistTag.D4.tag K) := by
  obtain ⟨d, e, f, rfl⟩ := exists_param_of_mem_three σ' hσ
    (heightSeries_le_of_le (show (3 : ℤ) ≤ 4 by norm_num) hg4) hgΓ
  have h3 : height (trialityRoot 3) = 3 := by decide
  have hd := rootCoord_tail_four σ'.toRingHom d e f
  rw [rootCoord_of_mem_succ _ (heightSeries_le_of_le (show height (trialityRoot 3) + 1 ≤ 4 by
    rw [h3]; norm_num) hg4)] at hd
  rw [← hd, trialityX₄, orbitProd_zero, one_mul]
  exact ⟨e, f, rfl⟩

end Param

end CFSG.LargeExtraspecial.S8
