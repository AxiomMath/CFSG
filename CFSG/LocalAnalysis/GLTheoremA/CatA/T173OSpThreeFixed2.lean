module
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeUnitary2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeRank
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
  CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LieType.SeitzGeneration
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

theorem spPrimaryBlocks_of_order_three (hF : Nat.card F = 2) (hℓ : 1 ≤ ℓ) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    SpPrimaryBlocks 2 1 3 d (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d) := by
  have hxp : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hker := CFSG.HardMathSupport.Dickson.Bal207.ker_proj_eq_bot_of_two (r := ℓ) hℓ hF
    (Or.inl rfl)
  have ha1 : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d ≠ 1 := fun h =>
    hd1 ((MonoidHom.ker_eq_bot_iff _).1 hker (by rw [h, map_one]))
  have ha : orderOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hd3, map_one]) ha1
  have hK : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  exact (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := 1) (p := 3) (r := ℓ)
    (K := F) Nat.prime_two le_rfl hK Nat.prime_three (by norm_num) (by norm_num) hℓ
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d) ha).2 d rfl hxp

theorem spFixedFactor_eq_bot_of_spFixedDim_eq_zero [CharP F 2] {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hd : spFixedDim d = 0) : spFixedFactor d = ⊥ := by
  have hsq : Squarefree (minpoly F (spEnd d)) :=
    (CFSG.RankThree.Classical.altPrimaryData_spLin (p := 3) (x := d)
      (three_ne_zero_of_charP_two (F := F)) hd3).squarefree
  have hbot : primaryComponent (spEnd d) (X - 1) = ⊥ := by
    rw [spFixedDim] at hd
    exact Submodule.finrank_eq_zero.mp hd
  have hXnot : (X - 1 : F[X]) ∉ primaryFactors (spEnd d) := fun hmem =>
    primaryComponent_ne_bot hsq hmem hbot
  rw [spFixedFactor, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hmap : ((spLin ℓ F) g : Module.End F (Fin ℓ ⊕ Fin ℓ → F)) = 1 := by
    refine ext_primaryComponent hsq fun k hk v hv => ?_
    rw [Module.End.one_apply]
    exact (mem_spSupported.mp hg).2 k hk (by rintro rfl; exact hXnot hk) v hv
  apply spLin_injective
  rw [map_one]
  exact Units.ext hmap

theorem two_le_fixed_half [CharP F 2] (hF : Nat.card F = 2) (hℓ : 1 ≤ ℓ)
    {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple ↥⁅spFixedFactor d, spFixedFactor d⁆)
    (blocks : SpPrimaryBlocks 2 1 3 d
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d))
    {s : ℕ} (hs : spFixedDim d = 2 * s) : 2 ≤ s := by
  have hns : ¬ Group.IsSolvable ↥⁅spFixedFactor d, spFixedFactor d⁆ := by
    intro hs
    haveI : Group.IsPerfect ↥⁅spFixedFactor d, spFixedFactor d⁆ :=
      Group.isPerfect_def.mpr hQ.1
    haveI : Nontrivial ↥⁅spFixedFactor d, spFixedFactor d⁆ := by
      haveI : IsSimpleGroup (↥⁅spFixedFactor d, spFixedFactor d⁆ ⧸
          Subgroup.center ↥⁅spFixedFactor d, spFixedFactor d⁆) := hQ.2
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥⁅spFixedFactor d,
        spFixedFactor d⁆)).nontrivial
    exact Group.IsPerfect.not_isSolvable _ hs
  rcases Nat.lt_or_ge s 2 with hlt | hge
  · have hs01 : s = 0 ∨ s = 1 := by omega
    rcases hs01 with rfl | rfl
    ·
      have hbot : spFixedFactor d = ⊥ := by
        refine spFixedFactor_eq_bot_of_spFixedDim_eq_zero hd3 ?_
        rw [hs]
      have hsolv : Group.IsSolvable ↥⁅spFixedFactor d, spFixedFactor d⁆ := by
        rw [hbot, Subgroup.commutator_bot_left]
        infer_instance
      exact (hns hsolv).elim
    ·
      have hdim2 : spFixedDim d = 2 := by rw [hs]
      have hcard : Nat.card ↥(spFixedFactor d) = 6 := by
        rw [card_spFixedFactor_of_dim_two (ℓ := 2) (f := 1) (p := 3) blocks hdim2, hF]
        norm_num
      have hsolv : Group.IsSolvable ↥(spFixedFactor d) := by
        haveI : Fintype ↥(spFixedFactor d) := Fintype.ofFinite _
        refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
          (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
        rw [← Nat.card_eq_fintype_card, hcard]
        norm_num
      exact (hns (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (Subgroup.commutator_le_self (spFixedFactor d)))
        (Subgroup.inclusion_injective _))).elim
  · exact hge

theorem spSupported_unitary_le_centralizer_fixed_commutator [CharP F 2]
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) :
    spSupported d ({X ^ 2 + X + 1} : Set F[X]) ≤
      Subgroup.centralizer (((⁅spSupported d ({X - 1} : Set F[X]),
        spSupported d ({X - 1} : Set F[X])⁆) : Subgroup ↥(StatedSp ℓ F)) :
          Set ↥(StatedSp ℓ F)) := by
  intro y hy
  have hO : Disjoint ({X ^ 2 + X + 1} : Set F[X]) {X - 1} := by
    rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
    exact fun h => CFSG.HardMathSupport.Dickson.Bal207.X_sq_add_X_add_one_ne h
  have hcomm : ∀ u ∈ spSupported d ({X - 1} : Set F[X]), y * u = u * y := fun u hu =>
    commute_spSupported_of_disjoint hd3 hO hy hu
  have hle : ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆ ≤
      Subgroup.centralizer ({y} : Set ↥(StatedSp ℓ F)) := by
    refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
    have huC : u ∈ Subgroup.centralizer ({y} : Set ↥(StatedSp ℓ F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcomm u hu
    have hvC : v ∈ Subgroup.centralizer ({y} : Set ↥(StatedSp ℓ F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcomm v hv
    rw [commutatorElement_def]
    exact (Subgroup.centralizer _).mul_mem
      ((Subgroup.centralizer _).mul_mem
        ((Subgroup.centralizer _).mul_mem huC hvC) ((Subgroup.centralizer _).inv_mem huC))
      ((Subgroup.centralizer _).inv_mem hvC)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' := hle hx
  rw [Subgroup.mem_centralizer_iff] at hx'
  exact (hx' y (Set.mem_singleton y)).symm

theorem mem_commutator_fixed_of_cube_one (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1)
    (blocks : SpPrimaryBlocks 2 1 3 d
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj ℓ F d))
    {s : ℕ} (hs : spFixedDim d = 2 * s) (h2s : 2 ≤ s) {a : ↥(StatedSp ℓ F)}
    (ha : a ∈ spFixedFactor d) (ha3 : a ^ 3 = 1) :
    a ∈ ⁅spFixedFactor d, spFixedFactor d⁆ := by
  rcases Nat.eq_or_lt_of_le h2s with hs2 | hs3
  ·
    have hd4 : spFixedDim d = 4 := by rw [hs, ← hs2]
    exact (spFixed_four_two (ℓ := 2) (f := 1) (p := 3) hF blocks hd4).2
      Nat.prime_three (by norm_num) a ha ha3
  ·
    have hs3' : 3 ≤ s := hs3
    have hd4 : ¬ (spFixedDim d = 4 ∧ Nat.card F = 2) := by
      rintro ⟨h4, -⟩
      rw [hs] at h4
      omega
    have hlist : SpFixedListed d := by
      refine ⟨?_, ?_⟩
      · rw [hs]; omega
      · rintro ⟨h2, -⟩
        rw [hs] at h2
        omega
    have hK : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
    have hq := spFixedFactor_isQuasisimple (ℓ := 2) (f := 1) (p := 3) hK Nat.prime_two
      (by norm_num) blocks hlist hd4
    have hsub : ⁅spFixedFactor d, spFixedFactor d⁆ = spFixedFactor d := by
      rw [← Subgroup.map_subtype_commutator, Group.isPerfect_def.mp hq.1, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [hsub]
    exact ha

theorem commute_fixed_of_fixes [CharP F 2] (hF : Nat.card F = 2)
    {d a g : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hg : g ∈ spFixedFactor d) (had : a * d = d * a)
    (ha : ∀ v ∈ primaryComponent (spEnd d) (X - 1), spEnd a v = v) :
    a * g = g * a := by
  have hsq : Squarefree (minpoly F (spEnd d)) :=
    (CFSG.RankThree.Classical.altPrimaryData_spLin (p := 3) (x := d)
      (three_ne_zero_of_charP_two (F := F)) hd3).squarefree
  have hsa : Commute (spEnd a) (spEnd d) := by
    show spEnd a * spEnd d = spEnd d * spEnd a
    rw [← spEnd_mul, ← spEnd_mul, had]
  have hsg : Commute (spEnd g) (spEnd d) := by
    show spEnd g * spEnd d = spEnd d * spEnd g
    rw [← spEnd_mul, ← spEnd_mul, (mem_spSupported.mp hg).1]
  have hg3 : ∀ w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1), spEnd g w = w := by
    intro w hw
    by_cases hmem : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (spEnd d)
    · exact (mem_spSupported.mp hg).2 _ hmem (by
        rw [Set.mem_singleton_iff]
        exact CFSG.HardMathSupport.Dickson.Bal207.X_sq_add_X_add_one_ne) w hw
    · have hbot := primaryComponent_eq_bot_of_not_mem
        (CFSG.HardMathSupport.Dickson.Bal207.irreducible_X_sq_add_X_add_one_of_card hF
          (Or.inl rfl)) (by monicity!) hmem
      rw [hbot, Submodule.mem_bot] at hw
      rw [hw, map_zero]
  have hcomm : spEnd (a * g) = spEnd (g * a) := by
    rw [spEnd_mul, spEnd_mul]
    refine ext_primaryComponent hsq fun k hk w hw => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    rcases CFSG.HardMathSupport.Dickson.Bal207.primaryFactor_cases_of_card hF (Or.inl rfl)
      (spEnd_pow hd3) hk with rfl | rfl
    · have hgW : spEnd g w ∈ primaryComponent (spEnd d) (X - 1) :=
        apply_mem_primaryComponent hsg hw
      rw [ha w hw, ha _ hgW]
    · have haW : spEnd a w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) :=
        apply_mem_primaryComponent hsa hw
      rw [hg3 w hw, hg3 _ haW]
  exact spLin_injective (Units.ext hcomm)

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
