module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.SpinMinus
public import CFSG.ClassicalInvolution.WeakCT.TwistedAssembly

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

section Long

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

@[expose] noncomputable def rLong (n : ℕ) (b c : F) {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    SL(2, F) →* spinGroup (quadMinus n F b c) :=
  (minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false

omit hirr in
theorem rLong_tv01 {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) (x : F) :
    rLong n b c hk (tv 0 1 x) =
      (minusFrame n b c).longRoot (succ_ne_of_lt n hk) true false (.ofAdd x) := by
  rw [rLong, tv01_eq_upperSL2, HypFrame.longSL2_upperSL2]

omit hirr in
theorem rLong_tv10 {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) (x : F) :
    rLong n b c hk (tv 1 0 x) =
      (minusFrame n b c).longRoot (succ_ne_of_lt n hk).symm true false (.ofAdd x) := by
  rw [rLong, tv10_eq_lowerSL2, HypFrame.longSL2_lowerSL2]
  rfl

omit hirr in
theorem rLong_injective {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    Function.Injective (rLong n b c hk) :=
  SpinFrame.longSL2_injective _ _ _ _

theorem rLong_upper {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) (x : F) :
    rLong n b c hk (tv 0 1 x) ∈ (minusDatum n hirr).rootGroup (Pi.single k 1) := by
  rw [rLong_tv01]
  show _ ∈ minusRootGroup n hirr (Pi.single k 1)
  rw [minusRootGroup_single_of_lt n hirr hk]
  exact ⟨.ofAdd x, rfl⟩

theorem rLong_lower {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) (x : F) :
    rLong n b c hk (tv 1 0 x) ∈ (minusDatum n hirr).rootGroup (-Pi.single k 1) := by
  rw [rLong_tv10]
  show _ ∈ minusRootGroup n hirr (-Pi.single k 1)
  rw [minusRootGroup_neg_single_of_lt n hirr hk]
  exact ⟨.ofAdd x, rfl⟩

theorem rLong_param_upper {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    ∀ g ∈ (minusDatum n hirr).rootGroup (Pi.single k 1), ∃ x, rLong n b c hk (tv 0 1 x) = g := by
  intro g hg
  have hg' : g ∈ minusRootGroup n hirr (Pi.single k 1) := hg
  rw [minusRootGroup_single_of_lt n hirr hk] at hg'
  obtain ⟨a, rfl⟩ := hg'
  exact ⟨Multiplicative.toAdd a, by rw [rLong_tv01]; rfl⟩

theorem rLong_param_lower {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    ∀ g ∈ (minusDatum n hirr).rootGroup (-Pi.single k 1), ∃ x, rLong n b c hk (tv 1 0 x) = g := by
  intro g hg
  have hg' : g ∈ minusRootGroup n hirr (-Pi.single k 1) := hg
  rw [minusRootGroup_neg_single_of_lt n hirr hk] at hg'
  obtain ⟨a, rfl⟩ := hg'
  exact ⟨Multiplicative.toAdd a, by rw [rLong_tv10]; rfl⟩

@[expose] noncomputable def nodeDataLong {X : Type} [Group X] {U : Subgroup X}
    (ρ : SL(2, F) →* X) (hU : ρ.range = U) {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    NodeData (minusDatum n hirr) X k U :=
  NodeData.ofParam (rLong n b c hk) ρ hU (rLong_injective hk) (rLong_upper hirr hk)
    (rLong_lower hirr hk) (rLong_param_upper hirr hk) (rLong_param_lower hirr hk)

theorem nodeDataLong_isParam {X : Type} [Group X] {U : Subgroup X} (ρ : SL(2, F) →* X)
    (hU : ρ.range = U) {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    (nodeDataLong hirr ρ hU hk).IsParam (rLong n b c hk) ρ :=
  NodeData.ofParam_isParam hU (rLong_injective hk) (rLong_upper hirr hk) (rLong_lower hirr hk)
    (rLong_param_upper hirr hk) (rLong_param_lower hirr hk)

end Long

section ShortNode

variable {F : Type} [Field F] [Finite F] {b c : F} [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem shortBlock_upper_mem {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) (t : ShortField b c) :
    shortBlock hirr n k (tv 0 1 t) ∈ (minusDatum n hirr).rootGroup (Pi.single k 1) := by
  rw [shortBlock_tv01]
  show _ ∈ minusRootGroup n hirr (Pi.single k 1)
  rw [minusRootGroup_single_of_not_lt n hirr hk]
  exact ⟨_, rfl⟩

theorem shortBlock_lower_mem {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) (t : ShortField b c) :
    shortBlock hirr n k (tv 1 0 t) ∈ (minusDatum n hirr).rootGroup (-Pi.single k 1) := by
  rw [shortBlock_tv10]
  show _ ∈ minusRootGroup n hirr (-Pi.single k 1)
  rw [minusRootGroup_neg_single_of_not_lt n hirr hk]
  exact ⟨_, rfl⟩

theorem shortBlock_param_upper {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) :
    ∀ g ∈ (minusDatum n hirr).rootGroup (Pi.single k 1),
      ∃ t : ShortField b c, shortBlock hirr n k (tv 0 1 t) = g := by
  intro g hg
  have hg' : g ∈ minusRootGroup n hirr (Pi.single k 1) := hg
  rw [minusRootGroup_single_of_not_lt n hirr hk] at hg'
  obtain ⟨a, rfl⟩ := hg'
  obtain ⟨t, ht⟩ := exists_fieldCoord_eq (b := b) (c := c) (Multiplicative.toAdd a)
  exact ⟨t, by rw [shortBlock_tv01, ht, ofAdd_toAdd]⟩

theorem shortBlock_param_lower {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) :
    ∀ g ∈ (minusDatum n hirr).rootGroup (-Pi.single k 1),
      ∃ t : ShortField b c, shortBlock hirr n k (tv 1 0 t) = g := by
  intro g hg
  have hg' : g ∈ minusRootGroup n hirr (-Pi.single k 1) := hg
  rw [minusRootGroup_neg_single_of_not_lt n hirr hk] at hg'
  obtain ⟨a, rfl⟩ := hg'
  obtain ⟨t, ht⟩ := exists_starCoord_eq (b := b) (c := c) (Multiplicative.toAdd a)
  exact ⟨t, by rw [shortBlock_tv10, ht, ofAdd_toAdd]⟩

@[expose] noncomputable def nodeDataShort (h2 : (2 : F) ≠ 0) {X : Type} [Group X] {U : Subgroup X}
    (ρ : SL(2, ShortField b c) →* X) (hU : ρ.range = U) {k : Fin (n - 1)}
    (hk : ¬ k.val + 1 < n - 1) : NodeData (minusDatum n hirr) X k U :=
  NodeData.ofParam (shortBlock hirr n k) ρ hU (shortBlock_injective hirr h2 n k)
    (shortBlock_upper_mem hirr hk) (shortBlock_lower_mem hirr hk) (shortBlock_param_upper hirr hk)
    (shortBlock_param_lower hirr hk)

theorem nodeDataShort_isParam (h2 : (2 : F) ≠ 0) {X : Type} [Group X] {U : Subgroup X}
    (ρ : SL(2, ShortField b c) →* X) (hU : ρ.range = U) {k : Fin (n - 1)}
    (hk : ¬ k.val + 1 < n - 1) :
    (nodeDataShort hirr h2 ρ hU hk).IsParam (shortBlock hirr n k) ρ :=
  NodeData.ofParam_isParam hU (shortBlock_injective hirr h2 n k) (shortBlock_upper_mem hirr hk)
    (shortBlock_lower_mem hirr hk) (shortBlock_param_upper hirr hk) (shortBlock_param_lower hirr hk)

end ShortNode

section Orthogonal

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

omit hirr in
theorem commute_rLong_rLong {i j : Fin (n - 1)} (hi : i.val + 1 < n - 1) (hj : j.val + 1 < n - 1)
    (hij : i.val + 1 < j.val) (A B : SL(2, F)) :
    Commute (rLong n b c hi A) (rLong n b c hj B) := by
  have h1 : i ≠ j := Fin.ne_of_val_ne (by omega)
  have h2 : i ≠ ⟨j.val + 1, hj⟩ := Fin.ne_of_val_ne (by dsimp only; omega)
  have h3 : (⟨i.val + 1, hi⟩ : Fin (n - 1)) ≠ j := Fin.ne_of_val_ne (by dsimp only; omega)
  have h4 : (⟨i.val + 1, hi⟩ : Fin (n - 1)) ≠ ⟨j.val + 1, hj⟩ :=
    Fin.ne_of_val_ne (by dsimp only; omega)
  refine commute_of_tv (rLong n b c hi) (rLong n b c hj) (fun x y => ?_) A B
  simp only [rLong_tv01, rLong_tv10]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint _ _ h1 h2 h3 h4 _ _ _ _ _ _
  · exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint _ _ h2 h1 h4 h3 _ _ _ _ _ _
  · exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint _ _ h3 h4 h1 h2 _ _ _ _ _ _
  · exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint _ _ h4 h3 h2 h1 _ _ _ _ _ _

theorem commute_rLong_shortBlock [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    {i k : Fin (n - 1)} (hi : i.val + 1 < n - 1) (hik : i.val + 1 < k.val) (A : SL(2, F))
    (B : SL(2, ShortField b c)) : Commute (rLong n b c hi A) (shortBlock hirr n k B) := by
  refine commute_of_tv₂ (rLong n b c hi) (shortBlock hirr n k) (fun x y => ?_) A B
  simp only [rLong_tv01, rLong_tv10, shortBlock_tv01, shortBlock_tv10]
  have h1 : k ≠ i := Fin.ne_of_val_ne (by omega)
  have h2 : k ≠ ⟨i.val + 1, by omega⟩ := Fin.ne_of_val_ne (by dsimp only; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact commute_longRoot_twShortRoot_of_ne n hirr _ h1 h2 true false true _ _
  · exact commute_longRoot_twShortRoot_of_ne n hirr _ h1 h2 true false false _ _
  · exact commute_longRoot_twShortRoot_of_ne n hirr _ h2 h1 true false true _ _
  · exact commute_longRoot_twShortRoot_of_ne n hirr _ h2 h1 true false false _ _

omit hirr in
theorem wS_one_eq_weylSL2 : (wS (1 : Fˣ) : SL(2, F)) = weylSL2 1 := by
  apply Subtype.ext
  simp only [wS, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, weylSL2,
    Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

theorem rLong_center_mem_torus {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    rLong n b c hk (wS (1 : Fˣ) * wS (1 : Fˣ)) ∈ minusTorus n hirr k := by
  rw [minusTorus_of_lt n hirr hk, map_mul, wS_one_eq_weylSL2]
  have h : (minusFrame n b c).longWeyl (succ_ne_of_lt n hk) true false *
      (minusFrame n b c).longWeyl (succ_ne_of_lt n hk) true false =
        (minusFrame n b c).longTorus (succ_ne_of_lt n hk) true false (-1) :=
    HypFrame.longWeyl_mul_self _ _ _ _
  exact ⟨-1, h.symm⟩

theorem shortBlock_center_mem_torus [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) :
    shortBlock hirr n k (wS (1 : (ShortField b c)ˣ) * wS (1 : (ShortField b c)ˣ)) ∈
      minusTorus n hirr k := by
  have := finite_shortField (b := b) (c := c)
  rw [minusTorus_of_not_lt n hirr hk]
  have h1 : shortBlock hirr n k (wS (1 : (ShortField b c)ˣ)) = shortWeyl n hirr k := by
    rw [wS, map_mul, map_mul, shortBlock_upper, shortBlock_lower, ← shortRels_w_one n hirr k,
      RankOneRels.w_def]
    simp only [shortRels_x, shortRels_y, Units.val_one, inv_one]
  rw [map_mul, h1, ← pow_two]
  exact shortWeyl_sq_mem n hirr k

end Orthogonal

end CFSG.ClassicalInvolution.WeakCT
