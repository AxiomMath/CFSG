module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpO2Fixed
public import CFSG.RankThree.Classical.SteinbergBJSymplecticPrimarySelfDual

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary (blockGL blockApply unitaryCentralizer
  mem_unitaryCentralizer supportedUnitary supportedUnitary_le_unitaryCentralizer root_ne_zero
  finrank_adjoinRoot)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Invariant

theorem aeval_mem_of_invariant {f : Module.End K V} {W : Submodule K V}
    (hf : ∀ w ∈ W, f w ∈ W) (g : K[X]) : ∀ w ∈ W, aeval f g w ∈ W := by
  induction g using Polynomial.induction_on with
  | C c =>
    intro w hw
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact W.smul_mem c hw
  | add p q hp hq =>
    intro w hw
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp w hw) (hq w hw)
  | monomial n c hn =>
    intro w hw
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact hn _ (hf w hw)

variable {x : Module.End K V} {a : K[X]} [Fact (Irreducible a)]

@[expose] noncomputable def primarySubspace (W : Submodule K V) (hx : ∀ w ∈ W, x w ∈ W) :
    Submodule (AdjoinRoot a) (primaryComponent x a) where
  carrier := {v | (v : V) ∈ W}
  add_mem' hv hw := W.add_mem hv hw
  zero_mem' := W.zero_mem
  smul_mem' e v hv := by
    induction e using AdjoinRoot.induction_on with
    | ih g =>
      change ((AdjoinRoot.mk a g • v : primaryComponent x a) : V) ∈ W
      rw [coe_mk_smul_primaryComponent]
      exact aeval_mem_of_invariant hx g _ hv

theorem primarySubspace_ne_bot {W : Submodule K V} (hx : ∀ w ∈ W, x w ∈ W)
    (hWa : W ≤ primaryComponent x a) (hW : W ≠ ⊥) : primarySubspace (a := a) W hx ≠ ⊥ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro hbot
  have h1 : (⟨w, hWa hw⟩ : primaryComponent x a) ∈ primarySubspace (a := a) W hx := hw
  rw [hbot, Submodule.mem_bot] at h1
  exact hw0 (congrArg Subtype.val h1)

theorem primaryComponent_le_of_primarySubspace_eq_top {W : Submodule K V}
    {hx : ∀ w ∈ W, x w ∈ W} (htop : primarySubspace (a := a) W hx = ⊤) :
    primaryComponent x a ≤ W := fun v hv => by
  have h1 : (⟨v, hv⟩ : primaryComponent x a) ∈ primarySubspace (a := a) W hx := by
    rw [htop]
    exact Submodule.mem_top
  exact h1

end Invariant

section Root

variable [FiniteDimensional K V] {x : Module.End K V}

theorem root_ne_one_of_ne {a : K[X]} (ha : a ∈ primaryFactors x) (hne : a ≠ X - 1)
    [Fact (Irreducible a)] : AdjoinRoot.root a ≠ 1 := by
  intro h1
  have hdvd : a ∣ X - 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, AdjoinRoot.mk_X, map_one, h1, sub_self]
  refine hne (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (monic_of_mem_primaryFactors ha)
    (monic_X_sub_C 1) hdvd ?_).symm
  rw [natDegree_X_sub_C]
  exact (irreducible_of_mem_primaryFactors ha).natDegree_pos

theorem root_pow_eq_one {a : K[X]} (ha : a ∈ primaryFactors x) [Fact (Irreducible a)] {m : ℕ}
    (hxm : x ^ m = 1) : AdjoinRoot.root a ^ m = 1 := by
  have hmin : minpoly K x ∣ X ^ m - 1 :=
    minpoly.dvd K x (by rw [map_sub, map_pow, aeval_X, map_one, hxm, sub_self])
  have hdvd : a ∣ X ^ m - 1 := (mem_primaryFactors.mp ha).2.2.trans hmin
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at hdvd
  exact hdvd

theorem root_sq_ne_one {a : K[X]} (ha : a ∈ primaryFactors x) (hne : a ≠ X - 1)
    [Fact (Irreducible a)] {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    AdjoinRoot.root a ^ 2 ≠ 1 := by
  intro h2
  obtain ⟨k, rfl⟩ := hm
  have hm1 := root_pow_eq_one ha hxm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hm1
  exact root_ne_one_of_ne ha hne hm1

end Root

section Fixed

variable {B : LinearMap.BilinForm K V}

@[expose] noncomputable def altTransvection (hB : B.IsAlt) (v : V) :
    LinearMap.GeneralLinearGroup K V where
  val := LinearMap.id + (B v).smulRight v
  inv := LinearMap.id - (B v).smulRight v
  val_inv := LinearMap.ext fun u => by simp [hB v]
  inv_val := LinearMap.ext fun u => by simp [hB v]

theorem altTransvection_apply (hB : B.IsAlt) (v u : V) :
    ((altTransvection hB v : LinearMap.GeneralLinearGroup K V) : Module.End K V) u =
      u + B v u • v := rfl

variable [FiniteDimensional K V] {x : LinearMap.GeneralLinearGroup K V}

omit [FiniteDimensional K V] in
theorem altTransvection_mem_unitaryCentralizer (H : AltPrimaryData B x) {v : V}
    (hv : (x : Module.End K V) v = v) : altTransvection H.alt v ∈ unitaryCentralizer B x := by
  rw [mem_unitaryCentralizer]
  refine ⟨mem_sesqUnitaryGroup.mpr fun u w => ?_, ?_⟩
  · simp only [altTransvection_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, H.alt v, H.skew u v]
    ring
  · refine LinearMap.ext fun u => ?_
    simp only [Module.End.mul_apply, altTransvection_apply, map_add, map_smul, hv]
    congr 2
    have := H.isom_apply v u
    rwa [hv] at this

theorem primaryComponent_le_of_fixed (H : AltPrimaryData B x)
    (h1 : (X - 1 : K[X]) ∈ primaryFactors (x : Module.End K V)) {W : Submodule K V}
    (hWa : W ≤ primaryComponent (x : Module.End K V) (X - 1)) (hW : W ≠ ⊥)
    (hC : ∀ g ∈ unitaryCentralizer B x, ∀ w ∈ W, (g : Module.End K V) w ∈ W) :
    primaryComponent (x : Module.End K V) (X - 1) ≤ W := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hfix : ∀ v ∈ primaryComponent (x : Module.End K V) (X - 1),
      (x : Module.End K V) v = v := fun v hv => mem_primaryComponent_X_sub_one.mp hv
  have key : ∀ v ∈ primaryComponent (x : Module.End K V) (X - 1), B v w ≠ 0 → v ∈ W := by
    intro v hv hvw
    have h2 := W.sub_mem (hC _ (altTransvection_mem_unitaryCentralizer H (hfix v hv)) w hw) hw
    rw [altTransvection_apply, add_sub_cancel_left] at h2
    have h3 := W.smul_mem (B v w)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hvw, one_smul] at h3
  obtain ⟨v₀, hv₀, hv₀w⟩ : ∃ v₀ ∈ primaryComponent (x : Module.End K V) (X - 1), B v₀ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h2 := (H.nondegenerate_restrict_fixed h1).2 ⟨w, hWa hw⟩ fun v => hcon v v.2
    exact hw0 (congrArg Subtype.val h2)
  have hv₀W := key v₀ hv₀ hv₀w
  intro v hv
  by_cases hvw : B v w = 0
  · have h2 : v + v₀ ∈ W := key (v + v₀) (Submodule.add_mem _ hv hv₀) (by
      rw [LinearMap.map_add, LinearMap.add_apply, hvw, zero_add]
      exact hv₀w)
    have h3 := W.sub_mem h2 hv₀W
    rwa [add_sub_cancel_right] at h3
  · exact key v hv hvw

end Fixed

section Blocks

variable [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
  {x : LinearMap.GeneralLinearGroup K V}

theorem primaryComponent_le_of_paired (H : AltPrimaryData B x) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne1 : a ≠ X - 1)
    (hne : a ≠ reciprocalPolynomial a) {W : Submodule K V}
    (hWa : W ≤ primaryComponent (x : Module.End K V) a) (hW : W ≠ ⊥)
    (hx : ∀ w ∈ W, (x : Module.End K V) w ∈ W)
    (hC : ∀ g ∈ unitaryCentralizer B x, ∀ w ∈ W, (g : Module.End K V) w ∈ W) :
    primaryComponent (x : Module.End K V) a ≤ W := by
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  set W' := primarySubspace (a := a) W hx
  have hγ : ∀ γ : blockGL (x : Module.End K V) a, ∀ v ∈ W',
      (γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) v ∈ W' := by
    intro γ v hv
    set g := (H.pairedEquiv ha hne).symm γ
    have hg : (g : LinearMap.GeneralLinearGroup K V) ∈ unitaryCentralizer B x :=
      supportedUnitary_le_unitaryCentralizer _ g.2
    have h1 := H.blockApply_pairedEquiv ha hne g v v.2
    rw [MulEquiv.apply_symm_apply] at h1
    change (blockApply γ v v.2 : V) ∈ W
    rw [h1]
    exact hC _ hg v hv
  set b := Module.finBasis (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)
  have hr0 : AdjoinRoot.root a ≠ 0 := root_ne_zero (H.coeff_zero_ne ha)
  refine primaryComponent_le_of_primarySubspace_eq_top
    (eq_top_of_basisScale_basisSwap b (root_ne_one_of_ne ha hne1) W'
      (primarySubspace_ne_bot hx hWa hW) (fun i v hv => ?_) fun i j v hv => ?_)
  · exact hγ (basisScaleUnit b (Units.mk0 _ hr0) i) v hv
  · exact hγ (basisSwapUnit b i j) v hv

variable [Finite K]

theorem primaryComponent_le_of_selfDual (H : AltPrimaryData B x) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hne1 : a ≠ X - 1) (hself : reciprocalPolynomial a = a) {W : Submodule K V}
    (hWa : W ≤ primaryComponent (x : Module.End K V) a) (hW : W ≠ ⊥)
    (hx : ∀ w ∈ W, (x : Module.End K V) w ∈ W)
    (hC : ∀ g ∈ unitaryCentralizer B x, ∀ w ∈ W, (g : Module.End K V) w ∈ W) :
    primaryComponent (x : Module.End K V) a ≤ W := by
  classical
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have h0 := H.coeff_zero_ne ha
  have hxm' : (x : Module.End K V) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxm, Units.val_one]
  have hsq2 := root_sq_ne_one ha hne1 hm hxm'
  obtain ⟨d, hd, hσd⟩ := exists_rootInv_eq_pow h0 hself hsq2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  have hKc : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hd1 : 1 ≤ d := by
    have := (irreducible_of_mem_primaryFactors ha).natDegree_pos
    rw [finrank_adjoinRoot] at hd
    omega
  have hE : UnitaryFieldData p ((n : ℕ) * d) (AdjoinRoot a) := by
    refine ⟨hp, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero n.ne_zero (by omega)), ?_⟩
    rw [Module.natCard_eq_pow_finrank (K := K), hd, hKc, ← pow_mul]
    ring_nf
  have hbar : ∀ z, hE.bar z = rootInv h0 hself z := fun z => by
    rw [UnitaryFieldData.bar_apply, hσd, hKc, ← pow_mul]
  obtain ⟨η, hη0, hη⟩ := exists_ne_zero_neg (rootInv h0 hself) (rootInv_rootInv h0 hself)
    (rootInv_ne_one h0 hself hsq2)
  have hηbar : hE.bar η = -η := by rw [hbar, hη]
  have hsymm := H.altHermForm_isSymm ha hself hE.bar hbar hηbar
  have hsep := H.altHermForm_separatingLeft ha hself hE.bar hbar hη0
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hsymm hsep
  set W' := primarySubspace (a := a) W hx
  have hγ : ∀ γ ∈ sesqUnitaryGroup (H.altHermForm ha hself hE.bar hbar η), ∀ v ∈ W',
      (γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) v ∈ W' := by
    intro γ hγu v hv
    set g := (H.selfDualEquiv ha hself hE.bar hbar hη0).symm ⟨γ, hγu⟩
    have hg : (g : LinearMap.GeneralLinearGroup K V) ∈ unitaryCentralizer B x :=
      supportedUnitary_le_unitaryCentralizer _ g.2
    have h1 := H.blockApply_selfDualEquiv ha hself hE.bar hbar hη0 g v v.2
    rw [MulEquiv.apply_symm_apply] at h1
    change (blockApply γ v v.2 : V) ∈ W
    rw [h1]
    exact hC _ hg v hv
  have hr0 : AdjoinRoot.root a ≠ 0 := root_ne_zero h0
  have hc : hE.bar (AdjoinRoot.root a) * AdjoinRoot.root a = 1 := by
    rw [hbar, rootInv_root, inv_mul_cancel₀ hr0]
  refine primaryComponent_le_of_primarySubspace_eq_top
    (eq_top_of_basisScale_basisSwap e (root_ne_one_of_ne ha hne1) W'
      (primarySubspace_ne_bot hx hWa hW) (fun i v hv => ?_) fun i j v hv => ?_)
  · refine hγ (basisScaleUnit e (Units.mk0 _ hr0) i)
      (mem_sesqUnitaryGroup.mpr fun u w => ?_) v hv
    exact sesq_basisScale e he hc i u w
  · refine hγ (basisSwapUnit e i j) (mem_sesqUnitaryGroup.mpr fun u w => ?_) v hv
    exact sesq_basisSwap e he i j u w

theorem primaryComponent_le_of_invariant (H : AltPrimaryData B x) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    {W : Submodule K V} (hWa : W ≤ primaryComponent (x : Module.End K V) a) (hW : W ≠ ⊥)
    (hx : ∀ w ∈ W, (x : Module.End K V) w ∈ W)
    (hC : ∀ g ∈ unitaryCentralizer B x, ∀ w ∈ W, (g : Module.End K V) w ∈ W) :
    primaryComponent (x : Module.End K V) a ≤ W := by
  by_cases ha1 : a = X - 1
  · subst ha1
    exact primaryComponent_le_of_fixed H ha hWa hW hC
  · by_cases hself : reciprocalPolynomial a = a
    · exact primaryComponent_le_of_selfDual H hm hxm ha ha1 hself hWa hW hx hC
    · exact primaryComponent_le_of_paired H ha ha1 (fun h => hself h.symm) hWa hW hx hC

end Blocks

end CFSG.ComponentClassification.RankTwoClassical
