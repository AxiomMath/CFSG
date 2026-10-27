module

public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeD

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

namespace TightDatum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  (d : TightDatum R S t)

@[expose] def FixesFitting (x : Subgroup.centralizer ({t} : Set G)) : Prop :=
  ∀ p ∈ genFittingFitting d.Dbar, d.dbarAct x p * p⁻¹ ∈ Subgroup.zpowers d.tbar

@[expose] def InnerOnLayer (x : Subgroup.centralizer ({t} : Set G)) : Prop :=
  ∃ e ∈ genFittingLayer d.Dbar, ∀ y ∈ genFittingLayer d.Dbar, d.dbarAct x y = e * y * e⁻¹

@[expose] def Good (x : Subgroup.centralizer ({t} : Set G)) : Prop :=
  d.FixesFitting x ∧ d.InnerOnLayer x

theorem dbarAct_fixes_fitting {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) (hF : d.FixesFitting x) :
    ∀ p ∈ genFittingFitting d.Dbar, d.dbarAct x p = p := by
  intro p hp
  set δ := d.dbarAct x with hδ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hF p hp)
  set u := δ p * p⁻¹ with hu
  have hδt : δ d.tbar = d.tbar := d.dbarAct_tbar x
  have hδu : δ u = u := by rw [← hm, map_zpow, hδt]
  have hδun : ∀ n : ℕ, (δ ^ n) u = u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hδu, ih]
  have hp' : δ p = u * p := by rw [hu]; group
  have hform : ∀ n : ℕ, (δ ^ n) p = u ^ n * p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, hp', map_mul, hδun n, ih, pow_succ']
      group
  have hk : δ ^ 3 ^ k = 1 := by rw [hδ, ← map_pow, hx, map_one]
  have h1 : u ^ 3 ^ k = 1 := by
    have := hform (3 ^ k)
    rw [hk, MulAut.one_apply] at this
    exact mul_right_cancel (b := p) (by rw [one_mul]; exact this.symm)
  have hu2 : u ^ 2 = 1 := by
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : d.tbar ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact d.tbar_pow_two
    rw [this, one_zpow]
  obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  rw [hj, pow_succ, pow_mul, hu2, one_pow, one_mul] at h1
  rw [hp', h1, one_mul]

theorem innerAt_of_good {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ} (hx : x ^ 3 ^ k = 1)
    (hg : d.Good x) :
    ∃ dd ∈ d.act.ker, ∀ y ∈ d.act.ker, x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈
      oddCore (Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨hF, e, he, hE⟩ := hg
  obtain ⟨g, hgg⟩ := exists_inner_of_fixes_fitting_inner_layer d.oddCore_dbar_eq_bot
    (d.dbarAct x) (k := k) (by rw [← map_pow, hx, map_one]) (d.dbarAct_fixes_fitting hx hF) he hE
  exact (d.innerAt_iff_dbar_inner x).mpr ⟨g, hgg⟩

theorem exists_centModO_of_good {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) (hx1 : d.act x ≠ 1) (hg : d.Good x) :
    ∃ (x' : Subgroup.centralizer ({t} : Set G)) (k' : ℕ), x' ^ 3 ^ k' = 1 ∧ d.act x' ≠ 1 ∧
      x' ∈ centModO d.act (oddCore (Subgroup.centralizer ({t} : Set G))) := by
  obtain ⟨e⟩ := d.nonempty_equiv_q8 hx hx1
  exact exists_centModO_of_inner d.act _ (d.act_pow_three_eq_one e hx) hx1
    (d.innerAt_of_good hx hg)

theorem diagFree_of_good {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ} (hx : x ^ 3 ^ k = 1)
    (hx1 : d.act x ≠ 1) (hg : d.Good x) : d.DiagFree := by
  rw [d.diagFree_iff_c]
  intro _ _ _ _
  exact d.exists_centModO_of_good hx hx1 hg

theorem dbarAct_eq_one_of_mem_centModO {x : Subgroup.centralizer ({t} : Set G)}
    (hW : x ∈ centModO d.act (oddCore (Subgroup.centralizer ({t} : Set G)))) :
    d.dbarAct x = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [d.dbarAct_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem, d.mem_oddKer_iff]
    have h2 : ((MulAut.conjNormal (H := d.act.ker) x y / y : ↥d.act.ker) :
        Subgroup.centralizer ({t} : Set G)) = ⁅x, (y : Subgroup.centralizer ({t} : Set G))⁆ := by
      rw [Subgroup.coe_div, MulAut.conjNormal_apply, commutatorElement_def, div_eq_mul_inv]
    rw [h2]
    exact mem_centModO.mp hW y y.2

theorem good_of_mem_centModO {x : Subgroup.centralizer ({t} : Set G)}
    (hW : x ∈ centModO d.act (oddCore (Subgroup.centralizer ({t} : Set G)))) : d.Good x := by
  have h1 := d.dbarAct_eq_one_of_mem_centModO hW
  refine ⟨fun p _ => ?_, 1, Subgroup.one_mem _, fun y _ => ?_⟩
  · rw [h1, MulAut.one_apply, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h1, MulAut.one_apply]
    group

theorem diagFree_iff_good : d.DiagFree ↔
    ((∃ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ), x ^ 3 ^ k = 1 ∧ d.act x ≠ 1) →
      ∃ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ), x ^ 3 ^ k = 1 ∧ d.act x ≠ 1 ∧
        d.Good x) := by
  constructor
  · intro h hex
    obtain ⟨x, k, hx, hx1⟩ := hex
    obtain ⟨x', k', hx', hx'1, hW⟩ := (d.diagFree_iff_c.mp h) x k hx hx1
    exact ⟨x', k', hx', hx'1, d.good_of_mem_centModO hW⟩
  · intro h
    rw [d.diagFree_iff_c]
    intro x k hx hx1
    obtain ⟨x₁, k₁, hx₁, hx₁1, hg⟩ := h ⟨x, k, hx, hx1⟩
    exact d.exists_centModO_of_good hx₁ hx₁1 hg

theorem not_good_dichotomy (hnot : ¬ d.DiagFree) {x : Subgroup.centralizer ({t} : Set G)} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) (hx1 : d.act x ≠ 1) :
    (∃ p ∈ genFittingFitting d.Dbar, d.dbarAct x p * p⁻¹ ∉ Subgroup.zpowers d.tbar) ∨
      ¬ d.InnerOnLayer x := by
  by_contra hcon
  push Not at hcon
  exact hnot (d.diagFree_of_good hx hx1 ⟨hcon.1, hcon.2⟩)

theorem fixesFitting_of_fitting_le (h : genFittingFitting d.Dbar ≤ Subgroup.zpowers d.tbar)
    (x : Subgroup.centralizer ({t} : Set G)) : d.FixesFitting x := by
  intro p hp
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (h hp)
  have : d.dbarAct x p = p := by rw [← hm, map_zpow, d.dbarAct_tbar]
  rw [this, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem innerOnLayer_of_layer_eq_bot (h : genFittingLayer d.Dbar = ⊥)
    (x : Subgroup.centralizer ({t} : Set G)) : d.InnerOnLayer x := by
  refine ⟨1, Subgroup.one_mem _, fun y hy => ?_⟩
  rw [h, Subgroup.mem_bot] at hy
  subst hy
  simp

end TightDatum

@[expose] def TightGoodElement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R)
      (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))))
      (t : G) (ht : t ∈ (S : Subgroup R).map R.subtype) (hto : orderOf t = 2)
      (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
      (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
      (h2 : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)),
    (∃ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ), x ^ 3 ^ k = 1 ∧
        (⟨hS, ht, hto, hRC, hRn, h2⟩ : TightDatum R S t).act x ≠ 1) →
    ∃ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ), x ^ 3 ^ k = 1 ∧
      (⟨hS, ht, hto, hRC, hRn, h2⟩ : TightDatum R S t).act x ≠ 1 ∧
      (⟨hS, ht, hto, hRC, hRn, h2⟩ : TightDatum R S t).Good x

theorem tightDiagonalFree_iff_tightGoodElement : TightDiagonalFree ↔ TightGoodElement := by
  constructor
  · intro h G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
    have hd : TightDatum R S t := ⟨hS, ht, hto, hRC, hRn, h2⟩
    exact hd.diagFree_iff_good.mp (h G hnab hlarge R S hS t ht hto hRC hRn h2)
  · intro h G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
    have hd : TightDatum R S t := ⟨hS, ht, hto, hRC, hRn, h2⟩
    exact hd.diagFree_iff_good.mpr (h G hnab hlarge R S hS t ht hto hRC hRn h2)

end CFSG.ClassicalInvolution.Q3
