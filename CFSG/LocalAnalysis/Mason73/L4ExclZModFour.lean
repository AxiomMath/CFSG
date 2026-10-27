module

public import CFSG.LocalAnalysis.Mason73.L4ExclClassicalE32
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.Open CFSG.RankThree.PartOne.SLB4A
  CFSG.ClassicalGroups.SpecialLinear
open scoped Matrix

theorem pow_mod_eq_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {k : ℕ} (hx : x ^ k = 1)
    (m : ℕ) : x ^ (m % k) = x ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m k, pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] def zmodFourPow {M : Type*} [Monoid M] (ι : M) (hι : ι ^ 4 = 1) :
    Multiplicative (ZMod 4) →* M where
  toFun a := ι ^ (Multiplicative.toAdd a).val
  map_one' := by
    rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, pow_mod_eq_of_pow_eq_one hι, pow_add]

theorem zmodFourPow_apply {M : Type*} [Monoid M] (ι : M) (hι : ι ^ 4 = 1)
    (a : Multiplicative (ZMod 4)) : zmodFourPow ι hι a = ι ^ (Multiplicative.toAdd a).val :=
  rfl

theorem pow_four_eq_one_of_mul_self {K : Type} [Field K] {ι : Kˣ} (hι : (ι : K) * ι = -1) :
    ι ^ 4 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  linear_combination ((ι : K) * ι - 1) * hι

theorem zmodFourPow_injective {K : Type} [Field K] {ι : Kˣ} (hι : (ι : K) * ι = -1)
    (hneg : (-1 : K) ≠ 1) :
    Function.Injective (zmodFourPow ι (pow_four_eq_one_of_mul_self hι)) := by
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  rw [zmodFourPow_apply] at ha
  have hval := congrArg Units.val ha
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hval
  have hlt : (Multiplicative.toAdd a).val < 4 := ZMod.val_lt _
  suffices h0 : (Multiplicative.toAdd a).val = 0 by
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact (ZMod.val_eq_zero _).1 h0
  interval_cases h : (Multiplicative.toAdd a).val
  · rfl
  · exact absurd (by linear_combination -hι + ((ι : K) + 1) * hval : (-1 : K) = 1) hneg
  · exact absurd (by linear_combination -hι + hval : (-1 : K) = 1) hneg
  · exact absurd (by linear_combination (-((ι : K) - 1)) * hval +
      ((ι : K) * ((ι : K) - 1) - 1) * hι : (-1 : K) = 1) hneg

variable {K : Type} [Field K]

@[expose] noncomputable def diagFiveVec (χ : Multiplicative (ZMod 4) →* Kˣ) :
    Multiplicative (Fin 4 → ZMod 4) →* (Fin 5 → Kˣ) where
  toFun a := ![χ (Multiplicative.ofAdd (Multiplicative.toAdd a 0)),
    χ (Multiplicative.ofAdd (Multiplicative.toAdd a 1)),
    χ (Multiplicative.ofAdd (Multiplicative.toAdd a 2)),
    χ (Multiplicative.ofAdd (Multiplicative.toAdd a 3)),
    (χ (Multiplicative.ofAdd (∑ i, Multiplicative.toAdd a i)))⁻¹]
  map_one' := by
    funext j
    fin_cases j <;> simp
  map_mul' a b := by
    funext j
    fin_cases j <;>
      simp [Finset.sum_add_distrib, ofAdd_add, map_mul, mul_inv, mul_comm]

theorem diagFiveVec_apply (χ : Multiplicative (ZMod 4) →* Kˣ)
    (a : Multiplicative (Fin 4 → ZMod 4)) :
    diagFiveVec χ a = ![χ (Multiplicative.ofAdd (Multiplicative.toAdd a 0)),
      χ (Multiplicative.ofAdd (Multiplicative.toAdd a 1)),
      χ (Multiplicative.ofAdd (Multiplicative.toAdd a 2)),
      χ (Multiplicative.ofAdd (Multiplicative.toAdd a 3)),
      (χ (Multiplicative.ofAdd (∑ i, Multiplicative.toAdd a i)))⁻¹] :=
  rfl

theorem prod_diagFiveVec (χ : Multiplicative (ZMod 4) →* Kˣ)
    (a : Multiplicative (Fin 4 → ZMod 4)) : ∏ j, diagFiveVec χ a j = 1 := by
  rw [Fin.prod_univ_five, diagFiveVec_apply, Fin.sum_univ_four]
  simp only [Matrix.cons_val]
  rw [ofAdd_add, ofAdd_add, ofAdd_add, map_mul, map_mul, map_mul, mul_inv_cancel]

theorem diagFiveVec_mem (χ : Multiplicative (ZMod 4) →* Kˣ) {N : Subgroup Kˣ}
    (hN : ∀ x, χ x ∈ N) (a : Multiplicative (Fin 4 → ZMod 4)) (j : Fin 5) :
    diagFiveVec χ a j ∈ N := by
  rw [diagFiveVec_apply]
  fin_cases j
  · exact hN _
  · exact hN _
  · exact hN _
  · exact hN _
  · exact N.inv_mem (hN _)

theorem zmod_four_eq_zero_of_five : ∀ x : ZMod 4, x + x + x + x + x = 0 → x = 0 := by
  decide

theorem eq_one_of_diagGLHom_diagFiveVec_mem_statedScalars {χ : Multiplicative (ZMod 4) →* Kˣ}
    (hχ : Function.Injective χ) {a : Multiplicative (Fin 4 → ZMod 4)}
    (ha : diagGLHom 5 K (diagFiveVec χ a) ∈ StatedScalars (Fin 5) K) : a = 1 := by
  obtain ⟨c, hc⟩ := ha
  have hentry : ∀ j, diagFiveVec χ a j = c := by
    intro j
    apply Units.ext
    have := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) j j) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_diagGLHom, Matrix.diagonal_apply_eq,
      Matrix.scalar_apply] at this
    exact this.symm
  have hχ' : ∀ y z : ZMod 4, χ (Multiplicative.ofAdd y) = χ (Multiplicative.ofAdd z) → y = z :=
    fun y z h => Multiplicative.ofAdd.injective (hχ h)
  have e0 := hentry 0
  have e1 := hentry 1
  have e2 := hentry 2
  have e3 := hentry 3
  have e4 := hentry 4
  rw [diagFiveVec_apply] at e0 e1 e2 e3 e4
  simp only [Matrix.cons_val] at e0 e1 e2 e3 e4
  have h10 : Multiplicative.toAdd a 1 = Multiplicative.toAdd a 0 := hχ' _ _ (e1.trans e0.symm)
  have h20 : Multiplicative.toAdd a 2 = Multiplicative.toAdd a 0 := hχ' _ _ (e2.trans e0.symm)
  have h30 : Multiplicative.toAdd a 3 = Multiplicative.toAdd a 0 := hχ' _ _ (e3.trans e0.symm)
  have hsum : (∑ i, Multiplicative.toAdd a i) + Multiplicative.toAdd a 0 = 0 := by
    apply hχ'
    rw [ofAdd_add, map_mul, e0, ofAdd_zero, map_one, ← e4, mul_inv_cancel]
  rw [Fin.sum_univ_four, h10, h20, h30] at hsum
  have hx0 : Multiplicative.toAdd a 0 = 0 := zmod_four_eq_zero_of_five _ hsum
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_one, Pi.zero_apply]
  fin_cases i
  · exact hx0
  · exact h10.trans hx0
  · exact h20.trans hx0
  · exact h30.trans hx0

theorem injective_mk_comp_codRestrict {ι : Type} [Fintype ι] [DecidableEq ι] {M : Type*}
    [Group M] (H : Subgroup (GL ι K)) (ψ : M →* GL ι K) (hψ : ∀ m, ψ m ∈ H)
    (hinj : ∀ m, ψ m ∈ StatedScalars ι K → m = 1) :
    Function.Injective
      ((QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)).comp (ψ.codRestrict H hψ)) := by
  refine (injective_iff_map_eq_one _).2 fun m hm => hinj m ?_
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hm
  exact hm

variable {G : Type} [Group G] [Finite G] {n p f : ℕ}

theorem false_of_lieModel_psl_five_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSL 5 p f) (hq : p ^ f % 4 = 1) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hneg := neg_one_ne_one_of_card_odd K (natCard_mod_two_of_eq_pow hp hp2 hK)
  obtain ⟨u, hu⟩ := exists_sq_neg_one K (by rw [hK]; exact hq)
  set χ := zmodFourPow u (pow_four_eq_one_of_mul_self hu)
  set ψ := (diagGLHom 5 K).comp (diagFiveVec χ)
  have hψ : ∀ a, ψ a ∈ StatedSL 5 K := fun a => by
    refine Subgroup.subset_closure ?_
    show ((ψ a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1
    rw [MonoidHom.comp_apply, det_diagGLHom, prod_diagFiveVec, Units.val_one]
  exact false_of_injective_zmod_four_of_l4Sylow_of_mulEquiv hn P hP e _
    (injective_mk_comp_codRestrict _ ψ hψ fun a ha =>
      eq_one_of_diagGLHom_diagFiveVec_mem_statedScalars (zmodFourPow_injective hu hneg) ha)

theorem false_of_lieModel_psu_five_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSU 5 p f) (hq : p ^ f % 4 = 3) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hodd : Nat.card K % 2 = 1 := by
    rw [hK]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow.pow)
  have hneg := neg_one_ne_one_of_card_odd K hodd
  obtain ⟨u, hu, huq⟩ := exists_unit_sq_neg_one_of_mod_four_three hK hq
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
  set χ := zmodFourPow u (pow_four_eq_one_of_mul_self hu)
  set ψ := (diagGLHom 5 K).comp (diagFiveVec χ)
  set N : Subgroup Kˣ := (powMonoidHom (p ^ f + 1) : Kˣ →* Kˣ).ker
  have huN : u ∈ N := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    exact huq
  have hχN : ∀ x, χ x ∈ N := fun x => by
    rw [zmodFourPow_apply]
    exact pow_mem huN _
  have hψ : ∀ a, ψ a ∈ StatedSU 5 (p ^ f) K := fun a => by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [MonoidHom.comp_apply, det_diagGLHom, prod_diagFiveVec, Units.val_one]
    · show (((ψ a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map (· ^ (p ^ f)))ᵀ *
        ((ψ a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1
      rw [MonoidHom.comp_apply, coe_diagGLHom, Matrix.diagonal_map (by simp [zero_pow hq0]),
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext j
      have h1 := diagFiveVec_mem χ hχN a j
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at h1
      have h2 := congrArg Units.val h1
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h2
      exact h2
  exact false_of_injective_zmod_four_of_l4Sylow_of_mulEquiv hn P hP e _
    (injective_mk_comp_codRestrict _ ψ hψ fun a ha =>
      eq_one_of_diagGLHom_diagFiveVec_mem_statedScalars (zmodFourPow_injective hu hneg) ha)

end CFSG.LocalAnalysis.Mason73
