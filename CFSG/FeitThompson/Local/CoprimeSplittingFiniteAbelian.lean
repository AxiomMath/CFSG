module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import CFSG.FeitThompson.Foundations.DivisionCoprimeToAbelianOrder
public import Mathlib.Data.Nat.Prime.Defs

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset

section Ring

variable {R : Type*} [Ring R] {x : R} {n : ℕ}

theorem self_mul_geom_sum (hx : x ^ n = 1) :
    x * ∑ i ∈ range n, x ^ i = ∑ i ∈ range n, x ^ i := by
  have h1 : (∑ i ∈ range (n + 1), x ^ i) = (∑ i ∈ range n, x ^ (i + 1)) + x ^ 0 :=
    Finset.sum_range_succ' _ _
  have h2 : (∑ i ∈ range (n + 1), x ^ i) = (∑ i ∈ range n, x ^ i) + x ^ n :=
    Finset.sum_range_succ _ _
  have h3 : x * ∑ i ∈ range n, x ^ i = ∑ i ∈ range n, x ^ (i + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (pow_succ' x i).symm
  rw [h3]
  have h4 := h1.symm.trans h2
  rw [hx, pow_zero] at h4
  exact add_right_cancel h4

theorem pow_mul_geom_sum (hx : x ^ n = 1) (m : ℕ) :
    x ^ m * ∑ i ∈ range n, x ^ i = ∑ i ∈ range n, x ^ i := by
  induction m with
  | zero => rw [pow_zero, one_mul]
  | succ m ih => rw [pow_succ', mul_assoc, ih, self_mul_geom_sum hx]

theorem geom_sum_mul_geom_sum (hx : x ^ n = 1) :
    (∑ i ∈ range n, x ^ i) * (∑ i ∈ range n, x ^ i) = (n : R) * ∑ i ∈ range n, x ^ i := by
  rw [Finset.sum_mul, Finset.sum_congr rfl fun i (_ : i ∈ range n) => pow_mul_geom_sum hx i,
    Finset.sum_const, card_range, nsmul_eq_mul]

theorem sub_one_mul_sum_geom_sum (x : R) (n : ℕ) :
    (x - 1) * ∑ i ∈ range n, ∑ j ∈ range i, x ^ j = (∑ i ∈ range n, x ^ i) - (n : R) := by
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i (_ : i ∈ range n) => mul_geom_sum x i,
    Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]

end Ring

variable {A : Type*} [AddCommGroup A] {p : ℕ} {s f : AddMonoid.End A} {a : A}

private theorem end_congr_apply {g h : AddMonoid.End A} (e : g = h) (a : A) : g a = h a :=
  congrArg (fun k : AddMonoid.End A => k a) e

private theorem sum_end_apply (g : ℕ → AddMonoid.End A) (t : Finset ℕ) (a : A) :
    (∑ i ∈ t, g i) a = ∑ i ∈ t, (g i) a := by
  induction t using Finset.induction with
  | empty => rfl
  | insert x t hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]; rfl

theorem mem_ker_sub_one_iff : a ∈ (s - 1 : AddMonoid.End A).ker ↔ s a = a :=
  AddMonoidHom.mem_ker.trans sub_eq_zero

theorem mem_range_sub_one_iff : a ∈ (s - 1 : AddMonoid.End A).range ↔ ∃ b, s b - b = a :=
  AddMonoidHom.mem_range

theorem sub_mem_range_sub_one (s : AddMonoid.End A) (a : A) :
    s a - a ∈ (s - 1 : AddMonoid.End A).range :=
  mem_range_sub_one_iff.2 ⟨a, rfl⟩

theorem range_sub_one_eq_closure (s : AddMonoid.End A) :
    (s - 1 : AddMonoid.End A).range = AddSubgroup.closure {x | ∃ a : A, s a - a = x} := by
  refine le_antisymm ?_ ((AddSubgroup.closure_le _).2 ?_)
  · intro x hx
    exact AddSubgroup.subset_closure (mem_range_sub_one_iff.1 hx)
  · rintro x ⟨a, rfl⟩
    exact sub_mem_range_sub_one s a

theorem apply_mem_range_sub_one (hf : Commute s f) (ha : a ∈ (s - 1 : AddMonoid.End A).range) :
    f a ∈ (s - 1 : AddMonoid.End A).range := by
  obtain ⟨b, rfl⟩ := mem_range_sub_one_iff.1 ha
  have h : f (s b - b) = s (f b) - f b := by
    rw [map_sub]
    congr 1
    exact end_congr_apply hf.symm.eq b
  rw [h]
  exact sub_mem_range_sub_one s (f b)

theorem isUnit_of_pow_eq_one_of_coprime (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    IsUnit s := by
  rcases eq_or_ne p 0 with rfl | hp0
  · have h1 : Nat.card A = 1 := (Nat.coprime_zero_left _).1 hp
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 h1).1
    have hs1 : s = 1 := AddMonoidHom.ext fun _ => Subsingleton.elim _ _
    exact hs1 ▸ isUnit_one
  · exact IsUnit.of_pow_eq_one hs hp0

theorem map_range_sub_one (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    ((s - 1 : AddMonoid.End A).range).map (s : A →+ A) = (s - 1 : AddMonoid.End A).range := by
  obtain ⟨u, rfl⟩ := isUnit_of_pow_eq_one_of_coprime hp hs
  refine le_antisymm ?_ fun x hx => ?_
  · rintro y ⟨z, hz, rfl⟩
    exact apply_mem_range_sub_one (Commute.refl _) hz
  · exact ⟨(↑u⁻¹ : AddMonoid.End A) x,
      apply_mem_range_sub_one (Commute.refl (u : AddMonoid.End A)).units_inv_right hx,
      end_congr_apply u.mul_inv x⟩

private theorem isCompl_range_ker_of_idem {g : A →+ A} (hg : ∀ a, g (g a) = g a) :
    IsCompl g.range g.ker := by
  constructor
  · rw [AddSubgroup.disjoint_def]
    intro x hx hx'
    obtain ⟨b, rfl⟩ := AddMonoidHom.mem_range.1 hx
    rw [← hg b, AddMonoidHom.mem_ker.1 hx']
  · rw [codisjoint_iff, AddSubgroup.eq_top_iff']
    intro a
    rw [AddSubgroup.mem_sup]
    refine ⟨g a, ⟨a, rfl⟩, a - g a, ?_, by abel⟩
    rw [AddMonoidHom.mem_ker, map_sub, hg, sub_self]

private noncomputable def invNsmulEnd (hp : p.Coprime (Nat.card A)) : AddMonoid.End A :=
  ((nsmulCoprimeAddAut hp).symm : A →+ A)

private theorem invNsmulEnd_mul_natCast (hp : p.Coprime (Nat.card A)) :
    invNsmulEnd hp * (p : AddMonoid.End A) = 1 := by
  ext a
  change invNsmulEnd hp ((p : AddMonoid.End A) a) = a
  rw [AddMonoid.End.natCast_apply]
  exact nsmulCoprimeAddAut_symm_nsmul hp a

private theorem invNsmulEnd_nsmul (hp : p.Coprime (Nat.card A)) (a : A) :
    invNsmulEnd hp (p • a) = a :=
  nsmulCoprimeAddAut_symm_nsmul hp a

private theorem commute_invNsmulEnd (hp : p.Coprime (Nat.card A)) (f : AddMonoid.End A) :
    Commute (invNsmulEnd hp) f :=
  AddMonoidHom.ext fun a => nsmulCoprimeAddAut_symm_comm hp f a

private noncomputable def averagingProj (hp : p.Coprime (Nat.card A)) (s : AddMonoid.End A) :
    AddMonoid.End A :=
  invNsmulEnd hp * ∑ i ∈ range p, s ^ i

private theorem averagingProj_apply (hp : p.Coprime (Nat.card A)) (s : AddMonoid.End A) (a : A) :
    averagingProj hp s a = invNsmulEnd hp (∑ i ∈ range p, (s ^ i) a) := by
  change invNsmulEnd hp ((∑ i ∈ range p, s ^ i) a) = _
  rw [sum_end_apply]

private theorem averagingProj_mul_self (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    averagingProj hp s * averagingProj hp s = averagingProj hp s := by
  have hqT := (commute_invNsmulEnd hp (∑ i ∈ range p, s ^ i)).symm
  change invNsmulEnd hp * _ * (invNsmulEnd hp * _) = invNsmulEnd hp * _
  simp only [mul_assoc]
  rw [← mul_assoc (∑ i ∈ range p, s ^ i) (invNsmulEnd hp) _, hqT]
  simp only [mul_assoc]
  rw [geom_sum_mul_geom_sum hs, ← mul_assoc (invNsmulEnd hp) ((p : AddMonoid.End A)) _,
    invNsmulEnd_mul_natCast hp, one_mul]

private theorem sub_one_mul_averagingProj (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    (s - 1) * averagingProj hp s = 0 := by
  rw [averagingProj, ← mul_assoc, (commute_invNsmulEnd hp (s - 1)).symm.eq, mul_assoc,
    mul_geom_sum, hs, sub_self, mul_zero]

private theorem averagingProj_mul_sub_one (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    averagingProj hp s * (s - 1) = 0 := by
  rw [averagingProj, mul_assoc, geom_sum_mul, hs, sub_self, mul_zero]

private noncomputable def averagingCorr (hp : p.Coprime (Nat.card A)) (s : AddMonoid.End A) :
    AddMonoid.End A :=
  -(invNsmulEnd hp * ∑ i ∈ range p, ∑ j ∈ range i, s ^ j)

private theorem one_sub_averagingProj (hp : p.Coprime (Nat.card A)) (s : AddMonoid.End A) :
    1 - averagingProj hp s = (s - 1) * averagingCorr hp s := by
  have h : (s - 1) * (invNsmulEnd hp * ∑ i ∈ range p, ∑ j ∈ range i, s ^ j)
      = invNsmulEnd hp * ((∑ i ∈ range p, s ^ i) - (p : AddMonoid.End A)) := by
    rw [← mul_assoc, (commute_invNsmulEnd hp (s - 1)).symm.eq, mul_assoc,
      sub_one_mul_sum_geom_sum]
  rw [averagingCorr, mul_neg, h, mul_sub, invNsmulEnd_mul_natCast hp, averagingProj]
  abel

private theorem range_averagingProj (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    (averagingProj hp s : AddMonoid.End A).range = (s - 1 : AddMonoid.End A).ker := by
  refine le_antisymm ?_ fun a ha => ?_
  · rintro x ⟨b, rfl⟩
    exact mem_ker_sub_one_iff.2
      (sub_eq_zero.1 (end_congr_apply (sub_one_mul_averagingProj hp hs) b))
  · have hfix := mem_ker_sub_one_iff.1 ha
    have hpow : ∀ i, (s ^ i) a = a := by
      intro i
      induction i with
      | zero => rfl
      | succ n ih => rw [pow_succ']; exact (congrArg s ih).trans hfix
    refine ⟨a, ?_⟩
    change averagingProj hp s a = a
    rw [averagingProj_apply, Finset.sum_congr rfl fun i _ => hpow i, Finset.sum_const,
      card_range, invNsmulEnd_nsmul]

private theorem ker_averagingProj (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    (averagingProj hp s : AddMonoid.End A).ker = (s - 1 : AddMonoid.End A).range := by
  refine le_antisymm (fun a ha => ?_) fun a ha => ?_
  · have h0 : averagingProj hp s a = 0 := AddMonoidHom.mem_ker.1 ha
    have h2 : a - averagingProj hp s a = (s - 1) (averagingCorr hp s a) :=
      end_congr_apply (one_sub_averagingProj hp s) a
    rw [h0, sub_zero] at h2
    exact h2 ▸ AddMonoidHom.mem_range.2 ⟨_, rfl⟩
  · obtain ⟨b, rfl⟩ := AddMonoidHom.mem_range.1 ha
    exact AddMonoidHom.mem_ker.2 (end_congr_apply (averagingProj_mul_sub_one hp hs) b)

theorem isCompl_ker_range_sub_one (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    IsCompl (s - 1 : AddMonoid.End A).ker (s - 1 : AddMonoid.End A).range := by
  have hidem : ∀ a : A, averagingProj hp s (averagingProj hp s a) = averagingProj hp s a :=
    fun a => end_congr_apply (averagingProj_mul_self hp hs) a
  have h := isCompl_range_ker_of_idem hidem
  rwa [range_averagingProj hp hs, ker_averagingProj hp hs] at h

theorem sup_ker_range_sub_one_eq_top (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    (s - 1 : AddMonoid.End A).ker ⊔ (s - 1 : AddMonoid.End A).range = ⊤ :=
  (isCompl_ker_range_sub_one hp hs).sup_eq_top

theorem inf_ker_range_sub_one_eq_bot (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    (s - 1 : AddMonoid.End A).ker ⊓ (s - 1 : AddMonoid.End A).range = ⊥ :=
  (isCompl_ker_range_sub_one hp hs).inf_eq_bot

theorem exists_add_eq_of_pow_eq_one (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) (a : A) :
    ∃ c ∈ (s - 1 : AddMonoid.End A).ker, ∃ b ∈ (s - 1 : AddMonoid.End A).range, c + b = a := by
  have h : a ∈ (s - 1 : AddMonoid.End A).ker ⊔ (s - 1 : AddMonoid.End A).range := by
    rw [sup_ker_range_sub_one_eq_top hp hs]; trivial
  exact AddSubgroup.mem_sup.1 h

def subOneRestrict (s : AddMonoid.End A) :
    (s - 1 : AddMonoid.End A).range →+ (s - 1 : AddMonoid.End A).range :=
  AddMonoidHom.codRestrict
    (((s - 1 : AddMonoid.End A) : A →+ A).comp (s - 1 : AddMonoid.End A).range.subtype) _
    fun x => AddMonoidHom.mem_range.2 ⟨(x : A), rfl⟩

@[simp]
theorem coe_subOneRestrict_apply (s : AddMonoid.End A) (x : (s - 1 : AddMonoid.End A).range) :
    (subOneRestrict s x : A) = s (x : A) - (x : A) := (rfl)

theorem injective_subOneRestrict (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    Function.Injective (subOneRestrict s) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : s (x : A) - (x : A) = 0 := by
    have h := congrArg Subtype.val hx
    rw [coe_subOneRestrict_apply] at h
    simpa using h
  have hmem : (x : A) ∈ (s - 1 : AddMonoid.End A).ker ⊓ (s - 1 : AddMonoid.End A).range :=
    ⟨mem_ker_sub_one_iff.2 (sub_eq_zero.1 h1), x.2⟩
  rw [inf_ker_range_sub_one_eq_bot hp hs, AddSubgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem bijective_subOneRestrict [Finite A] (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    Function.Bijective (subOneRestrict s) :=
  Function.Injective.bijective_of_finite (injective_subOneRestrict hp hs)

noncomputable def subOneRestrictEquiv [Finite A] (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1) :
    (s - 1 : AddMonoid.End A).range ≃+ (s - 1 : AddMonoid.End A).range :=
  AddEquiv.ofBijective _ (bijective_subOneRestrict hp hs)

@[simp]
theorem coe_subOneRestrictEquiv_apply [Finite A] (hp : p.Coprime (Nat.card A)) (hs : s ^ p = 1)
    (x : (s - 1 : AddMonoid.End A).range) :
    (subOneRestrictEquiv hp hs x : A) = s (x : A) - (x : A) := (rfl)

def AddAut.toEnd (σ : AddAut A) : AddMonoid.End A := σ.toAddMonoidHom

@[simp]
theorem AddAut.toEnd_apply (σ : AddAut A) (a : A) : AddAut.toEnd σ a = σ a := (rfl)

theorem AddAut.toEnd_pow (σ : AddAut A) (n : ℕ) : AddAut.toEnd σ ^ n = AddAut.toEnd (n • σ) := by
  induction n with
  | zero => ext a; rfl
  | succ n ih =>
      ext a
      rw [pow_succ', ih]
      change σ ((n • σ) a) = ((n + 1) • σ) a
      rw [succ_nsmul', _root_.AddAut.add_apply]

theorem AddAut.toEnd_pow_eq_one {σ : AddAut A} (hσ : p • σ = 0) : AddAut.toEnd σ ^ p = 1 := by
  rw [AddAut.toEnd_pow, hσ]
  ext a; rfl

variable {σ : AddAut A}

theorem isCompl_ker_range_sub_one_of_prime (hp : p.Prime) (hdvd : ¬p ∣ Nat.card A)
    (hσ : p • σ = 0) :
    IsCompl (AddAut.toEnd σ - 1 : AddMonoid.End A).ker
      (AddAut.toEnd σ - 1 : AddMonoid.End A).range :=
  isCompl_ker_range_sub_one (hp.coprime_iff_not_dvd.2 hdvd) (AddAut.toEnd_pow_eq_one hσ)

theorem map_range_sub_one_of_prime (hp : p.Prime) (hdvd : ¬p ∣ Nat.card A) (hσ : p • σ = 0) :
    ((AddAut.toEnd σ - 1 : AddMonoid.End A).range).map (AddAut.toEnd σ : A →+ A)
      = (AddAut.toEnd σ - 1 : AddMonoid.End A).range :=
  map_range_sub_one (hp.coprime_iff_not_dvd.2 hdvd) (AddAut.toEnd_pow_eq_one hσ)

theorem bijective_subOneRestrict_of_prime [Finite A] (hp : p.Prime) (hdvd : ¬p ∣ Nat.card A)
    (hσ : p • σ = 0) : Function.Bijective (subOneRestrict (AddAut.toEnd σ)) :=
  bijective_subOneRestrict (hp.coprime_iff_not_dvd.2 hdvd) (AddAut.toEnd_pow_eq_one hσ)

end
end CFSG.FeitThompson
