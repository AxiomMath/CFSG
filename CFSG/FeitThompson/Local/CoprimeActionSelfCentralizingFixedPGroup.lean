module

public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Local.ConjugateFixedPointOrders
import CFSG.FeitThompson.Local.PointwiseStabilizerSelfCentralizingPGroup
import Mathlib.GroupTheory.Nilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup MulAction

variable {P : Type*} [Group P]

def restrictSubgroupAut (e : MulAut P) (H : Subgroup P) (h : ∀ x : P, e x ∈ H ↔ x ∈ H) :
    MulAut H where
  toFun x := ⟨e x, (h x).2 x.2⟩
  invFun x := ⟨e.symm x, (h (e.symm x)).1 (by simp only [MulEquiv.apply_symm_apply]; exact x.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem coe_restrictSubgroupAut_apply (e : MulAut P) (H : Subgroup P)
    (h : ∀ x : P, e x ∈ H ↔ x ∈ H) (x : H) :
    (restrictSubgroupAut e H h x : P) = e (x : P) := (rfl)

theorem coe_restrictSubgroupAut_pow_apply (e : MulAut P) (H : Subgroup P)
    (h : ∀ x : P, e x ∈ H ↔ x ∈ H) (j : ℕ) (x : H) :
    ((restrictSubgroupAut e H h ^ j) x : P) = (e ^ j) (x : P) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, coe_restrictSubgroupAut_apply, ih, pow_succ',
        MulAut.mul_apply]

theorem mem_map_mulAut_iff (e : MulAut P) (H : Subgroup P) (x : P) :
    e x ∈ H.map e.toMonoidHom ↔ x ∈ H := by
  simp only [Subgroup.mem_map]
  refine ⟨fun ⟨y, hy, hey⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
  have hyx : e y = e x := hey
  exact e.injective hyx ▸ hy

theorem map_eq_self_of_fixes (e : MulAut P) {F : Subgroup P} (he : ∀ x ∈ F, e x = x) :
    F.map e.toMonoidHom = F := by
  ext y
  simp only [Subgroup.mem_map]
  refine ⟨?_, fun hy => ⟨y, hy, he y hy⟩⟩
  rintro ⟨x, hx, rfl⟩
  rw [show e.toMonoidHom x = e x from rfl, he x hx]
  exact hx

theorem mem_normalizer_apply_iff_of_fixes (e : MulAut P) {F : Subgroup P}
    (he : ∀ x ∈ F, e x = x) (x : P) :
    e x ∈ normalizer (F : Set P) ↔ x ∈ normalizer (F : Set P) := by
  rw [← mem_map_mulAut_iff e (normalizer (F : Set P)) x,
    Subgroup.map_normalizer_eq_of_bijective F (f := e.toMonoidHom) (MulEquiv.bijective e),
    map_eq_self_of_fixes e he]

theorem mem_fixedPoints_subgroup_mulAut_iff {B : Subgroup (MulAut P)} {x : P} :
    x ∈ FixedPoints.subgroup B P ↔ ∀ b ∈ B, (b : MulAut P) x = x :=
  CFSG.FeitThompson.mem_fixedPoints_subgroup_iff B x

theorem mem_fixedPoints_range_iff {A : Type*} [Group A] (φ : A →* MulAut P) {x : P} :
    x ∈ FixedPoints.subgroup φ.range P ↔ ∀ a : A, φ a x = x := by
  rw [mem_fixedPoints_subgroup_mulAut_iff]
  exact ⟨fun h a => h (φ a) ⟨a, rfl⟩, by rintro h b ⟨a, rfl⟩; exact h a⟩

theorem fixedPoints_subgroup_eq_toMulAut_range {A : Type*} [Group A] [MulDistribMulAction A P] :
    FixedPoints.subgroup A P
      = FixedPoints.subgroup (MulDistribMulAction.toMulAut A P).range P := by
  ext x
  rw [FixedPoints.mem_subgroup, mem_fixedPoints_range_iff]
  simp [MulDistribMulAction.toMulAut]

variable {p : ℕ}

theorem fixedPoints_subgroup_eq_top_of_centralizer_le [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) (B : Subgroup (MulAut P)) {n : ℕ} (hcop : n.Coprime p)
    (hBn : ∀ b ∈ B, b ^ n = 1)
    (hself : centralizer (FixedPoints.subgroup B P : Set P) ≤ FixedPoints.subgroup B P) :
    FixedPoints.subgroup B P = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  set F := FixedPoints.subgroup B P with hFdef
  by_contra hne
  have hnorm : F < normalizer (F : Set P) :=
    (Group.normalizerCondition_of_isNilpotent (h := hP.isNilpotent)) F
      (lt_of_le_of_ne le_top hne)
  set N := normalizer (F : Set P) with hNdef
  have hFN : F ≤ N := le_normalizer
  set C := F.subgroupOf N with hCdef
  have hCnormal : C.Normal := Subgroup.normal_in_normalizer
  have hCself : centralizer (C : Set N) ≤ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_subgroupOf]
    refine hself ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hmem : (⟨c, hFN hc⟩ : N) ∈ C := by rw [hCdef, Subgroup.mem_subgroupOf]; exact hc
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx _ hmem)
  have hpg : IsPGroup p (fixingSubgroup (MulAut N) (C : Set N)) :=
    isPGroup_fixingSubgroup_mulAut hp (hP.to_subgroup N) C hCself
  have hNF : N ≤ F := by
    intro x hxN
    rw [hFdef, mem_fixedPoints_subgroup_mulAut_iff]
    intro b hb
    have he : ∀ y ∈ F, (b : MulAut P) y = y := fun y hy =>
      mem_fixedPoints_subgroup_mulAut_iff.mp hy b hb
    have hinv : ∀ y : P, b y ∈ N ↔ y ∈ N := fun y =>
      mem_normalizer_apply_iff_of_fixes b he y
    set r := restrictSubgroupAut b N hinv with hrdef
    have hrfix : r ∈ fixingSubgroup (MulAut N) (C : Set N) := by
      rw [mem_fixingSubgroup_mulAut_iff]
      intro c hc
      ext
      rw [hrdef, coe_restrictSubgroupAut_apply]
      exact he _ (Subgroup.mem_subgroupOf.mp hc)
    have hrn : r ^ n = 1 := by
      ext y
      rw [hrdef, coe_restrictSubgroupAut_pow_apply, hBn b hb]
      rfl
    obtain ⟨k, hk⟩ :=
      (IsPGroup.iff_orderOf.mp hpg) (⟨r, hrfix⟩ : fixingSubgroup (MulAut N) (C : Set N))
    have hko : orderOf r = p ^ k := by rw [← hk, orderOf_mk]
    have hpk : p ^ k = 1 :=
      (hcop.pow_right k).symm.eq_one_of_dvd (hko ▸ orderOf_dvd_of_pow_eq_one hrn)
    have hr1 : r = 1 := orderOf_eq_one_iff.mp (by rw [hko, hpk])
    have hres := congrArg (fun f => ((f (⟨x, hxN⟩ : N) : N) : P)) hr1
    simpa [hrdef] using hres
  exact absurd (le_antisymm hFN hNF) hnorm.ne

theorem fixedPoints_range_eq_top_of_coprime_of_centralizer_le [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) {A : Type*} [Group A] [Finite A] (φ : A →* MulAut P)
    (hcop : (Nat.card A).Coprime (Nat.card P))
    (hself : centralizer (FixedPoints.subgroup φ.range P : Set P) ≤
      FixedPoints.subgroup φ.range P) :
    FixedPoints.subgroup φ.range P = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  ·
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by rw [hk, hk0, pow_zero])).1
    exact (eq_top_iff' _).mpr fun x =>
      mem_fixedPoints_subgroup_mulAut_iff.mpr fun b _ => Subsingleton.elim _ _
  ·
    have hpdvd : p ∣ Nat.card P := hk ▸ dvd_pow_self p hk0.ne'
    refine fixedPoints_subgroup_eq_top_of_centralizer_le hp hP φ.range
      (n := Nat.card A) (hcop.coprime_dvd_right hpdvd) ?_ hself
    rintro b ⟨a, rfl⟩
    rw [← map_pow, pow_card_eq_one', map_one]

theorem eq_one_of_coprime_of_centralizer_fixedPoints_le [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) {A : Type*} [Group A] [Finite A] (φ : A →* MulAut P)
    (hcop : (Nat.card A).Coprime (Nat.card P))
    (hself : centralizer (FixedPoints.subgroup φ.range P : Set P) ≤
      FixedPoints.subgroup φ.range P) (a : A) :
    φ a = 1 := by
  have htop := fixedPoints_range_eq_top_of_coprime_of_centralizer_le hp hP φ hcop hself
  ext x
  have hx : x ∈ FixedPoints.subgroup φ.range P := htop ▸ mem_top x
  simpa using mem_fixedPoints_subgroup_mulAut_iff.mp hx (φ a) ⟨a, rfl⟩

end

end CFSG.FeitThompson
