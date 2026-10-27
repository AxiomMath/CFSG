module

public import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.OddCriticalExponentSubgroup
import CFSG.FeitThompson.Local.PointwiseStabilizerSelfCentralizingPGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup MulAction

variable {p : ℕ} {P : Type*} [Group P]

theorem mem_centralizer_apply_iff_of_fixes (e : MulAut P) {F : Subgroup P}
    (he : ∀ x ∈ F, e x = x) (x : P) :
    e x ∈ centralizer (F : Set P) ↔ x ∈ centralizer (F : Set P) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h f hf
    refine e.injective ?_
    rw [map_mul, map_mul, he f hf]
    exact h f hf
  · intro h f hf
    have h1 : e (f * x) = e (x * f) := by rw [h f hf]
    rw [map_mul, map_mul, he f hf] at h1
    exact h1

theorem centralizer_fixedPoints_range_le [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) {D : Type*} [Group D] [Finite D] (ρ : D →* MulAut P)
    (hcop : (Nat.card D).Coprime (Nat.card P))
    (htors : ∀ x ∈ centralizer (FixedPoints.subgroup ρ.range P : Set P), x ^ p = 1 →
      x ∈ FixedPoints.subgroup ρ.range P) :
    centralizer (FixedPoints.subgroup ρ.range P : Set P) ≤ FixedPoints.subgroup ρ.range P := by
  have := Fact.mk hp
  set F := FixedPoints.subgroup ρ.range P with hFdef
  set C := centralizer (F : Set P) with hCdef
  have hFfix : ∀ d : D, ∀ y ∈ F, ρ d y = y := fun d y hy =>
    (mem_fixedPoints_range_iff ρ).mp hy d
  have hinv : ∀ (d : D) (x : P), ρ d x ∈ C ↔ x ∈ C := fun d x =>
    mem_centralizer_apply_iff_of_fixes (ρ d) (hFfix d) x
  rcases eq_or_ne C ⊥ with hC | hC
  · rw [hC]; exact bot_le
  have hCnt : Nontrivial ↥C := C.nontrivial_iff_ne_bot.mpr hC
  have hPnt : Nontrivial P := by
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥C)
    exact ⟨⟨(x : P), 1, fun h => hx (Subtype.ext (by rw [h, Subgroup.coe_one]))⟩⟩
  have hpdvd : p ∣ Nat.card P := by
    rcases hP.card_eq_or_dvd with h | h
    · have := Finite.one_lt_card (α := P)
      omega
    · exact h
  have hcopp : (Nat.card D).Coprime p := hcop.coprime_dvd_right hpdvd
  obtain ⟨H, hH⟩ := exists_isOddCriticalExponentSubgroup hp hodd (hP.to_subgroup C)
  have hHF : ∀ h : ↥C, h ∈ H → ((h : P) ∈ F) := fun h hh =>
    htors (h : P) h.2 (by simpa using congrArg Subtype.val (hH.pow_eq_one h hh))
  intro x hxC
  rw [hFdef, mem_fixedPoints_range_iff]
  intro d
  set r := restrictSubgroupAut (ρ d) C (hinv d) with hrdef
  have hrfix : r ∈ fixingSubgroup (MulAut ↥C) (H : Set ↥C) := by
    rw [mem_fixingSubgroup_mulAut_iff]
    intro h hh
    ext
    rw [hrdef, coe_restrictSubgroupAut_apply]
    exact hFfix d _ (hHF h hh)
  have hrn : r ^ Nat.card D = 1 := by
    ext y
    rw [hrdef, coe_restrictSubgroupAut_pow_apply, ← map_pow, pow_card_eq_one', map_one]
    rfl
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hH.isPGroup_fixingSubgroup) ⟨r, hrfix⟩
  have hko : orderOf r = p ^ k := by rw [← hk, orderOf_mk]
  have hpk : p ^ k = 1 :=
    (hcopp.pow_right k).symm.eq_one_of_dvd (hko ▸ orderOf_dvd_of_pow_eq_one hrn)
  have hr1 : r = 1 := orderOf_eq_one_iff.mp (by rw [hko, hpk])
  have hres := congrArg (fun f => ((f (⟨x, hxC⟩ : ↥C) : ↥C) : P)) hr1
  simpa [hrdef] using hres

theorem fixedPoints_range_eq_top_of_coprime_of_pow_eq_one_mem [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) {D : Type*} [Group D] [Finite D] (ρ : D →* MulAut P)
    (hcop : (Nat.card D).Coprime (Nat.card P))
    (htors : ∀ x ∈ centralizer (FixedPoints.subgroup ρ.range P : Set P), x ^ p = 1 →
      x ∈ FixedPoints.subgroup ρ.range P) :
    FixedPoints.subgroup ρ.range P = ⊤ :=
  fixedPoints_range_eq_top_of_coprime_of_centralizer_le hp hP ρ hcop
    (centralizer_fixedPoints_range_le hp hodd hP ρ hcop htors)

theorem apply_eq_self_of_coprime_of_pow_eq_one_mem [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) {D : Type*} [Group D] [Finite D] (ρ : D →* MulAut P)
    (hcop : (Nat.card D).Coprime (Nat.card P))
    (htors : ∀ x ∈ centralizer (FixedPoints.subgroup ρ.range P : Set P), x ^ p = 1 →
      x ∈ FixedPoints.subgroup ρ.range P) (d : D) (x : P) :
    ρ d x = x :=
  (mem_fixedPoints_range_iff ρ).mp
    ((fixedPoints_range_eq_top_of_coprime_of_pow_eq_one_mem hp hodd hP ρ hcop htors) ▸ mem_top x) d

end

end CFSG.FeitThompson
