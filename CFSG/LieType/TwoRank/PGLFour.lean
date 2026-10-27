module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import CFSG.LieType.TwoRank.GLElementaryAbelian
import CFSG.LieType.TwoRank.PGLTrace
import CFSG.LieType.TwoRank.PGLSection
import CFSG.LieType.TwoRank.PGLMap
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.LieType.TwoRank

open Matrix

theorem card_le_eight_of_trace_ne_zero {F : Type*} [Field F] [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n] (hn : Fintype.card n = 4)
    (E : Subgroup (ProjGenLinGroup n F)) [IsElementaryAbelian 2 E] {g₀ : GL n F}
    (hg₀E : ProjGenLinGroup.mk g₀ ∈ E) (hg₀ : ProjGenLinGroup.mk g₀ ≠ 1)
    (htr : trace (g₀ : Matrix n n F) ≠ 0) : Nat.card E ≤ 8 := by
  obtain ⟨φ, hφ⟩ := exists_section_of_trace_ne_zero h2 hn E hg₀E hg₀ htr
  have hφinj : Function.Injective φ := by
    intro e e' heq
    apply Subtype.ext
    calc (e : ProjGenLinGroup n F) = ProjGenLinGroup.mk (φ e) := (hφ e).symm
      _ = ProjGenLinGroup.mk (φ e') := by rw [heq]
      _ = (e' : ProjGenLinGroup n F) := hφ e'
  let A : Subgroup (GL n F) := φ.range
  haveI : IsElementaryAbelian 2 A := by
    refine
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    rintro ⟨x, hx⟩
    change x ∈ φ.range at hx
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hx
    apply Subtype.ext
    simpa using congrArg φ (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) e)
  have hcardA : Nat.card A = Nat.card E := by
    show Nat.card φ.range = Nat.card E
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj, Subgroup.card_top]
  have hneg1_mk : ProjGenLinGroup.mk (-1 : GL n F) = 1 := by
    rw [ProjGenLinGroup.mk_eq_one]
    exact Subgroup.mem_center_iff.mpr fun g => by simp
  have hneg1_not_mem : (-1 : GL n F) ∉ A := by
    change (-1 : GL n F) ∉ φ.range
    rw [MonoidHom.mem_range]
    rintro ⟨e, he⟩
    have he1 : e = 1 := by
      apply Subtype.ext
      calc (e : ProjGenLinGroup n F) = ProjGenLinGroup.mk (φ e) := (hφ e).symm
        _ = ProjGenLinGroup.mk (-1 : GL n F) := by rw [he]
        _ = 1 := hneg1_mk
    have hneg1_eq_one : (-1 : GL n F) = 1 := by
      calc (-1 : GL n F) = φ e := he.symm
        _ = φ 1 := by rw [he1]
        _ = 1 := map_one φ
    obtain ⟨i⟩ : Nonempty n := Fintype.card_pos_iff.mp (by rw [hn]; norm_num)
    have hentry : (-1 : F) = 1 := by
      simpa using congrArg (fun x : GL n F => (x : Matrix n n F) i i) hneg1_eq_one
    exact h2 (by linear_combination -hentry)
  have hle := two_mul_card_le_two_pow_of_neg_one_not_mem h2 A hneg1_not_mem
  rw [hcardA, hn] at hle
  norm_num at hle
  omega

theorem card_le_sixteen_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n] (hn : Fintype.card n = 4)
    (E : Subgroup (ProjGenLinGroup n F)) [IsElementaryAbelian 2 E] : Nat.card E ≤ 16 := by
  by_cases h : ∀ g : GL n F, ProjGenLinGroup.mk g ∈ E → ProjGenLinGroup.mk g ≠ 1 →
      trace (g : Matrix n n F) = 0
  · have hnF : (Fintype.card n : F) ≠ 0 := by
      rw [hn, Nat.cast_ofNat]
      rw [show (4 : F) = 2 * 2 by ring]
      exact mul_ne_zero h2 h2
    have hle := card_le_sq_of_forall_trace_eq_zero hnF E h
    rw [hn] at hle
    norm_num at hle
    exact hle
  · push Not at h
    obtain ⟨g₀, hg₀E, hg₀, htr⟩ := h
    have hle := card_le_eight_of_trace_ne_zero h2 hn E hg₀E hg₀ htr
    exact hle.trans (by norm_num)

theorem card_le_sixteen_of_isElementaryAbelian_pgl_four {F : Type*} [Field F]
    (hF : ringChar F ≠ 2) {n : Type*} [Fintype n] [DecidableEq n] (hn : Fintype.card n = 4)
    (E : Subgroup (ProjGenLinGroup n F)) [IsElementaryAbelian 2 E] : Nat.card E ≤ 16 := by
  let K := AlgebraicClosure F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap F K) 2]
    simpa using (RingHom.injective (algebraMap F K)).ne_iff.mpr h2F
  let E' : Subgroup (ProjGenLinGroup n K) := E.map (ProjGenLinGroup.map (algebraMap F K))
  haveI : IsElementaryAbelian 2 E' :=
    IsElementaryAbelian.map (ProjGenLinGroup.map (algebraMap F K))
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (projGenLinGroup_map_injective (n := n) (algebraMap F K))
  have hle : Nat.card E' ≤ 16 := card_le_sixteen_of_isAlgClosed h2K hn E'
  rw [hcard] at hle
  exact hle

theorem trace_eq_zero_of_card_eq_sixteen {F : Type*} [Field F] (hF : ringChar F ≠ 2)
    {n : Type*} [Fintype n] [DecidableEq n] (hn : Fintype.card n = 4)
    (E : Subgroup (ProjGenLinGroup n F)) [IsElementaryAbelian 2 E] (hE : Nat.card E = 16)
    {g : GL n F} (hgE : ProjGenLinGroup.mk g ∈ E) (hg : ProjGenLinGroup.mk g ≠ 1) :
    trace (g : Matrix n n F) = 0 := by
  by_contra htr
  let K := AlgebraicClosure F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap F K) 2]
    simpa using (RingHom.injective (algebraMap F K)).ne_iff.mpr h2F
  let E' : Subgroup (ProjGenLinGroup n K) := E.map (ProjGenLinGroup.map (algebraMap F K))
  haveI : IsElementaryAbelian 2 E' :=
    IsElementaryAbelian.map (ProjGenLinGroup.map (algebraMap F K))
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (projGenLinGroup_map_injective (n := n) (algebraMap F K))
  let g' := GeneralLinearGroup.map (algebraMap F K) g
  have hg'E' : ProjGenLinGroup.mk g' ∈ E' := by
    have hgm : ProjGenLinGroup.mk g' =
        ProjGenLinGroup.map (algebraMap F K) (ProjGenLinGroup.mk g) := by
      show ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap F K) g) =
        ProjGenLinGroup.map (algebraMap F K) (ProjGenLinGroup.mk g)
      exact (ProjGenLinGroup.map_mk (n := n) (algebraMap F K) g).symm
    rw [hgm]
    exact Subgroup.mem_map_of_mem _ hgE
  have hg' : ProjGenLinGroup.mk g' ≠ 1 := by
    intro h
    exact hg ((projGenLinGroup_map_injective (n := n) (algebraMap F K)) (by
      rw [ProjGenLinGroup.map_mk, h, map_one]))
  have htr' : trace (g' : Matrix n n K) ≠ 0 := by
    have hco : (g' : Matrix n n K) = (g : Matrix n n F).map (algebraMap F K) := rfl
    rw [hco, ← AddMonoidHom.map_trace (algebraMap F K) (g : Matrix n n F)]
    simpa using (RingHom.injective (algebraMap F K)).ne_iff.mpr htr
  have hle : Nat.card E' ≤ 8 :=
    card_le_eight_of_trace_ne_zero h2K hn E' hg'E' hg' htr'
  rw [hcard, hE] at hle
  omega

end CFSG.LieType.TwoRank
