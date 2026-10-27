module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaRel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.AaGeneric
public import Certificates.Certificate24205
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Assembly

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native
open scoped Matrix

set_option linter.unusedSectionVars false

section


@[expose] noncomputable def gA : Fin 4 → J := ![gAa1, gAa2, gAa3, gAa4]

@[expose] noncomputable def AaJ : Subgroup J := Subgroup.closure (Set.range gA)

theorem gA_comm (R : AaRel) : ∀ i j, gA i * gA j = gA j * gA i := by
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact R.comm12
  · exact R.comm13
  · exact R.comm14
  · exact R.comm12.symm
  · rfl
  · exact R.comm23
  · exact R.comm24
  · exact R.comm13.symm
  · exact R.comm23.symm
  · rfl
  · exact R.comm34
  · exact R.comm14.symm
  · exact R.comm24.symm
  · exact R.comm34.symm
  · rfl

theorem gA_sq (R : AaRel) : ∀ i, gA i * gA i ∈ A := by
  intro i
  fin_cases i
  · show gAa1 * gAa1 ∈ A
    rw [R.sq1]
    exact cA_mem _
  · show gAa2 * gAa2 ∈ A
    rw [R.sq2]
    exact cA_mem _
  · show gAa3 * gAa3 ∈ A
    rw [R.sq3]
    exact cA_mem _
  · show gAa4 * gAa4 ∈ A
    rw [R.sq4]
    exact cA_mem _

theorem gA_mem (i : Fin 4) : gA i ∈ AaJ := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] def colC : Fin 4 → Vec4 := ![codeVec 4 2, codeVec 4 1, codeVec 4 5, codeVec 4 10]

@[expose] def fC (e : Vec4) : Vec4 := ![e 1 + e 3, e 0 + e 2, e 2, e 3]

theorem span_colC (e : Vec4) :
    e = fC e 0 • colC 0 + fC e 1 • colC 1 + fC e 2 • colC 2 + fC e 3 • colC 3 := by
  revert e
  decide

theorem A_le_of_colC (H : Subgroup J) (h : ∀ i : Fin 4, cA (colC i) ∈ H) : A ≤ H := by
  intro a ha
  obtain ⟨e, rfl⟩ := exists_cA ha
  have hsum := cA_sum colC (fC e)
  rw [← span_colC e] at hsum
  rw [hsum]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.pow_mem (h 0) _) (H.pow_mem (h 1) _))
    (H.pow_mem (h 2) _)) (H.pow_mem (h 3) _)

theorem cA_colC_eq (R : AaRel) (i : Fin 4) : cA (colC i) = gA i * gA i := by
  fin_cases i
  · exact R.sq1.symm
  · exact R.sq2.symm
  · exact R.sq3.symm
  · exact R.sq4.symm

theorem A_le_AaJ (R : AaRel) : A ≤ AaJ :=
  A_le_of_colC AaJ fun i => by
    rw [cA_colC_eq R i]
    exact AaJ.mul_mem (gA_mem i) (gA_mem i)

theorem isRows_prodBits (c : ℕ) : IsRows (rowsPE c) (prodBits gA (codeVec 4 c)) := by
  have h0 : (codeVec 4 c 0).val = c % 2 := by simp [codeVec, bitZ_val]
  have h1 : (codeVec 4 c 1).val = c / 2 % 2 := by simp [codeVec, bitZ_val]
  have h2 : (codeVec 4 c 2).val = c / 4 % 2 := by
    simp only [codeVec, bitZ_val]
    norm_num
  have h3 : (codeVec 4 c 3).val = c / 8 % 2 := by
    simp only [codeVec, bitZ_val]
    norm_num
  show IsRows (rowsPE c) (gAa1 ^ (codeVec 4 c 0).val * gAa2 ^ (codeVec 4 c 1).val *
    gAa3 ^ (codeVec 4 c 2).val * gAa4 ^ (codeVec 4 c 3).val)
  rw [h0, h1, h2, h3]
  exact (((isRows_gAa1.pow _).mul (isRows_gAa2.pow _)).mul (isRows_gAa3.pow _)).mul
    (isRows_gAa4.pow _)

theorem prodBits_notMem :
    ∀ e : Vec4, e ≠ 0 → prodBits gA e ∉ A := by
  intro e he hmem
  obtain ⟨c, hc, rfl⟩ := exists_codeVec 4 e
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact he (codeVec_zero 4)
  obtain ⟨e', heq⟩ := exists_cA hmem
  obtain ⟨c', hc', rfl⟩ := exists_codeVec 4 e'
  have hc16 : c < 16 := lt_of_lt_of_eq hc (by norm_num)
  have hc'16 : c' < 16 := lt_of_lt_of_eq hc' (by norm_num)
  have h := Certificates.certificate24205 (c - 1) (by omega) c' hc'16
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hc0)] at h
  exact (isRows_prodBits c).ne_of_eqRows (isRows_cA c') h heq.symm

theorem card_AaJ (R : AaRel) : Nat.card AaJ = 2 ^ 8 := by
  have h := card_closure_four gA A (gA_comm R) (gA_sq R) (A_le_AaJ R) prodBits_notMem
  rw [A_card] at h
  exact h

theorem mem_B_of_comm_aGen {m : J} (h : ∀ i : Fin 4, m * aGen i = aGen i * m) : m ∈ B := by
  rw [mem_B_iff]
  have hC : ∀ i : Fin 4, aGen i ∈ Subgroup.centralizer ({m} : Set J) := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact h i
  intro a ha
  obtain ⟨e, rfl⟩ := exists_cA ha
  exact (Subgroup.mem_centralizer_iff.1 (cA_mem_of _ hC e)) m (Set.mem_singleton m)

theorem gA_mem_B (R : AaRel) (i : Fin 4) : gA i ∈ B := by
  fin_cases i
  · refine mem_B_of_comm_aGen fun j => ?_
    fin_cases j
    · exact R.cen10
    · exact R.cen11
    · exact R.cen12
    · exact R.cen13
  · refine mem_B_of_comm_aGen fun j => ?_
    fin_cases j
    · exact R.cen20
    · exact R.cen21
    · exact R.cen22
    · exact R.cen23
  · refine mem_B_of_comm_aGen fun j => ?_
    fin_cases j
    · exact R.cen30
    · exact R.cen31
    · exact R.cen32
    · exact R.cen33
  · refine mem_B_of_comm_aGen fun j => ?_
    fin_cases j
    · exact R.cen40
    · exact R.cen41
    · exact R.cen42
    · exact R.cen43

theorem AaJ_le_B (R : AaRel) : AaJ ≤ B := by
  refine (Subgroup.closure_le B).2 ?_
  rintro _ ⟨i, rfl⟩
  exact gA_mem_B R i

theorem AaJ_comm (R : AaRel) : ∀ x ∈ AaJ, ∀ y ∈ AaJ, x * y = y * x :=
  closure_range_comm gA (gA_comm R)

theorem AaJ_sq_mem (R : AaRel) : ∀ x ∈ AaJ, x * x ∈ A :=
  sq_mem_of_closure gA A (gA_comm R) (gA_sq R)

theorem AaJ_exp (R : AaRel) : ∀ x ∈ AaJ, x ^ 4 = 1 := by
  intro x hx
  have h := A_sq _ (AaJ_sq_mem R x hx)
  calc x ^ 4 = (x ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (x * x) ^ 2 := by rw [sq x]
    _ = 1 := h

@[expose] noncomputable def sqAa (R : AaRel) : ↥AaJ →* J :=
  MonoidHom.mk' (fun x => (x : J) ^ 2) (fun x y => by
    have h := AaJ_comm R _ x.2 _ y.2
    show ((x : J) * y) ^ 2 = (x : J) ^ 2 * (y : J) ^ 2
    calc ((x : J) * y) ^ 2 = (x * y) * (x * y) := sq ((x : J) * y)
      _ = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← h]
      _ = (x * x) * (y * y) := by group
      _ = (x : J) ^ 2 * (y : J) ^ 2 := by rw [sq (x : J), sq (y : J)])

theorem A_eq_sq_AaJ (R : AaRel) : ∀ y, y ∈ A ↔ ∃ x ∈ AaJ, x ^ 2 = y := by
  intro y
  constructor
  · intro hy
    have hsq : ∀ i : Fin 4, (sqAa R) ⟨gA i, gA_mem i⟩ = gA i * gA i := fun i => sq (gA i)
    have hle : A ≤ (sqAa R).range := A_le_of_colC _ fun i =>
      ⟨⟨gA i, gA_mem i⟩, (hsq i).trans (cA_colC_eq R i).symm⟩
    obtain ⟨x, hx⟩ := hle hy
    exact ⟨x, x.2, hx⟩
  · rintro ⟨x, hx, rfl⟩
    rw [sq]
    exact AaJ_sq_mem R x hx

theorem bAa_mem_B (R : AaRel) : bAa ∈ B :=
  mem_B_of_comm_aGen fun j => by
    fin_cases j
    · exact R.bcen0
    · exact R.bcen1
    · exact R.bcen2
    · exact R.bcen3

theorem bAa_not_mem (R : AaRel) : bAa ∉ AaJ := by
  intro hb
  have hcomm : bAa * gAa1 = gAa1 * bAa := AaJ_comm R _ hb _ (gA_mem 0)
  have h1 : gAa1 * 1 = gAa1 * (gAa1 * gAa1) := by
    calc gAa1 * 1 = gAa1 * (bAa * bAa) := by rw [R.bsq]
      _ = (gAa1 * bAa) * bAa := (mul_assoc _ _ _).symm
      _ = (bAa * gAa1) * bAa := by rw [hcomm]
      _ = gAa1 * (gAa1 * gAa1) := R.binv1
  have h2 : cA (codeVec 4 2) = 1 := by
    rw [← R.sq1]
    exact (mul_left_cancel h1).symm
  have h3 := eq_zero_of_cA_eq_one h2
  have h4 : (codeVec 4 2 : Vec4) ≠ 0 := by decide
  exact h4 h3

theorem bAa_sq (R : AaRel) : bAa ^ 2 = 1 := by
  rw [sq]
  exact R.bsq

theorem bAa_inv (R : AaRel) : ∀ x ∈ AaJ, bAa * x * bAa⁻¹ = x⁻¹ := by
  have hbinv : bAa⁻¹ = bAa := inv_eq_of_mul_eq_one_right R.bsq
  have hgen : ∀ i, bAa * gA i * bAa⁻¹ = (gA i)⁻¹ := by
    intro i
    rw [hbinv]
    have hq : (gA i * gA i) * (gA i * gA i) = 1 := by
      have := A_sq _ (gA_sq R i)
      rwa [sq] at this
    have hi : bAa * gA i * bAa = gA i * (gA i * gA i) := by
      fin_cases i
      exacts [R.binv1, R.binv2, R.binv3, R.binv4]
    rw [hi]
    refine eq_inv_of_mul_eq_one_left ?_
    calc gA i * (gA i * gA i) * gA i = (gA i * gA i) * (gA i * gA i) := by group
      _ = 1 := hq
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => bAa * x * bAa⁻¹ = x⁻¹) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact hgen i
  · simp
  · intro a b ha hb hpa hpb
    have e : bAa * (a * b) * bAa⁻¹ = (bAa * a * bAa⁻¹) * (bAa * b * bAa⁻¹) := by group
    rw [e, hpa, hpb, mul_inv_rev]
    exact AaJ_comm R _ (AaJ.inv_mem ha) _ (AaJ.inv_mem hb)
  · intro a ha hpa
    have e : bAa * a⁻¹ * bAa⁻¹ = (bAa * a * bAa⁻¹)⁻¹ := by group
    rw [e, hpa]

end

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
