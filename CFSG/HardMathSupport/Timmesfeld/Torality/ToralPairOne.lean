module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2ConjLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

private theorem exists_conj_mem_monomial_familyGroup_E6_three
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {y z : ModGL Tag.E6 L}
    (hy : y ∈ familyGroup (K := L) (fun _ : Unit => a))
    (hzC : z ∈ familyCentralizer Tag.E6 L (fun _ : Unit => a))
    (hzN : z * y * z⁻¹ ∈ monomialSubgroup Tag.E6 L) (hy3 : y ^ 3 = 1) :
    ∃ c ∈ familyGroup (K := L) (fun _ : Unit => a),
      c * y * c⁻¹ ∈ monomialSubgroup Tag.E6 L ∧
        c * y * c⁻¹ ∈ familyGroup (K := L) (fun _ : Unit => a) ∧
          (c * y * c⁻¹) ^ 3 = 1 := by
  obtain ⟨w, hw, v, hv, hzv⟩ := familyCentralizer_le_mul Tag.E6 L (fun _ : Unit => a) hzC
  set nw : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hnwN : nw ∈ monomialSubgroup Tag.E6 L := by
    rw [hnw]
    exact canonicalRep_mem_monomialSubgroup L w
  have hnwM : nw ∈ Subgroup.normalizer
      (familyGroup (K := L) (fun _ : Unit => a) : Set (ModGL Tag.E6 L)) := by
    rw [hnw]
    exact canonicalRep_mem_normalizer_familyGroup (K := L) hw
  have hcM : nw⁻¹ * z ∈ familyGroup (K := L) (fun _ : Unit => a) := by
    have hconj : nw⁻¹ * z = nw⁻¹ * v * nw := by
      rw [hzv]
      group
    rw [hconj]
    simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hnwM) v).1 hv
  refine ⟨nw⁻¹ * z, hcM, ?_, ?_, ?_⟩
  · have e : (nw⁻¹ * z) * y * (nw⁻¹ * z)⁻¹ = nw⁻¹ * (z * y * z⁻¹) * nw := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnwN) hzN) hnwN
  · exact mul_mem (mul_mem hcM hy) (inv_mem hcM)
  · rw [conj_pow, hy3, mul_one, mul_inv_cancel]

private theorem exists_conj_torus_of_mem_monomial_familyGroup_E6_three
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {a : Fin Tag.E6.rank → Lˣ}
    {n : ModGL Tag.E6 L} (hnM : n ∈ familyGroup (K := L) (fun _ : Unit => a))
    (hnN : n ∈ monomialSubgroup Tag.E6 L) (hn3 : n ^ 3 = 1) :
    ∃ r ∈ familyGroup (K := L) (fun _ : Unit => a),
      r * n * r⁻¹ ∈ torusGroup Tag.E6 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnM' : n ∈ toralRootGroup Tag.E6 L a := by
    rw [← familyGroup_unit_eq_toralRootGroup (L := L) a]
    exact hnM
  have hker : weylQuotientHom Tag.E6 L ⟨n, hnN⟩ ∈ kernelReflectionGroup a :=
    d4t2tp_weyl_mem_kernelReflectionGroup hnN hnM'
  have hnW : weylQuotientHom Tag.E6 L ⟨n, hnN⟩ ∈
      kernelWeylGroup (CFSG.LieType.AlgebraicGroups.rootCharHom a) := by
    rwa [CFSG.LieType.AlgebraicGroups.kernelReflectionGroup_eq_kernelWeylGroup_rootCharHom a]
      at hker
  have hn3' : weylQuotientHom Tag.E6 L ⟨n, hnN⟩ ^ 3 = 1 :=
    weylQuotientHom_pow_eq_one hnN hn3
  have hLp : ringChar L ≠ 3 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨r, hr, hrn⟩ :=
    monomialToralAt_E6_three L hLp Lˣ (CFSG.LieType.AlgebraicGroups.rootCharHom a) n hnN hnW hn3'
  refine ⟨r, ?_, hrn⟩
  rw [familyGroup_unit_eq_toralRootGroup (L := L) a]
  exact Subgroup.mem_sup_right hr

theorem exists_conj_mem_torusGroup_of_mem_familyGroup_E6_three
    {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {a : Fin Tag.E6.rank → Lˣ} {y : ModGL Tag.E6 L}
    (hy : y ∈ familyGroup (fun _ : Unit => a)) (hy3 : y ^ 3 = 1) :
    ∃ m ∈ familyGroup (fun _ : Unit => a), m * y * m⁻¹ ∈ torusGroup Tag.E6 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMm : y ∈ familyCentralizer Tag.E6 L (fun _ : Unit => a) :=
    familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => a) hy
  have hcomm_y : rootDiagUnit Tag.E6 a * y = y * rootDiagUnit Tag.E6 a := by
    have h := (mem_familyCentralizer.1 hMm).2 ()
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hBadj : Subgroup.zpowers y ≤ adjointGroup Tag.E6 L :=
    Subgroup.zpowers_le.mpr (mem_familyCentralizer.1 hMm).1
  have hBfin : (Subgroup.zpowers y : Set (ModGL Tag.E6 L)).Finite := by
    haveI : Finite (Subgroup.zpowers y) :=
      Nat.finite_of_card_ne_zero (by
        rw [Nat.card_zpowers]
        exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hy3) (by norm_num)).ne')
    exact Set.toFinite _
  have hBa : ∀ x ∈ Subgroup.zpowers y,
      rootDiagUnit Tag.E6 a * x = x * rootDiagUnit Tag.E6 a := by
    have hle : Subgroup.zpowers y ≤ Subgroup.centralizer
        ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 L)) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.2 hcomm_y.symm)
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hexp : ∀ x ∈ Subgroup.zpowers y, x ^ 3 = 1 := by
    intro x hx
    have h1 : orderOf x ∣ orderOf y := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers y) hx
      rwa [Nat.card_zpowers] at h
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans (orderOf_dvd_of_pow_eq_one hy3))
  obtain ⟨z, hz, hzd, hzN⟩ :=
    exists_conj_le_monomial_centralizer_bar (τ := Tag.E6) (ℓ := 2) (p := 3)
      (by norm_num) halg a hBadj hBfin hBa hexp
  have hzC : z ∈ familyCentralizer Tag.E6 L (fun _ : Unit => a) :=
    mem_familyCentralizer.2 ⟨hz, fun _ => by rw [hzd, mul_inv_cancel_right]⟩
  obtain ⟨c, hcM, hcN, hcG, hc3⟩ :=
    exists_conj_mem_monomial_familyGroup_E6_three (a := a) hy hzC
      (hzN y (Subgroup.mem_zpowers y)) hy3
  obtain ⟨r, hrM, hrn⟩ :=
    exists_conj_torus_of_mem_monomial_familyGroup_E6_three (a := a) hcG hcN hc3
  refine ⟨r * c, mul_mem hrM hcM, ?_⟩
  have e : (r * c) * y * (r * c)⁻¹ = r * (c * y * c⁻¹) * r⁻¹ := by group
  rw [e]
  exact hrn

end CFSG.HardMathSupport.Timmesfeld.Torality
