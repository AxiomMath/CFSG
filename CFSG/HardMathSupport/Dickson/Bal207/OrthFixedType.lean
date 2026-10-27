module

public import CFSG.RankThree.PartOne.K159.RowFourFixed

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.GroupTheory.WeirSylow QuadraticMap
  CFSG.RankThree.PartOne.K159

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] [CharP K 2] in
theorem othersSpace_invariant {u : V} (hu : u ∈ othersSpace x.toLinearMap (X - 1)) :
    x u ∈ othersSpace x.toLinearMap (X - 1) := by
  have hmap : (othersSpace x.toLinearMap (X - 1)).map x.toLinearMap ≤
      othersSpace x.toLinearMap (X - 1) := by
    unfold othersSpace
    rw [Submodule.map_iSup]
    refine iSup_le fun k => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hk => ?_
    refine le_iSup₂_of_le k hk ?_
    rintro _ ⟨v, hv, rfl⟩
    exact apply_mem_primaryComponent (Commute.refl _) hv
  exact hmap ⟨u, hu, rfl⟩

theorem fixed_type (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {n : ℕ} (hdim : finrank K V = 2 * n)
    (hV : IsPlusType Q ↔ Even n) :
    ∃ s k : ℕ, finrank K (fixedSpace x) = 2 * s ∧
      finrank K (othersSpace x.toLinearMap (X - 1)) = 2 * k ∧ s + k = n ∧
      (1 ≤ s → (IsPlusType (Q.comp (fixedSpace x).subtype) ↔ Even s)) := by
  classical
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  obtain ⟨s, hs⟩ := hx.even_finrank_fixed
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  set W := fixedSpace x with hW
  set R := othersSpace x.toLinearMap (X - 1) with hR
  have hRfix : ∀ u ∈ R, x u = u → u = 0 := fun u hu hxu =>
    (Submodule.disjoint_def.1 hcompl.disjoint) u (mem_fixedSpace.2 hxu) hu
  have hRreg : RegOn Q R := by
    intro u hu hperp
    refine hx.regular u fun v => ?_
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm Q u w,
      horth w hw u hu, add_zero]
  have hRdim : finrank K R = 2 * (n - s) := by omega
  refine ⟨s, n - s, by omega, hRdim, by omega, fun hs1 => ?_⟩
  have hRtype := isPlusType_iff_even_of_fixedFree hx hp hp2 hpq (n - s) R
    (fun u hu => othersSpace_invariant hu) hRreg hRfix hRdim
  by_cases hk : n - s = 0
  · have hRb : R = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have hWtop : W = ⊤ := by
      have h := hcompl.sup_eq_top
      rwa [hRb, sup_bot_eq] at h
    rw [← isPlusType_congr ((isometryTop Q).trans (isometryOfEq Q hWtop.symm)), hV]
    have hns : n = s := by omega
    rw [hns]
  · have hk1 : 1 ≤ n - s := by omega
    have eV : Q.IsometryEquiv ((Q.comp W.subtype).prod (Q.comp R.subtype)) :=
      (isometryTop Q).trans ((isometryOfEq Q hcompl.sup_eq_top.symm).trans
        (isometryEquivSup Q W R hcompl.disjoint horth))
    have htype : IsPlusType Q ↔
        (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp R.subtype)) :=
      (isPlusType_congr eV).trans
        (isPlusType_prod_iff hx.polarBilin_fixed_nondegenerate (nondegenerate_of_regOn hRreg) hs1
          hk1 (by omega) hRdim)
    have hpar : Even (s + (n - s)) ↔ (Even s ↔ Even (n - s)) := Nat.even_add
    rw [show s + (n - s) = n by omega] at hpar
    rw [hRtype, hV, hpar] at htype
    tauto

theorem fixed_type' (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {n : ℕ} (hdim : finrank K V = 2 * n) :
    ∃ s k : ℕ, finrank K (fixedSpace x) = 2 * s ∧
      finrank K (othersSpace x.toLinearMap (X - 1)) = 2 * k ∧ s + k = n ∧
      (1 ≤ s → (IsPlusType (Q.comp (fixedSpace x).subtype) ↔ (IsPlusType Q ↔ Even k))) := by
  classical
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  obtain ⟨s, hs⟩ := hx.even_finrank_fixed
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  set W := fixedSpace x with hW
  set R := othersSpace x.toLinearMap (X - 1) with hR
  have hRfix : ∀ u ∈ R, x u = u → u = 0 := fun u hu hxu =>
    (Submodule.disjoint_def.1 hcompl.disjoint) u (mem_fixedSpace.2 hxu) hu
  have hRreg : RegOn Q R := by
    intro u hu hperp
    refine hx.regular u fun v => ?_
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm Q u w,
      horth w hw u hu, add_zero]
  have hRdim : finrank K R = 2 * (n - s) := by omega
  refine ⟨s, n - s, by omega, hRdim, by omega, fun hs1 => ?_⟩
  have hRtype := isPlusType_iff_even_of_fixedFree hx hp hp2 hpq (n - s) R
    (fun u hu => othersSpace_invariant hu) hRreg hRfix hRdim
  by_cases hk : n - s = 0
  · have hRb : R = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have hWtop : W = ⊤ := by
      have h := hcompl.sup_eq_top
      rwa [hRb, sup_bot_eq] at h
    have hWtype : IsPlusType (Q.comp W.subtype) ↔ IsPlusType Q :=
      (isPlusType_congr ((isometryTop Q).trans (isometryOfEq Q hWtop.symm))).symm
    rw [hWtype, hk]
    simp
  · have hk1 : 1 ≤ n - s := by omega
    have eV : Q.IsometryEquiv ((Q.comp W.subtype).prod (Q.comp R.subtype)) :=
      (isometryTop Q).trans ((isometryOfEq Q hcompl.sup_eq_top.symm).trans
        (isometryEquivSup Q W R hcompl.disjoint horth))
    have htype : IsPlusType Q ↔
        (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp R.subtype)) :=
      (isPlusType_congr eV).trans
        (isPlusType_prod_iff hx.polarBilin_fixed_nondegenerate (nondegenerate_of_regOn hRreg) hs1
          hk1 (by omega) hRdim)
    rw [hRtype] at htype
    tauto

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem monic_phi : (X ^ 2 + X + 1 : K[X]).Monic ∧ (X ^ 2 + X + 1 : K[X]).natDegree = 2 :=
  ⟨by monicity!, by compute_degree!⟩

omit [CharP K 2] in
theorem eq_phi (hx : OddOrderIsometry Q 3 x) (hpq : 3 ∣ Nat.card K + 1) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) : h = X ^ 2 + X + 1 := by
  have hdeg := natDegree_eq_two_of_dvd_card_add_one hx Nat.prime_three (by norm_num) hpq hh hne
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd : h ∣ (X ^ 3 - 1 : K[X]) := hx.dvd_X_pow_sub_one hh
  rw [show (X ^ 3 - 1 : K[X]) = (X - C 1) * (X ^ 2 + X + 1) by rw [C_1]; ring] at hdvd
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
  · exfalso
    have h3 := natDegree_le_of_dvd h1 (X_sub_C_ne_zero 1)
    rw [natDegree_X_sub_C, hdeg] at h3
    omega
  · exact (eq_of_monic_of_dvd_of_natDegree_le hmon monic_phi.1 h2
      (by rw [monic_phi.2, hdeg])).symm

omit [CharP K 2] [FiniteDimensional K V] in
theorem phi_ne : (X ^ 2 + X + 1 : K[X]) ≠ X - 1 := by
  intro h
  have h1 := congrArg natDegree h
  rw [monic_phi.2, show (X - 1 : K[X]) = X - C 1 by rw [C_1], natDegree_X_sub_C] at h1
  omega

theorem phi_mem (hx : OddOrderIsometry Q 3 x) (hpq : 3 ∣ Nat.card K + 1) (hx1 : x ≠ 1) :
    (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
  classical
  obtain ⟨hcompl, -⟩ := hx.fixed_others
  by_contra hnot
  apply hx1
  have hRb : othersSpace x.toLinearMap (X - 1) = ⊥ := by
    unfold othersSpace
    refine le_bot_iff.1 (iSup₂_le fun k hk => ?_)
    exact absurd (eq_phi hx hpq hk.1 hk.2.1 ▸ hk.1) hnot
  have hW' : fixedSpace x = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hRb, sup_bot_eq] at this
  ext v
  have : v ∈ fixedSpace x := hW' ▸ Submodule.mem_top
  exact mem_fixedSpace.1 this

omit [CharP K 2] in
theorem othersSpace_eq (hx : OddOrderIsometry Q 3 x) (hpq : 3 ∣ Nat.card K + 1)
    (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap) :
    othersSpace x.toLinearMap (X - 1) = primaryComponent x.toLinearMap (X ^ 2 + X + 1) := by
  classical
  unfold othersSpace
  refine le_antisymm (iSup₂_le fun k hk => ?_) ?_
  · rw [eq_phi hx hpq hk.1 hk.2.1]
  · refine le_iSup₂_of_le (X ^ 2 + X + 1 : K[X]) ⟨hmem, phi_ne, ?_⟩ le_rfl
    rw [CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one]
    exact phi_ne

omit [Finite K] [CharP K 2] in
theorem finrank_phi (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap) :
    finrank K (primaryComponent x.toLinearMap (X ^ 2 + X + 1)) =
      2 * primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) := by
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  rw [finrank_primaryComponent x.toLinearMap (X ^ 2 + X + 1), monic_phi.2]

theorem dims (hx : OddOrderIsometry Q 3 x) (hpq : 3 ∣ Nat.card K + 1) (hx1 : x ≠ 1) {n : ℕ}
    (hdim : finrank K V = 2 * n) (hV : IsPlusType Q ↔ Even n) :
    (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap ∧
      ∃ s : ℕ, finrank K (fixedSpace x) = 2 * s ∧
        s + primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) = n ∧
        (1 ≤ s → (IsPlusType (Q.comp (fixedSpace x).subtype) ↔ Even s)) := by
  have hmem := phi_mem hx hpq hx1
  obtain ⟨s, k, hs, hk, hsk, htype⟩ := fixed_type hx Nat.prime_three (by norm_num) hpq hdim hV
  rw [othersSpace_eq hx hpq hmem, finrank_phi hmem] at hk
  exact ⟨hmem, s, hs, by omega, htype⟩

theorem dims' (hx : OddOrderIsometry Q 3 x) (hpq : 3 ∣ Nat.card K + 1) (hx1 : x ≠ 1) {n : ℕ}
    (hdim : finrank K V = 2 * n) :
    (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap ∧
      ∃ s : ℕ, finrank K (fixedSpace x) = 2 * s ∧
        s + primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) = n ∧
        (1 ≤ s → (IsPlusType (Q.comp (fixedSpace x).subtype) ↔
          (IsPlusType Q ↔ Even (n - s)))) := by
  have hmem := phi_mem hx hpq hx1
  obtain ⟨s, k, hs, hk, hsk, htype⟩ := fixed_type' hx Nat.prime_three (by norm_num) hpq hdim
  rw [othersSpace_eq hx hpq hmem, finrank_phi hmem] at hk
  have hmk : primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) = k := by omega
  refine ⟨hmem, s, hs, by omega, fun hs1 => ?_⟩
  have h := htype hs1
  rwa [show k = n - s by omega] at h

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
