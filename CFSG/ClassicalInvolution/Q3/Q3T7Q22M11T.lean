module

public import CFSG.ClassicalInvolution.Q3.M11Branch
public import CFSG.ClassicalInvolution.Uniform.ULieType
public import CFSG.ClassicalInvolution.ModelFacts.CF3A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.M11Tw

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

theorem isSubnormal_le' {G : Type} [Group G] {H K : Subgroup G} (h : IsSubnormal H K) :
    H ≤ K :=
  h.le

theorem m11_classical_eq {J J' : Subgroup ↥NativeSporadic.M11} {w : ↥NativeSporadic.M11}
    (hJ : IsClassicalMember3 J w) (hJ' : IsClassicalMember3 J' w) : J = J' := by
  classical
  have hc : Nat.card J = 24 := hJ.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  have hc' : Nat.card J' = 24 := hJ'.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  set C := Subgroup.centralizer ({w} : Set ↥NativeSporadic.M11) with hC
  have hJC : J ≤ C := isSubnormal_le' hJ.subnormal
  have hJ'C : J' ≤ C := isSubnormal_le' hJ'.subnormal
  have hCle : Nat.card C ≤ 48 := card_centralizer_le_of_orderOf_eq_two hJ.orderOf_eq_two
  have hdvd : Nat.card J ∣ Nat.card C := Subgroup.card_dvd_of_le hJC
  have hpos : 0 < Nat.card C := Nat.card_pos
  rw [hc] at hdvd
  have hC24 : Nat.card C = 24 ∨ Nat.card C = 48 := by omega
  rcases hC24 with h24 | h48
  · have e1 : J = C := Subgroup.eq_of_le_of_card_ge hJC (by omega)
    have e2 : J' = C := Subgroup.eq_of_le_of_card_ge hJ'C (by omega)
    rw [e1, e2]
  · set N : Subgroup ↥C := J'.subgroupOf C with hN
    have hNc : Nat.card N = 24 := by
      rw [← hc']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ'C).toEquiv
    have hidx : N.index = 2 := by
      have := Subgroup.card_mul_index N
      rw [hNc, h48] at this
      omega
    have : N.Normal := Subgroup.normal_of_index_eq_two hidx
    have hO : classicalInvolutionOddCore J = ⊥ := by
      obtain ⟨e'⟩ := hJ.nonempty_equiv
      have hq : Nat.card (J ⧸ classicalInvolutionOddCore J) = 24 := by
        rw [Nat.card_congr e'.toEquiv, natCard_sl2Three]
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore J)
      rw [hq, hc] at hmul
      apply Subgroup.eq_bot_of_card_eq
      omega
    obtain ⟨e⟩ := hJ.nonempty_equiv_sl2 hO
    obtain ⟨S, hSJ, hS3, hJS⟩ := ModelFacts.gen3_of_equiv_sl2 (F := ZMod 3) e
    have hSJ' : ∀ s ∈ S, s ∈ J' := by
      intro s hs
      have hsC : s ∈ C := hJC (hSJ hs)
      have h1 : (⟨s, hsC⟩ : ↥C) ^ N.index ∈ N := Subgroup.pow_index_mem N _
      rw [hidx] at h1
      have h2 : s ^ 2 ∈ J' := by
        simpa [hN, Subgroup.mem_subgroupOf] using h1
      have h3 : s = (s ^ 2) ^ 2 := by
        rw [← pow_mul]
        show s = s ^ (3 + 1)
        rw [pow_succ, hS3 s hs, one_mul]
      rw [h3]
      exact pow_mem h2 2
    have hJJ' : J ≤ J' := hJS.trans ((Subgroup.closure_le J').mpr hSJ')
    exact Subgroup.eq_of_le_of_card_ge hJJ' (by omega)


theorem not_twins_of_hasM11TypeU {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (hM : Uniform.HasM11TypeU 3 1 Φ) {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    (hne : A ≠ A') {z : X} (hz : IsUniqueInvolution A z) (hz' : IsUniqueInvolution A' z) :
    False := by
  obtain ⟨-, D, hc, i, hk⟩ := hM
  have hsub : ∀ j : Fin D.card, j = i := fun j => Fin.ext (by
    have h1 := i.2
    have h2 := j.2
    omega)
  let ψ : ↥NativeSporadic.M11 →* X := Uniform.castHom hk (D.hom i)
  have hker : ψ.ker ≤ Subgroup.center ↥NativeSporadic.M11 :=
    Uniform.castHom_ker_le_center hk (D.hom i) (D.ker_le_center i)
  have key : ∀ {L : Subgroup X}, L ∈ Φ → ∃ J ∈ M11ClassicalClass, L = J.map ψ := by
    intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : i = j := (hsub j).symm
    obtain ⟨R', hR', hRR⟩ := Uniform.exists_map_castHom hk (D.hom i) hR
    exact ⟨R', hR', hLR.trans hRR.symm⟩
  have : IsSimpleGroup ↥NativeSporadic.M11 := isSimpleGroup_m11_kernel
  have hcenter : Subgroup.center ↥NativeSporadic.M11 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥NativeSporadic.M11) with
      h | h
    · exact h
    · exfalso
      obtain ⟨J, ⟨w, hw⟩, -⟩ := key hA
      exact hw.not_le_center (h ▸ le_top)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hker.trans hcenter.le)
  obtain ⟨J, ⟨w, hw⟩, rfl⟩ := key hA
  obtain ⟨J', ⟨w', hw'⟩, rfl⟩ := key hA'
  have hψ : ∀ {L : Subgroup ↥NativeSporadic.M11} {u : ↥NativeSporadic.M11} {y : X},
      IsClassicalMember3 L u → IsUniqueInvolution (L.map ψ) y → ψ u = y := by
    intro L u y hu hy
    have hmem : ψ u ∈ L.map ψ := Subgroup.mem_map_of_mem _ hu.mem
    have hsq : ψ u * ψ u = 1 := by
      rw [← map_mul]
      have h2 := pow_orderOf_eq_one u
      rw [hu.orderOf_eq_two] at h2
      rw [← sq, h2, map_one]
    rcases hy.unique _ hmem hsq with h | h
    · exact absurd (hinj (h.trans ψ.map_one.symm)) hu.ne_one
    · exact h
  have hww : w = w' := hinj ((hψ hw hz).trans (hψ hw' hz').symm)
  subst hww
  exact hne (by rw [m11_classical_eq hw hw'])

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.M11Tw
