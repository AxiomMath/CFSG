module

public import CFSG.ClassicalInvolution.Q3.M11Branch

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open scoped MatrixGroups

section SL2Three

theorem sl2Three_eq_sq_mul_sq :
    ∀ g : SL(2, ZMod 3), ∃ a b : SL(2, ZMod 3), g = a * a * (b * b) := by
  decide +kernel

theorem sl2Three_index_ne_two (H : Subgroup SL(2, ZMod 3)) : H.index ≠ 2 := by
  intro h
  have hH : H = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, b, rfl⟩ := sl2Three_eq_sq_mul_sq g
    exact H.mul_mem (Subgroup.mul_self_mem_of_index_two h a)
      (Subgroup.mul_self_mem_of_index_two h b)
  rw [hH, Subgroup.index_top] at h
  exact absurd h (by norm_num)

theorem sl2Three_no_card_twelve (H : Subgroup SL(2, ZMod 3)) : Nat.card H ≠ 12 := by
  intro h
  apply sl2Three_index_ne_two H
  have := Subgroup.card_mul_index H
  rw [h, natCard_sl2Three] at this
  omega

end SL2Three

section M11

variable {R R' : Subgroup ↥NativeSporadic.M11} {z : ↥NativeSporadic.M11}

theorem m11_member_equiv (h : Q3.IsClassicalMember3 R z) : Nonempty (R ≃* SL(2, ZMod 3)) := by
  have hc := h.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  obtain ⟨e⟩ := h.nonempty_equiv
  have hq : Nat.card (R ⧸ classicalInvolutionOddCore R) = 24 := by
    rw [Nat.card_congr e.toEquiv]
    exact natCard_sl2Three
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore R)
  rw [hq, hc] at h1
  have h2 : Nat.card (classicalInvolutionOddCore R) = 1 := by omega
  have hO : classicalInvolutionOddCore R = ⊥ := Subgroup.eq_bot_of_card_eq _ h2
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem m11_classical_eq (h : Q3.IsClassicalMember3 R z) (h' : Q3.IsClassicalMember3 R' z) :
    R = R' := by
  have hRC : R ≤ Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11) :=
    isSubnormal_le h.subnormal
  have hR'C : R' ≤ Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11) :=
    isSubnormal_le h'.subnormal
  have hC : Nat.card (Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11)) ≤ 48 :=
    Q3.card_centralizer_le_of_orderOf_eq_two h.orderOf_eq_two
  have hR : Nat.card R = 24 := h.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  have hR' : Nat.card R' = 24 := h'.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  obtain ⟨eR⟩ := m11_member_equiv h
  set C := Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11) with hCdef
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hiR : R.relIndex C * 24 = Nat.card C := by
    have := Subgroup.relIndex_mul_card R C
    rwa [inf_eq_left.mpr hRC, hR] at this
  have hiR' : R'.relIndex C * 24 = Nat.card C := by
    have := Subgroup.relIndex_mul_card R' C
    rwa [inf_eq_left.mpr hR'C, hR'] at this
  have hiI : (R ⊓ R').relIndex C * Nat.card ↥(R ⊓ R') = Nat.card C := by
    have := Subgroup.relIndex_mul_card (R ⊓ R') C
    rwa [inf_eq_left.mpr (inf_le_left.trans hRC)] at this
  have hle : (R ⊓ R').relIndex C ≤ R.relIndex C * R'.relIndex C := Subgroup.relIndex_inf_le
  have hdvd : Nat.card ↥(R ⊓ R') ∣ 24 := hR ▸ Subgroup.card_dvd_of_le inf_le_left
  have hcases : Nat.card ↥(R ⊓ R') = 12 ∨ Nat.card ↥(R ⊓ R') = 24 := by
    set a := R.relIndex C
    set r := (R ⊓ R').relIndex C
    set n := Nat.card ↥(R ⊓ R')
    have ha : R'.relIndex C = a := by omega
    rw [ha] at hle
    have ha2 : a ≤ 2 := by omega
    have ha0 : 0 < a := by omega
    have hr4 : r ≤ 4 := by nlinarith
    have hn0 : 0 < n := Nat.card_pos
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, zero_mul] at hiI
        omega
      · exact h0
    have hn24 : n ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have hn12 : 12 ≤ n := by
      interval_cases a <;> interval_cases r <;> omega
    interval_cases n <;> omega
  rcases hcases with h12 | h24
  · exfalso
    have hle' : R ⊓ R' ≤ R := inf_le_left
    have hc1 : Nat.card ((R ⊓ R').subgroupOf R) = 12 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv]
      exact h12
    have hc2 : Nat.card (((R ⊓ R').subgroupOf R).map eR.toMonoidHom) = 12 := by
      rw [Subgroup.card_map_of_injective eR.injective]
      exact hc1
    exact sl2Three_no_card_twelve _ hc2
  · have h1 : R ⊓ R' = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h24, hR])
    have hRR' : R ≤ R' := h1 ▸ inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hRR' (by rw [hR, hR'])

theorem m11_classicalClass_conj (hR : R ∈ Q3.M11ClassicalClass) (hR' : R' ∈ Q3.M11ClassicalClass) :
    ∃ g : ↥NativeSporadic.M11, R' = conjSub g R := by
  obtain ⟨z, hz⟩ := hR
  obtain ⟨z', hz'⟩ := hR'
  have hc := (Q3.isConj_m11SdZ_of_orderOf_eq_two hz.orderOf_eq_two).symm.trans
    (Q3.isConj_m11SdZ_of_orderOf_eq_two hz'.orderOf_eq_two)
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  refine ⟨g, ?_⟩
  have h1 : Q3.IsClassicalMember3 (conjSub g R) z' := by
    have := hz.map_mulEquiv (MulAut.conj g)
    rwa [MulAut.conj_apply, hg] at this
  exact (m11_classical_eq h1 hz').symm

theorem m11_singleClass :
    ∀ R ∈ Q3.CompData.m11.fund, ∀ R' ∈ Q3.CompData.m11.fund,
      ∃ g : Q3.CompData.m11.G, R' = conjSub g R :=
  fun _ hR _ hR' => m11_classicalClass_conj hR hR'

end M11

end CFSG.ClassicalInvolution.Uniform
