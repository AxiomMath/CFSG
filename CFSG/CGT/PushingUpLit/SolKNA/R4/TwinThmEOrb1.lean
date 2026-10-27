module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf23Orb4Shape

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

namespace ThmE

section Orb1


variable {G : Type} [Group G]

theorem orb4_rset_ne_of_ne [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {K J R R' : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : R ∈ RSet Ω)
    (hRK : R ≤ K) (hR'J : R' ≤ J) : R ≠ R' := by
  intro h
  subst h
  have hR2 : IsPGroup 2 R := by
    obtain ⟨J', -, -, h2, -⟩ := mem_RSet_iff.mp hR
    exact h2
  have h1 := hΩ.card_le_two_of_le_inf hK hJ hKJ hR2 hRK hR'J
  have h8 := hΩ.eight_le_of_mem_RSet hR
  omega

theorem orb4_noncentral {R : Subgroup G} (hR : IsQuatSub R) {u : G} (hu : u ∈ R)
    (hu4 : orderOf u = 4) : ∃ r ∈ R, u * r ≠ r * u := by
  by_contra hcon
  push Not at hcon
  exact TwinThmEW.orb4_sq_ne_one_of_orderOf_eq_four hu4 (hR.sq_eq_one_of_central hu hcon)

theorem orb4_cent_of_sq {K : Subgroup G} {z u y : G} (hz : IsUniqueInvolution K z) (hu : u ∈ K)
    (hu2 : u * u = z) (hy : y ∈ K) (hyu : y * u = u * y) (hy4 : (y * y) * (y * y) = 1) :
    y = 1 ∨ y = u ∨ y = u * u ∨ y = u * u * u := by
  rcases hz.unique (y * y) (K.mul_mem hy hy) hy4 with h1 | h1
  · rcases hz.unique y hy h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl (h2.trans hu2.symm)))
  · have hc : Commute y u⁻¹ := (show Commute y u from hyu).inv_right
    have hv : (y * u⁻¹) * (y * u⁻¹) = 1 := by
      calc (y * u⁻¹) * (y * u⁻¹) = y * (u⁻¹ * y) * u⁻¹ := by group
        _ = y * (y * u⁻¹) * u⁻¹ := by rw [← hc.eq]
        _ = (y * y) * (u⁻¹ * u⁻¹) := by group
        _ = 1 := by rw [h1, ← hu2]; group
    rcases hz.unique (y * u⁻¹) (K.mul_mem hy (K.inv_mem hu)) hv with h2 | h2
    · exact Or.inr (Or.inl (mul_inv_eq_one.mp h2))
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc y = (y * u⁻¹) * u := by group
        _ = z * u := by rw [h2]
        _ = u * u * u := by rw [← hu2]

theorem orb4_commute_AD [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G)
    {Ka Kb Ra Rb : Subgroup G} (hKa : Ka ∈ Ω) (hKb : Kb ∈ Ω) (hKab : Ka ≠ Kb)
    (hRa : Ra ∈ RSet Ω) (hRb : Rb ∈ RSet Ω) (hRaK : Ra ≤ Ka) (hRbK : Rb ≤ Kb)
    (hRaS : Ra ≤ (S : Subgroup G)) (hRbS : Rb ≤ (S : Subgroup G)) {u u' z : G}
    (hza : IsUniqueInvolution Ka z) (hzb : IsUniqueInvolution Kb z)
    (hua : u ∈ Ra) (hu4 : orderOf u = 4) (hub : u' ∈ Rb) (hu'4 : orderOf u' = 4)
    (hz : u * u = z) (hz' : u' * u' = z) {w : G} (hwP : w ∈ Ra ⊔ Rb) (hwu : w * u = u * w)
    (hwu' : w * u' = u' * w) (hww : w * w = 1) :
    w = 1 ∨ w = z ∨ w = u * u' ∨ w = z * (u * u') := by
  have hne : Ra ≠ Rb := orb4_rset_ne_of_ne hΩ hKa hKb hKab hRa hRaK hRbK
  have hcomm : Commutes Ra Rb := TwinThmEW.orb4_rset_commutes hΩ S hRa hRb hRaS hRbS hne
  obtain ⟨y, hy, y', hy', rfl⟩ := exists_mul_of_mem_sup_of_commutes hcomm hwP
  have hyu : y * u = u * y := by
    have h2 : u * y' = y' * u := hcomm u hua y' hy'
    have : (y * u) * y' = (u * y) * y' := by
      calc (y * u) * y' = y * (u * y') := by group
        _ = y * (y' * u) := by rw [h2]
        _ = y * y' * u := by group
        _ = u * (y * y') := hwu
        _ = (u * y) * y' := by group
    exact mul_right_cancel this
  have hyu' : y' * u' = u' * y' := by
    have h2 : y * u' = u' * y := hcomm y hy u' hub
    have : y * (y' * u') = y * (u' * y') := by
      calc y * (y' * u') = y * y' * u' := by group
        _ = u' * (y * y') := hwu'
        _ = (u' * y) * y' := by group
        _ = (y * u') * y' := by rw [h2]
        _ = y * (u' * y') := by group
    exact mul_left_cancel this
  have hz2 : z * z = 1 := TwinThmEW.orb4_four_pow_eq hu4 hz
  have hz1 : z ≠ 1 := by rw [← hz]; exact TwinThmEW.orb4_sq_ne_one_of_orderOf_eq_four hu4
  have hyy' : y * y' = y' * y := hcomm y hy y' hy'
  have hsq : (y * y) * (y' * y') = 1 := by
    calc (y * y) * (y' * y') = y * (y * y') * y' := by group
      _ = y * (y' * y) * y' := by rw [hyy']
      _ = (y * y') * (y * y') := by group
      _ = 1 := hww
  have hRa2 : IsPGroup 2 Ra := by
    obtain ⟨J, -, -, h2, -⟩ := mem_RSet_iff.mp hRa
    exact h2
  have hs_a : y * y ∈ Ra := Ra.mul_mem hy hy
  have hs_b : y * y ∈ Rb := by
    have : y * y = (y' * y')⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact Rb.inv_mem (Rb.mul_mem hy' hy')
  have hcard : Nat.card (Subgroup.zpowers (y * y)) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hKa hKb hKab (hRa2.to_le (Subgroup.zpowers_le.mpr hs_a))
      (Subgroup.zpowers_le.mpr (hRaK hs_a)) (Subgroup.zpowers_le.mpr (hRbK hs_b))
  have hs2 : (y * y) * (y * y) = 1 := by
    rw [Nat.card_zpowers] at hcard
    have hpos : 0 < orderOf (y * y) := orderOf_pos _
    have hpow := pow_orderOf_eq_one (y * y)
    interval_cases h : orderOf (y * y)
    · rw [pow_one] at hpow
      rw [hpow, one_mul]
    · rwa [pow_two] at hpow
  have hs2' : (y' * y') * (y' * y') = 1 := by
    have : y' * y' = (y * y)⁻¹ := eq_inv_of_mul_eq_one_right hsq
    rw [this]
    calc (y * y)⁻¹ * (y * y)⁻¹ = ((y * y) * (y * y))⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hyc := orb4_cent_of_sq hza (hRaK hua) hz (hRaK hy) hyu hs2
  have hyc' := orb4_cent_of_sq hzb (hRbK hub) hz' (hRbK hy') hyu' hs2'
  exact TwinThmEW.orb4_d4_cases (hcomm u hua u' hub) hz hz' hz2 hz1 hyc hyc' hww

theorem orb4_center_pair' {Ka Kb Ra Rb : Subgroup G} (hcomm : Commutes Ra Rb)
    (hqa : IsQuatSub Ra) (hqb : IsQuatSub Rb) (hRaK : Ra ≤ Ka) (hRbK : Rb ≤ Kb) {z : G}
    (hza : IsUniqueInvolution Ka z) (hzb : IsUniqueInvolution Kb z) (hz2 : z * z = 1) {v : G}
    (hv : v ∈ Ra ⊔ Rb) (hva : ∀ r ∈ Ra, r * v = v * r) (hvb : ∀ r ∈ Rb, r * v = v * r) :
    v = 1 ∨ v = z := by
  obtain ⟨y, hy, y', hy', rfl⟩ := exists_mul_of_mem_sup_of_commutes hcomm hv
  have hyc : ∀ r ∈ Ra, y * r = r * y := by
    intro r hr
    have h1 := hva r hr
    have h2 : r * y' = y' * r := hcomm r hr y' hy'
    have : (r * y) * y' = (y * r) * y' := by
      calc (r * y) * y' = r * (y * y') := by group
        _ = (y * y') * r := h1
        _ = y * (y' * r) := by group
        _ = y * (r * y') := by rw [h2]
        _ = (y * r) * y' := by group
    exact (mul_right_cancel this).symm
  have hyc' : ∀ r ∈ Rb, y' * r = r * y' := by
    intro r hr
    have h1 := hvb r hr
    have h2 : y * r = r * y := hcomm y hy r hr
    have : y * (r * y') = y * (y' * r) := by
      calc y * (r * y') = (y * r) * y' := by group
        _ = (r * y) * y' := by rw [h2]
        _ = r * (y * y') := by group
        _ = (y * y') * r := h1
        _ = y * (y' * r) := by group
    exact (mul_left_cancel this).symm
  have h1 := hza.unique y (hRaK hy) (hqa.sq_eq_one_of_central hy hyc)
  have h2 := hzb.unique y' (hRbK hy') (hqb.sq_eq_one_of_central hy' hyc')
  rcases h1 with h | h <;> rcases h2 with h' | h'
  · left; rw [h, h', one_mul]
  · right; rw [h, h', one_mul]
  · right; rw [h, h', mul_one]
  · left; rw [h, h']; exact hz2

theorem orb4_not_all_commute' {R : Subgroup G} (hR : IsQuatSub R) {v a b : G} (hv : v ∈ R)
    (hv4 : orderOf v = 4) (ha : ∀ r ∈ R, r * a = a * r) (hb : ∀ r ∈ R, r * b = b * r) :
    ¬ ∀ r ∈ R, r * (a * v * b) = (a * v * b) * r := by
  intro hall
  obtain ⟨r, hrR, hr⟩ := orb4_noncentral hR hv hv4
  apply hr
  have h1 : Commute r (a * v * b) := hall r hrR
  have hra : Commute r a := ha r hrR
  have hrb : Commute r b := hb r hrR
  have h2 : Commute r (a * v) := by
    have : a * v = (a * v * b) * b⁻¹ := by group
    rw [this]
    exact h1.mul_right hrb.inv_right
  have h3 : Commute r v := by
    have : v = a⁻¹ * (a * v) := by group
    rw [this]
    exact hra.inv_right.mul_right h2
  exact h3.eq.symm


theorem shape_commute' [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G)
    {W : Subgroup G} (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {Ka Kb Ra Rb : Subgroup G} (hKa : Ka ∈ Ω) (hKb : Kb ∈ Ω) (hKab : Ka ≠ Kb)
    (hRa : Ra ∈ RSet Ω) (hRb : Rb ∈ RSet Ω) (hRaK : Ra ≤ Ka) (hRbK : Rb ≤ Kb)
    (hRaS : Ra ≤ (S : Subgroup G)) (hRbS : Rb ≤ (S : Subgroup G)) {u u' z : G}
    (hza : IsUniqueInvolution Ka z) (hzb : IsUniqueInvolution Kb z)
    (hua : u ∈ Ra) (huW : u ∈ W) (hu4 : orderOf u = 4) (hub : u' ∈ Rb) (hu'W : u' ∈ W)
    (hu'4 : orderOf u' = 4) (hz : u * u = z) (hz' : u' * u' = z) (t : G) :
    TwinThmEW.D4Shape (S : Subgroup G) t z (u * u') := by
  have hne : Ra ≠ Rb := orb4_rset_ne_of_ne hΩ hKa hKb hKab hRa hRaK hRbK
  have hcomm : Commutes Ra Rb := TwinThmEW.orb4_rset_commutes hΩ S hRa hRb hRaS hRbS hne
  refine ⟨(Ra ⊔ Rb) ⊓ W, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hz]
      exact Subgroup.mem_sup_left (Ra.mul_mem hua hua)
    · rw [← hz]
      exact W.mul_mem huW huW
  · exact Subgroup.mem_inf.mpr ⟨(Ra ⊔ Rb).mul_mem (Subgroup.mem_sup_left hua)
      (Subgroup.mem_sup_right hub), W.mul_mem huW hu'W⟩
  · intro c hc hct hcd
    have hsupp : ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → (R ∈ ({Ra, Rb} : Set (Subgroup G)) ↔
        ¬ ∀ r ∈ R, r * (u * u') = (u * u') * r) := by
      intro R hR hRS
      constructor
      · rintro (rfl | rfl)
        · have := orb4_not_all_commute' (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRa) (v := u) (a := 1) (b := u') hua hu4
            (fun r _ => by simp) (fun r hr => hcomm r hr u' hub)
          simpa using this
        · have := orb4_not_all_commute' (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRb) (v := u') (a := u) (b := 1) hub hu'4
            (fun r hr => (hcomm u hua r hr).symm) (fun r _ => by simp)
          simpa using this
      · intro hnot
        by_contra hR'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hR'
        apply hnot
        have hRa' := TwinThmEW.orb4_rset_commutes hΩ S hR hRa hRS hRaS hR'.1
        have hRb' := TwinThmEW.orb4_rset_commutes hΩ S hR hRb hRS hRbS hR'.2
        intro r hr
        exact ((show Commute r u from hRa' r hr u hua).mul_right
          (show Commute r u' from hRb' r hr u' hub)).eq
    have hP : conjSub c (Ra ⊔ Rb) = Ra ⊔ Rb := by
      have := TwinThmEW.orb4_conjSub_sSup_eq (𝒮 := {Ra, Rb}) (d := u * u') hΩ (S := (S : Subgroup G))
        (by
          rintro R (rfl | rfl)
          · exact ⟨hRa, hRaS⟩
          · exact ⟨hRb, hRbS⟩) hsupp hc hcd
      rwa [sSup_pair] at this
    rw [TwinThmEW.orb4_conjSub_inf, hP, hWn c hc]
  · intro w hw hww _
    exact orb4_commute_AD hΩ S hKa hKb hKab hRa hRb hRaK hRbK hRaS hRbS hza hzb hua hu4 hub hu'4 hz hz'
      (Subgroup.mem_inf.mp hw).1 (hWab _ (Subgroup.mem_inf.mp hw).2 u huW)
      (hWab _ (Subgroup.mem_inf.mp hw).2 u' hu'W) hww

end Orb1

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
