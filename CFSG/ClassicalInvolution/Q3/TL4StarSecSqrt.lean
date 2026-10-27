module

public import CFSG.ClassicalInvolution.Q3.TL4StarSecNbr
public import CFSG.ClassicalInvolution.AschTight.S19MInv

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

theorem quat_sq_of_central :
    ∀ x : QuaternionGroup (2 ^ (3 - 2)), (∀ y, x * y = y * x) → x * x = 1 := by
  decide

theorem natCard_quat : Nat.card (QuaternionGroup (2 ^ (3 - 2))) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem not_central_of_orderOf_eq_four (hR : TypeRFam 3 Φ) {P : Subgroup X} (hP : P ∈ RSet Φ)
    {j : X} (hj : j ∈ P) (hj4 : orderOf j = 4) : ¬ ∀ x ∈ P, j * x = x * j := by
  intro hc
  obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
  obtain ⟨e⟩ := hR.quat M hM P hPM
  have h1 : e ⟨j, hj⟩ * e ⟨j, hj⟩ = 1 := by
    refine quat_sq_of_central _ fun y => ?_
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hc y'.1 y'.2))
  rw [← map_mul, ← map_one e] at h1
  have h3 : j * j = 1 := congrArg Subtype.val (e.injective h1)
  have h4 : orderOf j ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
  rw [hj4] at h4
  norm_num at h4

omit [Finite X] in
theorem natCard_of_mem_RSet (hR : TypeRFam 3 Φ) {P : Subgroup X} (hP : P ∈ RSet Φ) :
    Nat.card P = 8 := by
  obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
  obtain ⟨e⟩ := hR.quat M hM P hPM
  rw [Nat.card_congr e.toEquiv, natCard_quat]

theorem isSylow2In_of_mem_RSet_le (hR : TypeRFam 3 Φ) {L R : Subgroup X} (hL : L ∈ Φ)
    (hRS : R ∈ RSet Φ) (hRL : R ≤ L) : IsSylow2In R L := by
  obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hRS
  refine ⟨hRL, hRM.2.1, fun V' hV'L hV'2 hRV' => ?_⟩
  obtain ⟨V, hV, hV'V⟩ := IsSylow2In.exists_ge hV'2 hV'L
  have h1 : Nat.card V = Nat.card R := hR.hyp.omega3 L hL M hM V R hV hRM
  have h2 : Nat.card V' ≤ Nat.card R := h1 ▸ Subgroup.card_le_of_le hV'V
  exact (Subgroup.eq_of_le_of_card_ge hRV' h2).symm

theorem exists_starPair_of_sqrt (hR : TypeRFam 3 Φ) {L : Subgroup X} (hL : L ∈ Φ) {z j k h : X}
    (hz : IsUniqueInvolution L z) (hj : j ∈ L) (hj4 : orderOf j = 4)
    (hk : ∀ x ∈ L, k * x = x * k) (hkk : k * k = z) (hh : h * z * h⁻¹ = j * k) :
    conjSub h L ∈ Φ ∧ L ∈ omegaStarNbr Φ (conjSub h L) ∧ L ∉ omegaNbr Φ (conjSub h L) := by
  have hΦ := hR.hyp
  have hL₀ : conjSub h L ∈ Φ := hΦ.conjInvariant h L hL
  have hd₀ : IsUniqueInvolution (conjSub h L) (j * k) := hh ▸ hz.conj h
  have hjk : j * k = k * j := (hk j hj).symm
  have hj2 : IsPGroup 2 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hj4]; norm_num)
  obtain ⟨P, hP, hjP⟩ := IsSylow2In.exists_ge hj2 (Subgroup.zpowers_le.mpr hj)
  have hPR : P ∈ RSet Φ := mem_RSet_of_isSylow2In hL hP
  have hjP' : j ∈ P := hjP (Subgroup.mem_zpowers j)
  have hne : L ≠ conjSub h L := by
    intro he
    have h1 : z = j * k := hz.eq (he ▸ hd₀)
    have h2 : j = k := by
      have h3 : j * k = k * k := h1.symm.trans hkk.symm
      exact mul_right_cancel h3
    refine not_central_of_orderOf_eq_four hR hPR hjP' hj4 fun x hx => ?_
    rw [h2]
    exact hk x (hP.1 hx)
  refine ⟨hL₀, ⟨hL, hne, Subgroup.zpowers j, ⟨P, hPR, hjP, inferInstance, ?_⟩,
    Subgroup.zpowers_le.mpr hj, ?_⟩, ?_⟩
  ·
    have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers j) P
    rw [inf_eq_left.mpr hjP, Nat.card_zpowers, hj4, natCard_of_mem_RSet hR hPR] at h1
    omega
  ·
    refine Subgroup.zpowers_le.mpr (hR.tight _ hL₀ _ hd₀ ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc j * (j * k) = j * (k * j) := by rw [hjk]
      _ = j * k * j := by group
  ·
    rintro ⟨-, -, R, hRS, hRL, hRN⟩
    have hRL' := isSylow2In_of_mem_RSet_le hR hL hRS hRL
    have hc : ∀ x ∈ R, j * x = x * j := by
      intro x hx
      have hxd : x * (j * k) * x⁻¹ = j * k := hd₀.conj_eq (conjSub_eq_of_mem_normalizer (hRN hx))
      have hxk : k * x = x * k := hk x (hRL hx)
      have e1 : x * j * x⁻¹ = j := by
        calc x * j * x⁻¹ = x * (j * k) * x⁻¹ * (x * k * x⁻¹)⁻¹ := by group
          _ = j * k * (k * x * x⁻¹)⁻¹ := by rw [hxd, hxk]
          _ = j := by group
      calc j * x = (x * j * x⁻¹) * x := by rw [e1]
        _ = x * j := by group
    have hN : Subgroup.zpowers j ≤ Subgroup.normalizer (R : Set X) := by
      refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (R : Set X) ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hc x hx).symm
    have h2 : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers j) := hRL'.2.1.to_sup_of_normal_left' hj2 hN
    have h3 := hRL'.2.2 _ (sup_le hRL (Subgroup.zpowers_le.mpr hj)) h2 le_sup_left
    have hjR : j ∈ R := h3 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers j)
    exact not_central_of_orderOf_eq_four hR hRS hjR hj4 hc

theorem starNbr_of_sqrt (hR : TypeRFam 3 Φ) (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    {L : Subgroup X} (hL : L ∈ Φ) {z j k h : X} (hz : IsUniqueInvolution L z) (hj : j ∈ L)
    (hj4 : orderOf j = 4) (hk : ∀ x ∈ L, k * x = x * k) (hkk : k * k = z)
    (hh : h * z * h⁻¹ = j * k) :
    ∀ L' ∈ Φ, ∃ L'' ∈ Φ, L'' ∈ omegaStarNbr Φ L' ∧ L'' ∉ omegaNbr Φ L' := by
  obtain ⟨hL₀, hs, hn⟩ := exists_starPair_of_sqrt hR hL hz hj hj4 hk hkk hh
  exact starNbr_of_exists hR.hyp.conjInvariant htr ⟨_, hL₀, L, hs, hn⟩

theorem starNbr_of_sqrt_involutionsConj (hR : TypeRFam 3 Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (hconj : CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.InvolutionsConj X)
    {L : Subgroup X} (hL : L ∈ Φ) {z k : X} (hz : IsUniqueInvolution L z)
    (hk : ∀ x ∈ L, k * x = x * k) (hkk : k * k = z) :
    ∀ L' ∈ Φ, ∃ L'' ∈ Φ, L'' ∈ omegaStarNbr Φ L' ∧ L'' ∉ omegaNbr Φ L' := by
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := L) (T := ⊥) IsPGroup.of_bot bot_le
  have hPR : P ∈ RSet Φ := mem_RSet_of_isSylow2In hL hP
  obtain ⟨e⟩ := hR.quat L hL P hP
  set j : X := (e.symm (QuaternionGroup.xa 0) : X) with hjdef
  have hjP : j ∈ P := (e.symm (QuaternionGroup.xa 0)).2
  have hj4 : orderOf j = 4 := by
    rw [hjdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]
  have hj : j ∈ L := hP.1 hjP
  have hjk : j * k = k * j := (hk j hj).symm
  have hjj : j * j = z := by
    have h1 : (j * j) * (j * j) = 1 := by
      have h4 : j ^ 4 = 1 := hj4 ▸ pow_orderOf_eq_one j
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at h4
      exact h4
    have h2 : j * j ≠ 1 := by
      intro h
      have h4 : orderOf j ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hj4] at h4
      norm_num at h4
    exact (hz.unique _ (L.mul_mem hj hj) h1).resolve_left h2
  have hd2 : (j * k) * (j * k) = 1 := by
    calc (j * k) * (j * k) = j * (k * j) * k := by group
      _ = j * (j * k) * k := by rw [hjk]
      _ = (j * j) * (k * k) := by group
      _ = 1 := by rw [hjj, hkk, hz.sq]
  have hd1 : j * k ≠ 1 := by
    intro h
    have hkj : k = j⁻¹ := eq_inv_of_mul_eq_one_right h
    refine not_central_of_orderOf_eq_four hR hPR hjP hj4 fun x hx => ?_
    have h1 := hk x (hP.1 hx)
    rw [hkj] at h1
    calc j * x = j * (x * j⁻¹) * j := by group
      _ = j * (j⁻¹ * x) * j := by rw [h1]
      _ = x * j := by group
  obtain ⟨h, hh⟩ := hconj z (j * k) hz.sq hd2 hz.ne_one hd1
  exact starNbr_of_sqrt hR htr hL hz hj hj4 hk hkk hh

end CFSG.ClassicalInvolution.Q3.TL4
