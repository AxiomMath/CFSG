module

public import CFSG.CharacterTheory.Wreathed.CentralProduct
public import CFSG.GH74.GLS.Bg.Local.Lemma1621

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem two_smul_eq_zero_half_quarter (l : ℕ) (hl : 0 < l) (c : ZMod (4 * l)) :
    2 • c = 0 ↔ c = 0 ∨ c = (2 * l : ℕ) := by
  let : NeZero (4 * l) := ⟨by omega⟩
  have hlt := ZMod.val_lt c
  have heq : 2 • c = ((2 * c.val : ℕ) : ZMod (4 * l)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  have hdiv (t : ℕ) : 4 * l ∣ 2 * t ↔ 2 * l ∣ t := by
    rw [show 4 * l = 2 * (2 * l) by omega,
      Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))]
  rw [heq, ZMod.natCast_eq_zero_iff, hdiv c.val]
  constructor
  · rintro ⟨k, hk⟩
    have hklt : k < 2 := by nlinarith
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · left
      have hz : c.val = 0 := by simpa using hk
      rw [← ZMod.natCast_zmod_val c, hz, Nat.cast_zero]
    · right
      have hz : c.val = 2 * l := by simpa using hk
      rw [← ZMod.natCast_zmod_val c, hz]
  · rintro (rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by omega)]

theorem quaternionEight_noncentral_square (q : QuaternionGroup 2)
    (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) : q ^ 2 = QuaternionGroup.a 2 :=
  (show ∀ q : QuaternionGroup 2,
    q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 → q ^ 2 = QuaternionGroup.a 2 by decide) q hq

theorem quaternionEight_noncentral_order (q : QuaternionGroup 2)
    (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) : orderOf q = 4 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hs := quaternionEight_noncentral_square q hq
  have hn : q ^ 2 ≠ 1 := by
    rw [hs]
    decide
  have hf : q ^ 4 = 1 := by
    calc q ^ 4 = (q ^ 2) ^ 2 := by rw [← pow_mul]
         _ = (QuaternionGroup.a 2) ^ 2 := by rw [hs]
         _ = 1 := by decide
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hn hf



private theorem quaternion_mem_center_iff (q : QuaternionGroup 2) :
    q ∈ Subgroup.center (QuaternionGroup 2) ↔
      q = 1 ∨ q = QuaternionGroup.a 2 := by
  rw [Subgroup.mem_center_iff]
  exact (show ∀ q : QuaternionGroup 2,
    (∀ h : QuaternionGroup 2, h * q = q * h) ↔
      q = 1 ∨ q = QuaternionGroup.a 2 by decide) q

private theorem card_center_quaternionGroup_two :
    Nat.card (Subgroup.center (QuaternionGroup 2)) = 2 := by
  have h : ∀ g : QuaternionGroup 2,
      (∀ h, g * h = h * g) ↔ (g = 1 ∨ g = QuaternionGroup.a 2) := by decide
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, one_mem _⟩, ⟨QuaternionGroup.a 2, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact ((h (QuaternionGroup.a 2)).2 (Or.inr rfl) g).symm
  · intro hh
    have h2 : (1 : QuaternionGroup 2) ≠ QuaternionGroup.a 2 := by decide
    exact h2 (congrArg Subtype.val hh)
  · ext ⟨g, hg⟩
    rw [Subgroup.mem_center_iff] at hg
    have := (h g).1 (fun k => (hg k).symm)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases this with rfl | rfl
    · left; rfl
    · right; rfl

private theorem quaternion_a_two_mem_center :
    (QuaternionGroup.a 2 : QuaternionGroup 2) ∈
      Subgroup.center (QuaternionGroup 2) :=
  (quaternion_mem_center_iff _).2 (Or.inr rfl)

private theorem mem_center_iff_map_mem_center
    {P : Type*} [Group P] {A : Subgroup P}
    (eA : A ≃* QuaternionGroup 2) (a : A) :
    a ∈ Subgroup.center A ↔ eA a ∈ Subgroup.center (QuaternionGroup 2) := by
  constructor
  · intro ha
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨a', rfl⟩ := eA.surjective q
    simpa only [map_mul] using congrArg eA (Subgroup.mem_center_iff.mp ha a')
  · intro ha
    rw [Subgroup.mem_center_iff]
    intro a'
    apply eA.injective
    simpa only [map_mul] using Subgroup.mem_center_iff.mp ha (eA a')

private theorem mem_inf_of_mem_center_quaternion
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card ↥(A ⊓ B) = 2)
    (eA : A ≃* QuaternionGroup 2)
    (a : A) (ha : a ∈ Subgroup.center A) : (a : P) ∈ A ⊓ B := by
  classical
  have hZcard : Nat.card (Subgroup.center A) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr eA).toEquiv]
    exact card_center_quaternionGroup_two
  have hle : (A ⊓ B).subgroupOf A ≤ Subgroup.center A := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 x hx.2)
  have hcard' : Nat.card ((A ⊓ B).subgroupOf A) = 2 := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv]
    exact hcard
  have heq : (A ⊓ B).subgroupOf A = Subgroup.center A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, hcard'])
  rw [← heq, Subgroup.mem_subgroupOf] at ha
  exact ha

private theorem normal_left_of_commuting_centralProduct
    {P : Type*} [Group P] {A B : Subgroup P}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = ⊤) : A.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
  apply sup_le
  · exact A.le_normalizer
  · rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have h : b * a * b⁻¹ = a := by
      rw [← hcomm a ha b hb]
      group
    rwa [h]

theorem center_eq_right_of_quaternion_centralProduct
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (eA : A ≃* QuaternionGroup 2)
    (hBcyc : IsCyclic B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = ⊤)
    (hinf : Nat.card ↥(A ⊓ B) = 2) :
    Subgroup.center P = B := by
  classical
  have hA : A.Normal := normal_left_of_commuting_centralProduct hcomm hsup
  apply le_antisymm
  · intro x hx
    have hxsup : x ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top x
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (@Subgroup.mem_sup_of_normal_left P _ A B hA x).mp hxsup
    have hacent : (⟨a, ha⟩ : A) ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro a'
      have h := Subgroup.mem_center_iff.mp hx (a' : P)
      have h' : (a' : P) * a * b = a * (a' : P) * b := by
        calc (a' : P) * a * b = (a' : P) * (a * b) := by group
          _ = (a * b) * (a' : P) := h
          _ = a * (b * (a' : P)) := by group
          _ = a * ((a' : P) * b) := by rw [hcomm (a' : P) a'.2 b hb]
          _ = a * (a' : P) * b := by group
      exact Subtype.ext (mul_right_cancel h')
    have haAB := mem_inf_of_mem_center_quaternion hcomm hinf eA ⟨a, ha⟩ hacent
    exact B.mul_mem haAB.2 hb
  · intro b hb
    rw [Subgroup.mem_center_iff]
    intro p
    have hpsup : p ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top p
    obtain ⟨a, ha, b', hb', rfl⟩ :=
      (@Subgroup.mem_sup_of_normal_left P _ A B hA p).mp hpsup
    have hBcomm : IsMulCommutative B := @IsCyclic.isMulCommutative B _ hBcyc
    have hbb' : b' * b = b * b' := by
      exact congrArg Subtype.val
        (hBcomm.is_comm.comm (⟨b', hb'⟩ : B) (⟨b, hb⟩ : B))
    calc (a * b') * b = a * (b' * b) := by group
      _ = a * (b * b') := by rw [hbb']
      _ = (a * b) * b' := by group
      _ = (b * a) * b' := by rw [hcomm a ha b hb]
      _ = b * (a * b') := by group

private theorem orderOf_eq_four_of_mem_quaternion_not_center
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (eA : A ≃* QuaternionGroup 2)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : Nat.card ↥(A ⊓ B) = 2)
    (hcenter : Subgroup.center P = B)
    {a : P} (ha : a ∈ A) (haC : a ∉ Subgroup.center P) :
    orderOf a = 4 := by
  let aA : A := ⟨a, ha⟩
  have haAcenter : aA ∉ Subgroup.center A := by
    intro hc
    exact haC (hcenter.symm.le (mem_inf_of_mem_center_quaternion hcomm hinf eA aA hc).2)
  have hqnc : eA aA ∉ Subgroup.center (QuaternionGroup 2) := by
    intro hq
    exact haAcenter ((mem_center_iff_map_mem_center eA aA).2 hq)
  have hqpair : eA aA ≠ 1 ∧ eA aA ≠ QuaternionGroup.a 2 := by
    constructor
    · intro h
      exact hqnc ((quaternion_mem_center_iff _).2 (Or.inl h))
    · intro h
      exact hqnc ((quaternion_mem_center_iff _).2 (Or.inr h))
  have hqord := quaternionEight_noncentral_order (eA aA) hqpair
  have horderA : orderOf aA = orderOf a := (Subgroup.orderOf_coe aA).symm
  have hmaporder : orderOf (eA aA) = orderOf aA :=
    orderOf_injective (eA : A →* QuaternionGroup 2) eA.injective aA
  rw [← horderA, ← hmaporder]
  exact hqord

private theorem eq_of_orderOf_eq_two_of_isCyclic
    {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {a b : Z} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; norm_num at hb
  exact CFSG.GH74.GLS.Bg.L1621.cyclic_invol_unique ha2 hb2 ha1 hb1

private theorem mem_quaternion_of_orderOf_eq_four
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (eA : A ≃* QuaternionGroup 2)
    (hBcyc : IsCyclic B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = ⊤)
    (hinf : Nat.card ↥(A ⊓ B) = 2)
    (hcenter : Subgroup.center P = B)
    {x : P} (hxcenter : x ∉ Subgroup.center P) (hx4 : orderOf x = 4) :
    x ∈ A := by
  classical
  have hA : A.Normal := normal_left_of_commuting_centralProduct hcomm hsup
  let zA : A := eA.symm (QuaternionGroup.a 2)
  let zP : P := zA
  have hzAcenter : zA ∈ Subgroup.center A :=
    (mem_center_iff_map_mem_center eA zA).2 (by
      simpa [zA] using quaternion_a_two_mem_center)
  have hzAB : zP ∈ A ⊓ B :=
    mem_inf_of_mem_center_quaternion hcomm hinf eA zA hzAcenter
  have hzB : zP ∈ B := hzAB.2
  have hzPcenter : zP ∈ Subgroup.center P := hcenter.symm.le hzB
  have hzA_sq : zA ^ 2 = 1 := by
    have h2 : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide
    change (eA.symm (QuaternionGroup.a 2)) ^ 2 = 1
    rw [← map_pow, h2, map_one]
  have hzP_sq : zP * zP = 1 := by
    have := congrArg (fun y : A => (y : P)) hzA_sq
    simpa [zP, pow_two] using this
  have hzA_ne : zA ≠ 1 := by
    intro h
    have hq : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by
      calc (QuaternionGroup.a 2 : QuaternionGroup 2) = eA zA := by simp [zA]
        _ = eA 1 := by rw [h]
        _ = 1 := map_one eA
    exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) hq
  have hzP_ne : zP ≠ 1 := by
    intro h
    exact hzA_ne (Subtype.ext (by simpa [zP] using h))
  have hzP_order : orderOf zP = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hzP_sq) hzP_ne
  have hxsup : x ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top x
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (@Subgroup.mem_sup_of_normal_left P _ A B hA x).mp hxsup
  have hxcenter' : a * b ∉ Subgroup.center P := hxcenter
  have haAcenter : (⟨a, ha⟩ : A) ∉ Subgroup.center A := by
    intro hc
    have haB : a ∈ B :=
      (mem_inf_of_mem_center_quaternion hcomm hinf eA ⟨a, ha⟩ hc).2
    exact hxcenter' (hcenter.symm.le (B.mul_mem haB hb))
  have hqnc : eA (⟨a, ha⟩ : A) ∉ Subgroup.center (QuaternionGroup 2) := by
    intro hq
    exact haAcenter ((mem_center_iff_map_mem_center eA ⟨a, ha⟩).2 hq)
  have hqpair : eA (⟨a, ha⟩ : A) ≠ 1 ∧
      eA (⟨a, ha⟩ : A) ≠ QuaternionGroup.a 2 := by
    constructor
    · intro h
      exact hqnc ((quaternion_mem_center_iff _).2 (Or.inl h))
    · intro h
      exact hqnc ((quaternion_mem_center_iff _).2 (Or.inr h))
  have hsqA : ((⟨a, ha⟩ : A) ^ 2) = zA := by
    apply eA.injective
    rw [map_pow, quaternionEight_noncentral_square (eA (⟨a, ha⟩ : A)) hqpair]
    simp [zA]
  have ha_sq : a ^ 2 = zP := by
    have := congrArg (fun y : A => (y : P)) hsqA
    simpa [zP, Subgroup.coe_pow] using this
  have hx2eq : (a * b) ^ 2 = zP * b ^ 2 := by
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow, ha_sq]
  have hx2ne : (a * b) ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hx4] at hdvd
    norm_num at hdvd
  have hx2sq : ((a * b) ^ 2) ^ 2 = 1 := by
    calc ((a * b) ^ 2) ^ 2 = (a * b) ^ (2 * 2) := by rw [pow_mul]
      _ = (a * b) ^ 4 := by norm_num
      _ = 1 := by simpa [hx4] using pow_orderOf_eq_one (a * b)
  have hb4 : (b ^ 2) ^ 2 = 1 := by
    have hcalc := hx2sq
    rw [hx2eq] at hcalc
    have hzc : Commute zP (b ^ 2) := by
      exact (Subgroup.mem_center_iff.mp hzPcenter (b ^ 2)).symm
    have hzP_sq' : zP ^ 2 = 1 := by simpa [pow_two] using hzP_sq
    rw [hzc.mul_pow, hzP_sq', one_mul] at hcalc
    exact hcalc
  have hb2 : b ^ 2 = 1 := by
    by_contra hb2ne
    have hb2ord : orderOf (⟨b ^ 2, B.pow_mem hb 2⟩ : B) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hb4 hb2ne
    have hzord : orderOf (⟨zP, hzB⟩ : B) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hzP_order
    have hb2eq : b ^ 2 = zP :=
      congrArg Subtype.val
        (@eq_of_orderOf_eq_two_of_isCyclic B _ _ hBcyc _ _ hb2ord hzord)
    exact hx2ne (by rw [hx2eq, hb2eq, hzP_sq])
  have hbA : b ∈ A := by
    by_cases hb1 : b = 1
    · simp [hb1]
    · have hbord : orderOf (⟨b, hb⟩ : B) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_eq_prime (by simpa [pow_two] using hb2) hb1
      have hzord : orderOf (⟨zP, hzB⟩ : B) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact hzP_order
      have hb_eq : b = zP :=
        congrArg Subtype.val
          (@eq_of_orderOf_eq_two_of_isCyclic B _ _ hBcyc _ _ hbord hzord)
      rw [hb_eq]
      exact zA.2
  exact A.mul_mem ha hbA


private theorem quaternion_eq_intrinsic_closure_of_centralProduct
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (eA : A ≃* QuaternionGroup 2)
    (hBcyc : IsCyclic B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = ⊤)
    (hinf : Nat.card ↥(A ⊓ B) = 2)
    (hcenter : Subgroup.center P = B) :
    A = Subgroup.closure
      {x : P | x ∉ Subgroup.center P ∧ orderOf x = 4} := by
  classical
  let H := Subgroup.closure
    {x : P | x ∉ Subgroup.center P ∧ orderOf x = 4}
  have hHA : H ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    exact mem_quaternion_of_orderOf_eq_four eA hBcyc hcomm hsup hinf hcenter hx.1 hx.2
  have hAH : A ≤ H := by
    intro g hg
    set q : QuaternionGroup 2 := eA ⟨g, hg⟩
    have hgq : eA.symm q = ⟨g, hg⟩ := by simp [q]
    change ((⟨g, hg⟩ : A) : P) ∈ H
    rw [← hgq]
    have hgen (r : QuaternionGroup 2)
        (hr : r ≠ 1 ∧ r ≠ QuaternionGroup.a 2) :
        ((eA.symm r : A) : P) ∈ H := by
      have hnoncenter : ((eA.symm r : A) : P) ∉ Subgroup.center P := by
        intro hcP
        have hcB : ((eA.symm r : A) : P) ∈ B := hcenter.le hcP
        have hcA : eA.symm r ∈ Subgroup.center A := by
          rw [Subgroup.mem_center_iff]
          intro a'
          exact Subtype.ext (hcomm a' a'.2 ((eA.symm r : A) : P) hcB)
        have hqcenter : r ∈ Subgroup.center (QuaternionGroup 2) := by
          have := (mem_center_iff_map_mem_center eA (eA.symm r)).mp hcA
          simpa using this
        rcases (quaternion_mem_center_iff r).1 hqcenter with h | h
        · exact hr.1 h
        · exact hr.2 h
      apply Subgroup.subset_closure
      refine ⟨hnoncenter, ?_⟩
      exact orderOf_eq_four_of_mem_quaternion_not_center eA hcomm hinf hcenter
        (eA.symm r).2 hnoncenter
    have hr : ((eA.symm (QuaternionGroup.a 1) : A) : P) ∈ H := hgen _ (by decide)
    have hd : ((eA.symm (QuaternionGroup.xa 0) : A) : P) ∈ H := hgen _ (by decide)
    have hrot (i : ZMod 4) :
        ((eA.symm (QuaternionGroup.a i) : A) : P) ∈ H := by
      have hp := H.pow_mem hr i.val
      rw [← Subgroup.coe_pow, ← map_pow, QuaternionGroup.a_one_pow,
        ZMod.natCast_zmod_val] at hp
      exact hp
    cases q with
    | a i => exact hrot i
    | xa i =>
      have hp := H.mul_mem hd (hrot i)
      rw [← Subgroup.coe_mul, ← map_mul, QuaternionGroup.xa_mul_a, zero_add] at hp
      exact hp
  change A = H
  exact le_antisymm hAH hHA

theorem quaternionSubgroup_characteristic_of_centralProduct
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (eA : A ≃* QuaternionGroup 2)
    (hBcyc : IsCyclic B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = ⊤)
    (hinf : Nat.card ↥(A ⊓ B) = 2) :
    A.Characteristic := by
  classical
  have hcenter := center_eq_right_of_quaternion_centralProduct eA hBcyc hcomm hsup hinf
  have hclosure := quaternion_eq_intrinsic_closure_of_centralProduct
    eA hBcyc hcomm hsup hinf hcenter
  rw [hclosure, Subgroup.characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨a, ha, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · intro hφ
    have hfixed : (Subgroup.center P).comap φ.toMonoidHom = Subgroup.center P :=
      Subgroup.Characteristic.fixed inferInstance φ
    have hmem : a ∈ (Subgroup.center P).comap φ.toMonoidHom := hφ
    rw [hfixed] at hmem
    exact ha.1 hmem
  · change orderOf (φ a) = 4
    rw [φ.orderOf_eq, ha.2]

theorem center_isCyclic_of_quaternion_centralProduct
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (eA : A ≃* QuaternionGroup 2)
    (hBcyc : IsCyclic B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = ⊤)
    (hinf : Nat.card ↥(A ⊓ B) = 2) :
    IsCyclic ↥(Subgroup.center P) := by
  rw [center_eq_right_of_quaternion_centralProduct eA hBcyc hcomm hsup hinf]
  exact hBcyc

theorem central_involution_mem_quaternion_of_centralProduct
    {P : Type*} [Group P] [Finite P] {A B : Subgroup P}
    (eA : A ≃* QuaternionGroup 2)
    (hBcyc : IsCyclic B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = ⊤)
    (hinf : Nat.card ↥(A ⊓ B) = 2)
    {z : P} (hz : z ∈ Subgroup.center P) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    z ∈ A := by
  classical
  have hcenter := center_eq_right_of_quaternion_centralProduct eA hBcyc hcomm hsup hinf
  have hzB : z ∈ B := hcenter.le hz
  let zA : A := eA.symm (QuaternionGroup.a 2)
  let zP : P := zA
  have hzAcenter : zA ∈ Subgroup.center A :=
    (mem_center_iff_map_mem_center eA zA).2 (by
      simpa [zA] using quaternion_a_two_mem_center)
  have hzAB : zP ∈ A ⊓ B :=
    mem_inf_of_mem_center_quaternion hcomm hinf eA zA hzAcenter
  have hzPB : zP ∈ B := hzAB.2
  have hzA_sq : zA ^ 2 = 1 := by
    have h2 : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide
    change (eA.symm (QuaternionGroup.a 2)) ^ 2 = 1
    rw [← map_pow, h2, map_one]
  have hzP_sq : zP * zP = 1 := by
    have := congrArg (fun y : A => (y : P)) hzA_sq
    simpa [zP, pow_two] using this
  have hzA_ne : zA ≠ 1 := by
    intro h
    have hq : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by
      calc (QuaternionGroup.a 2 : QuaternionGroup 2) = eA zA := by simp [zA]
        _ = eA 1 := by rw [h]
        _ = 1 := map_one eA
    exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) hq
  have hzP_ne : zP ≠ 1 := by
    intro h
    exact hzA_ne (Subtype.ext (by simpa [zP] using h))
  have hzP_order : orderOf zP = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hzP_sq) hzP_ne
  have hzBord : orderOf (⟨z, hzB⟩ : B) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hz2 hz1
  have hzPordB : orderOf (⟨zP, hzPB⟩ : B) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hzP_order
  have hz_eq : z = zP :=
    congrArg Subtype.val
      (@eq_of_orderOf_eq_two_of_isCyclic B _ _ hBcyc _ _ hzBord hzPordB)
  rw [hz_eq]
  exact zA.2

theorem centralProduct_square (l : ℕ) (c : Multiplicative (ZMod (4 * l)))
    (q : QuaternionGroup 2) (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) :
    (centralProductProjection l (c, q)) ^ 2 =
      element (4 * l) (2 • Multiplicative.toAdd c + (2 * l : ℕ))
        (2 • Multiplicative.toAdd c + (2 * l : ℕ)) 0 := by
  rw [← map_pow]
  change centralProductProjection l (c ^ 2, q ^ 2) = _
  rw [quaternionEight_noncentral_square q hq]
  change element (4 * l) (2 • Multiplicative.toAdd c) (2 • Multiplicative.toAdd c) 0 *
    element (4 * l) (quarterScale l 2) (-quarterScale l 2) 0 = _
  rw [quarterScale_two, element_base_mul]
  have hneg : -((2 * l : ℕ) : ZMod (4 * l)) = (2 * l : ℕ) := by
    linear_combination -(twice_quarter_add_self l)
  rw [hneg]

theorem centralProduct_central_of_central_quaternion (l : ℕ) (hl : 0 < l)
    (c : Multiplicative (ZMod (4 * l))) (q : QuaternionGroup 2)
    (hq : q = 1 ∨ q = QuaternionGroup.a 2) :
    centralProductProjection l (c, q) ∈ Subgroup.center (Wreath (4 * l)) := by
  rw [centralProductProjection, MonoidHom.noncommCoprod_apply]
  apply (Subgroup.center (Wreath (4 * l))).mul_mem
  · exact (element_mem_center_iff _ (by omega) _ _ _).mpr ⟨rfl, rfl⟩
  · exact (quaternionEight_mem_center_iff l hl q).mpr hq

theorem v_noncentral_order_four_iff (l : ℕ) (hl : 0 < l) (g : Wreath (4 * l))
    (hg : g ∈ vSubgroup l) (hn : g ∉ Subgroup.center (Wreath (4 * l))) :
    orderOf g = 4 ↔ g ∈ quaternionEightSubgroup l := by
  constructor
  · intro horder
    have himg : g ∈ (centralProductProjection l).range :=
      (centralProductProjection_range l hl).symm ▸ hg
    obtain ⟨⟨c, q⟩, rfl⟩ := himg
    have hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 := by
      constructor <;> intro heq
      · exact hn (centralProduct_central_of_central_quaternion l hl c q (Or.inl heq))
      · exact hn (centralProduct_central_of_central_quaternion l hl c q (Or.inr heq))
    have hs := centralProduct_square l c q hq
    have hfour : (centralProductProjection l (c, q)) ^ 4 = 1 := by
      simpa only [horder] using pow_orderOf_eq_one (centralProductProjection l (c, q))
    have htwo : (centralProductProjection l (c, q)) ^ 2 ≠ 1 := by
      intro ht
      have hd := orderOf_dvd_of_pow_eq_one ht
      rw [horder] at hd
      norm_num at hd
    have hfour' : ((centralProductProjection l (c, q)) ^ 2) ^ 2 = 1 := by
      simpa only [← pow_mul] using hfour
    rw [hs, element_base_pow, element_base_eq_one_iff] at hfour'
    have hkill : 2 • (2 • Multiplicative.toAdd c) = 0 := by
      have hh := hfour'.1
      rw [smul_add, two_nsmul ((2 * l : ℕ) : ZMod (4 * l)), twice_quarter_add_self l,
        add_zero] at hh
      exact hh
    have hc : 2 • Multiplicative.toAdd c = 0 := by
      rcases (two_smul_eq_zero_half_quarter l hl _).mp hkill with hh | hh
      · exact hh
      · apply False.elim
        apply htwo
        rw [hs, hh, twice_quarter_add_self l, element_zero]
    rcases (two_smul_eq_zero_half_quarter l hl _).mp hc with hc | hc
    · rw [centralProductProjection, MonoidHom.noncommCoprod_apply]
      have hd : diagonalHom (4 * l) c = 1 := by
        change element (4 * l) (Multiplicative.toAdd c) (Multiplicative.toAdd c) 0 = 1
        rw [hc, element_zero]
      rw [hd, one_mul]
      exact ⟨q, rfl⟩
    · rw [centralProductProjection, MonoidHom.noncommCoprod_apply]
      apply (quaternionEightSubgroup l).mul_mem
      · refine ⟨QuaternionGroup.a 2, ?_⟩
        change element (4 * l) (quarterScale l 2) (-quarterScale l 2) 0 =
          element (4 * l) (Multiplicative.toAdd c) (Multiplicative.toAdd c) 0
        rw [hc, quarterScale_two]
        have hneg : -((2 * l : ℕ) : ZMod (4 * l)) = (2 * l : ℕ) := by
          linear_combination -(twice_quarter_add_self l)
        rw [hneg]
      · exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    have hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 := by
      have hn' := mt (quaternionEight_mem_center_iff l hl q).mpr hn
      simpa only [not_or] using hn'
    rw [orderOf_injective _ (quaternionEightEmbedding_injective l hl)]
    exact quaternionEight_noncentral_order q hq

theorem v_center_map (l : ℕ) (hl : 0 < l) :
    (Subgroup.center (vSubgroup l)).map (vSubgroup l).subtype =
      Subgroup.center (Wreath (4 * l)) := by
  rw [nonabelian_subgroup_center _ (by omega) _ (v_is_nonabelian l hl),
    inf_eq_right.mpr (center_le_v l hl)]

theorem v_mem_center_iff (l : ℕ) (hl : 0 < l) (g : vSubgroup l) :
    g ∈ Subgroup.center (vSubgroup l) ↔ g.val ∈ Subgroup.center (Wreath (4 * l)) := by
  constructor
  · intro hg
    rw [← v_center_map l hl]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hg a.val

@[expose] def quaternionInV (l : ℕ) : Subgroup (vSubgroup l) :=
  (quaternionEightSubgroup l).subgroupOf (vSubgroup l)

theorem quaternionInV_noncentral_iff (l : ℕ) (hl : 0 < l) (g : vSubgroup l)
    (hn : g ∉ Subgroup.center (vSubgroup l)) :
    g ∈ quaternionInV l ↔ orderOf g = 4 := by
  have hn' : g.val ∉ Subgroup.center (Wreath (4 * l)) :=
    mt (v_mem_center_iff l hl g).mpr hn
  change g.val ∈ quaternionEightSubgroup l ↔ orderOf g = 4
  rw [← v_noncentral_order_four_iff l hl g.val g.property hn']
  have ho : orderOf g.val = orderOf g :=
    orderOf_injective (vSubgroup l).subtype Subtype.val_injective g
  rw [ho]

@[expose] def quaternionToV (l : ℕ) : QuaternionGroup 2 →* vSubgroup l :=
  (quaternionEightEmbedding l).codRestrict (vSubgroup l) (fun q =>
    quaternionEight_le_v l ⟨q, rfl⟩)

theorem quaternionToV_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (quaternionToV l) := by
  intro q r h
  exact quaternionEightEmbedding_injective l hl (congrArg Subtype.val h)

theorem quaternionToV_range (l : ℕ) : (quaternionToV l).range = quaternionInV l := by
  ext g
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩

theorem quaternionToV_noncentral (l : ℕ) (hl : 0 < l) (q : QuaternionGroup 2)
    (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) :
    quaternionToV l q ∉ Subgroup.center (vSubgroup l) := by
  rw [v_mem_center_iff l hl]
  change quaternionEightEmbedding l q ∉ Subgroup.center (Wreath (4 * l))
  rw [quaternionEight_mem_center_iff l hl]
  exact not_or.mpr hq

theorem quaternionInV_eq_intrinsic_closure (l : ℕ) (hl : 0 < l) :
    quaternionInV l = Subgroup.closure
      {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4} := by
  let H := Subgroup.closure
    {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4}
  have hgen (q : QuaternionGroup 2) (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) :
      quaternionToV l q ∈ H := by
    apply Subgroup.subset_closure
    refine ⟨quaternionToV_noncentral l hl q hq, ?_⟩
    rw [orderOf_injective _ (quaternionToV_injective l hl)]
    exact quaternionEight_noncentral_order q hq
  have hr : quaternionToV l (QuaternionGroup.a 1) ∈ H := hgen _ (by decide)
  have hd : quaternionToV l (QuaternionGroup.xa 0) ∈ H := hgen _ (by decide)
  apply le_antisymm
  · intro g hg
    rw [← quaternionToV_range] at hg
    obtain ⟨q, rfl⟩ := hg
    have hrot (i : ZMod 4) : quaternionToV l (QuaternionGroup.a i) ∈ H := by
      have hp := H.pow_mem hr i.val
      rw [← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] at hp
      exact hp
    cases q with
    | a i => exact hrot i
    | xa i =>
      have hp := H.mul_mem hd (hrot i)
      rw [← map_mul, QuaternionGroup.xa_mul_a, zero_add] at hp
      exact hp
  · rw [Subgroup.closure_le]
    intro g hg
    exact (quaternionInV_noncentral_iff l hl g hg.1).mpr hg.2

theorem quaternionInV_characteristic (l : ℕ) (hl : 0 < l) :
    (quaternionInV l).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [quaternionInV_eq_intrinsic_closure l hl, MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨a, ha, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · intro hφ
    have hcenter : (Subgroup.center (vSubgroup l)).comap φ.toMonoidHom =
        Subgroup.center (vSubgroup l) :=
      Subgroup.Characteristic.fixed inferInstance φ
    have hmem : a ∈ (Subgroup.center (vSubgroup l)).comap φ.toMonoidHom := hφ
    rw [hcenter] at hmem
    exact ha.1 hmem
  · change orderOf (φ a) = 4
    rw [φ.orderOf_eq, ha.2]

theorem quaternionInV_noncentral_set (l : ℕ) (hl : 0 < l) :
    {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4} =
      quaternionToV l '' {q : QuaternionGroup 2 | q ≠ 1 ∧ q ≠ QuaternionGroup.a 2} := by
  ext g
  constructor
  · intro hg
    have hq := (quaternionInV_noncentral_iff l hl g hg.1).mpr hg.2
    rw [← quaternionToV_range] at hq
    obtain ⟨q, rfl⟩ := hq
    refine ⟨q, ?_, rfl⟩
    have hn : quaternionEightEmbedding l q ∉ Subgroup.center (Wreath (4 * l)) :=
      mt (v_mem_center_iff l hl (quaternionToV l q)).mpr hg.1
    change q ≠ 1 ∧ q ≠ QuaternionGroup.a 2
    simpa only [quaternionEight_mem_center_iff l hl, not_or] using hn
  · rintro ⟨q, hq, rfl⟩
    refine ⟨quaternionToV_noncentral l hl q hq, ?_⟩
    rw [orderOf_injective _ (quaternionToV_injective l hl)]
    exact quaternionEight_noncentral_order q hq

theorem card_v_noncentral_order_four (l : ℕ) (hl : 0 < l) :
    Nat.card {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4} = 6 := by
  rw [quaternionInV_noncentral_set l hl,
    Nat.card_image_of_injective (quaternionToV_injective l hl)]
  rw [Nat.card_eq_fintype_card]
  decide

end CFSG.Wreathed
