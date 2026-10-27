module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

namespace CatDistinct

private theorem orderG2_two_pow_four {a : ℕ} (ha : 1 ≤ a) :
    ∃ O, Odd O ∧ O % 4 = 1 ∧ orderG2 (2 ^ a) = 2 ^ (a * 6) * O := by
  have h6 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 6)
  have h2 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 2)
  have p6 : 1 ≤ (2 ^ a) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have p2 : 1 ≤ (2 ^ a) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have e1 : ((2 ^ a) ^ 6 - 1) % 4 = 3 := by omega
  have e2 : ((2 ^ a) ^ 2 - 1) % 4 = 3 := by omega
  have hmod : (((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1)) % 4 = 1 := by
    rw [Nat.mul_mod, e1, e2]
  refine ⟨((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1),
    (odd_pow_two_pow_sub_one ha (by norm_num)).mul (odd_pow_two_pow_sub_one ha (by norm_num)),
    hmod, ?_⟩
  simp only [orderG2]
  rw [pow_mul 2 a 6, mul_assoc]

private theorem g2_ne_A2 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    orderG2 (2 ^ a) ≠ orderA 2 (2 ^ b) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := orderG2_two_pow_four ha
  have hg := orderA_two_mul_gcd (2 ^ b)
  rw [← h, e₁] at hg
  have hodd_g : Odd (Nat.gcd 3 (2 ^ b - 1)) :=
    Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
  have hP : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) :=
    (odd_pow_two_pow_sub_one hb (by norm_num)).mul (odd_pow_two_pow_sub_one hb (by norm_num))
  have hg' : 2 ^ (a * 6) * (O₁ * Nat.gcd 3 (2 ^ b - 1)) =
      2 ^ (b * 3) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) := by
    rw [← mul_assoc, hg, ← pow_mul]
  obtain ⟨h12, hprod⟩ := two_pow_mul_odd_inj (hO₁.mul hodd_g) hP hg'
  have hb2 : b = 2 * a := by omega
  have hQ3 : (2 ^ b) % 3 = 1 := by
    rw [hb2, pow_mul]
    norm_num [Nat.pow_mod]
  have hg3 : Nat.gcd 3 (2 ^ b - 1) = 3 := by
    apply Nat.gcd_eq_left
    omega
  rw [hg3] at hprod
  have e2 := mod_four_sq hb
  have e3 := mod_four_cube_sub hb
  have h4 := congrArg (· % 4) hprod
  simp only [Nat.mul_mod O₁ 3, Nat.mul_mod (((2 ^ b) ^ 2 - 1)), hm₁, e2, e3] at h4
  omega

private theorem g2_ne_U3 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    orderG2 (2 ^ a) ≠ orderTwistedA 2 (2 ^ b) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := orderG2_two_pow_four ha
  have hg := orderTwistedA_mul_gcd (r := 2) (m := b) (by norm_num) hb
  rw [← h, e₁, twP_two] at hg
  have hodd_g : Odd (Nat.gcd (2 + 1) (2 ^ b + 1)) := odd_gcd_twisted hb
  have hP : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) :=
    (odd_pow_two_pow_sub_one hb (by norm_num)).mul (odd_pow_two_pow_add_one hb (by norm_num))
  have hg' : 2 ^ (a * 6) * (O₁ * Nat.gcd (2 + 1) (2 ^ b + 1)) =
      2 ^ (b * 3) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) := by
    rw [← mul_assoc, hg, ← pow_mul]
  obtain ⟨h12, hprod⟩ := two_pow_mul_odd_inj (hO₁.mul hodd_g) hP hg'
  have hb2 : b = 2 * a := by omega
  have hQ3 : (2 ^ b) % 3 = 1 := by
    rw [hb2, pow_mul]
    norm_num [Nat.pow_mod]
  have hg3 : Nat.gcd (2 + 1) (2 ^ b + 1) = 1 := by
    have h3 : ¬ 3 ∣ 2 ^ b + 1 := by omega
    exact (Nat.prime_three.coprime_iff_not_dvd).2 h3
  rw [hg3] at hprod
  have e2 := mod_four_sq hb
  have e3 := mod_four_cube_add hb
  have h4 := congrArg (· % 4) hprod
  simp only [mul_one, Nat.mul_mod (((2 ^ b) ^ 2 - 1)), hm₁, e2, e3] at h4
  omega

private theorem orderA_two_ge {c : ℕ} (hc : 4 ≤ c) : 20160 ≤ orderA 2 c := by
  have hg := orderA_two_mul_gcd c
  have hg3 : Nat.gcd 3 (c - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h1 : 4 ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hc 3
  have h2 : 4 ^ 2 - 1 ≤ c ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1
  have h3 : 4 ^ 3 - 1 ≤ c ^ 3 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 3) 1
  have hX : 20160 * 3 ≤ c ^ 3 * ((c ^ 2 - 1) * (c ^ 3 - 1)) := by
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    norm_num at this ⊢
    exact this
  have hmul : c ^ 3 * ((c ^ 2 - 1) * (c ^ 3 - 1)) ≤ orderA 2 c * 3 := by
    rw [← hg]
    exact Nat.mul_le_mul_left _ hg3
  omega

private theorem orderTwistedA_two_ge {c : ℕ} (hc : 5 ≤ c) : 126000 ≤ orderTwistedA 2 c := by
  have hg : orderTwistedA 2 c * Nat.gcd (2 + 1) (c + 1) =
      c ^ 3 * ((c ^ 2 - 1) * (c ^ 3 + 1)) := by
    have h := (gcd_dvd_twP (r := 2) (Q := c) (by norm_num) (by omega)).mul_left (c ^ 3)
    rw [twP_two] at h
    rw [orderTwistedA_eq, twP_two, show 2 * (2 + 1) / 2 = 3 from rfl]
    exact Nat.div_mul_cancel h
  have hg3 : Nat.gcd (2 + 1) (c + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h1 : 5 ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hc 3
  have h2 : 5 ^ 2 - 1 ≤ c ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1
  have h3 : 5 ^ 3 + 1 ≤ c ^ 3 + 1 := Nat.add_le_add_right (Nat.pow_le_pow_left hc 3) 1
  have hX : 126000 * 3 ≤ c ^ 3 * ((c ^ 2 - 1) * (c ^ 3 + 1)) := by
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    norm_num at this ⊢
    exact this
  have hmul : c ^ 3 * ((c ^ 2 - 1) * (c ^ 3 + 1)) ≤ orderTwistedA 2 c * 3 := by
    rw [← hg]
    exact Nat.mul_le_mul_left _ hg3
  omega

theorem field_g2_exc (hc : Ctx) (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq2 : q.p = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (h2 : catalogIs S excIndex) : False := by
  have h3 : 3 ≤ q.card := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hcard : Nat.card S = orderG2 q.card := hc.bridge ⟨.G2 q, hv⟩ S ⟨e⟩
  have hbig : 4245696 ≤ Nat.card S := by
    rw [hcard]
    exact orderG2_ge h3
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hcharq : (TauCeti.LieTypeIndex.G2 q).characteristic = 2 := by
    rw [TauCeti.LieTypeIndex.characteristic_G2, hq2]
  obtain ⟨i, hi, ⟨f⟩⟩ := h2
  cases i with
  | cyclic p hp => simp [excIndex] at hi
  | alternating n hn =>
    simp only [excIndex] at hi
    rw [card_alternating_of_iso hn f] at hbig
    rcases hi with rfl | rfl <;> revert hbig <;> decide
  | sporadic s =>
    simp only [excIndex] at hi
    subst hi
    have : Nat.card S = 443520 := by
      rw [Nat.card_congr f.toEquiv]
      exact hc.m22
    omega
  | lie idx =>
    obtain ⟨d, hv'⟩ := idx
    cases d with
    | A r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hcard' : Nat.card S = orderA 2 q'.card := hc.bridge ⟨.A 2 q', hv'⟩ S ⟨f⟩
        have hqc' : q'.card = 2 ^ q'.exponent := by
          rw [TauCeti.PrimePower.card_def, hq']
        rw [hqc'] at hcard'
        rw [hqc] at hcard
        exact g2_ne_A2 q.exponent_pos q'.exponent_pos (hcard.symm.trans hcard')
      · have hadm' : StatedLieAdmissible .PSL 3 q'.p q'.exponent :=
          ⟨q'.prime_p, q'.exponent_pos, by norm_num, by simp, by simp⟩
        refine xc hc (t' := .PSL) (n' := 3) (by simp) hadm' hq' ?_ ⟨.G2 q, hv⟩ hcharq e
        refine hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.A 2 q', hv'⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderA, lieOrderNumerator, lieOrderDivisor,
          TauCeti.PrimePower.card_def]
    | twistedA r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hcard' : Nat.card S = orderTwistedA 2 q'.card :=
          hc.bridge ⟨.twistedA 2 q', hv'⟩ S ⟨f⟩
        have hqc' : q'.card = 2 ^ q'.exponent := by
          rw [TauCeti.PrimePower.card_def, hq']
        rw [hqc'] at hcard'
        rw [hqc] at hcard
        exact g2_ne_U3 q.exponent_pos q'.exponent_pos (hcard.symm.trans hcard')
      · have h3' : 3 ≤ q'.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv').1).2 rfl
        have hadm' : StatedLieAdmissible .PSU 3 q'.p q'.exponent := by
          refine ⟨q'.prime_p, q'.exponent_pos, le_rfl, ?_⟩
          intro hh
          have : q'.p ^ q'.exponent = 2 := (Prod.mk.inj hh).2
          have h3'' : 3 ≤ q'.p ^ q'.exponent := by
            rwa [TauCeti.PrimePower.card_def] at h3'
          omega
        refine xc hc (t' := .PSU) (n' := 3) (by simp) hadm' hq' ?_ ⟨.G2 q, hv⟩ hcharq e
        refine hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.twistedA 2 q', hv'⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderTwistedA, lieOrderNumerator, lieOrderDivisor,
          TauCeti.PrimePower.card_def]
    | _ => simp [excIndex] at hi

theorem field_u33_exc (hc : Ctx) (S : Type) [Group S] [Finite S] (h1 : catalogIs S isU33)
    (h2 : catalogIs S excIndex) : False := by
  have hcard : Nat.card S = 6048 := card_isU33 hc.bridge h1
  obtain ⟨i, hi, ⟨f⟩⟩ := h2
  cases i with
  | cyclic p hp => simp [excIndex] at hi
  | alternating n hn =>
    simp only [excIndex] at hi
    rw [card_alternating_of_iso hn f] at hcard
    rcases hi with rfl | rfl <;> revert hcard <;> decide
  | sporadic s =>
    simp only [excIndex] at hi
    subst hi
    have : Nat.card S = 443520 := by
      rw [Nat.card_congr f.toEquiv]
      exact hc.m22
    omega
  | lie idx =>
    obtain ⟨d, hv'⟩ := idx
    cases d with
    | A r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      have h4 : 4 ≤ q'.card := by
        rw [TauCeti.PrimePower.card_def]
        omega
      have hcard' : Nat.card S = orderA 2 q'.card := hc.bridge ⟨.A 2 q', hv'⟩ S ⟨f⟩
      have hge := orderA_two_ge h4
      omega
    | twistedA r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      have h5 : 5 ≤ q'.card := by
        have h3 : 3 ≤ q'.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv').1).2 rfl
        rw [TauCeti.PrimePower.card_def] at h3 ⊢
        omega
      have hcard' : Nat.card S = orderTwistedA 2 q'.card :=
        hc.bridge ⟨.twistedA 2 q', hv'⟩ S ⟨f⟩
      have hge := orderTwistedA_two_ge h5
      omega
    | _ => simp [excIndex] at hi

end CatDistinct

end CFSG.LocalAnalysis.GLTheoremA
