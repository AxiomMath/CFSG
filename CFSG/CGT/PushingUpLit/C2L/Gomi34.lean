module

public import CFSG.CGT.PushingUpLit.C2L.GomiMax

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_of_pow_odd_of_pow_two_pow {x : G} {b j : ℕ} (hb : Odd b) (h1 : x ^ b = 1)
    (h2 : x ^ 2 ^ j = 1) : x = 1 := by
  have hcop : Nat.Coprime b (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hb)
  have h : orderOf x ∣ Nat.gcd b (2 ^ j) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one hcop] at h
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)

theorem pow_mul_mul_pow_inv_eq {m o z : G} (hz : z = ⁅m, o⁆) (hzm : m * z = z * m) (k : ℕ) :
    m ^ k * o * (m ^ k)⁻¹ = z ^ k * o := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : m * o * m⁻¹ = z * o := by rw [hz, commutatorElement_def]; group
    have h2 : m * z ^ k * m⁻¹ = z ^ k := by
      have hc : Commute m (z ^ k) := Commute.pow_right hzm k
      rw [hc.eq]
      group
    calc m ^ (k + 1) * o * (m ^ (k + 1))⁻¹ = m * (m ^ k * o * (m ^ k)⁻¹) * m⁻¹ := by group
      _ = m * (z ^ k * o) * m⁻¹ := by rw [ih]
      _ = (m * z ^ k * m⁻¹) * (m * o * m⁻¹) := by group
      _ = z ^ (k + 1) * o := by rw [h2, h1]; group

theorem commute_of_odd_pow {Z O : Subgroup G} (hZ2 : IsPGroup 2 Z) {m : G} {b : ℕ} (hb : Odd b)
    (hmb : m ^ b = 1) (hZc : ∀ z ∈ Z, m * z = z * m) (hm : ∀ o ∈ O, ⁅m, o⁆ ∈ Z) :
    ∀ o ∈ O, m * o = o * m := by
  intro o ho
  have hz := hm o ho
  have h1 := pow_mul_mul_pow_inv_eq (m := m) (o := o) (z := ⁅m, o⁆) rfl (hZc _ hz) b
  rw [hmb] at h1
  have h2 : ⁅m, o⁆ ^ b = 1 := by
    have h3 : ⁅m, o⁆ ^ b * o = o := by simpa using h1.symm
    simpa using h3
  obtain ⟨j, hj⟩ := hZ2 ⟨⁅m, o⁆, hz⟩
  have h3 : ⁅m, o⁆ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  exact commutatorElement_eq_one_iff_mul_comm.1 (eq_one_of_pow_odd_of_pow_two_pow hb h2 h3)

@[expose] def centralizerMod (M Z O : Subgroup G) (hZ : ∀ z ∈ Z, ∀ m ∈ M, m * z = z * m) :
    Subgroup G where
  carrier := {m | m ∈ M ∧ ∀ o ∈ O, ⁅m, o⁆ ∈ Z}
  one_mem' := ⟨M.one_mem, fun o _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    refine ⟨M.mul_mem haM hbM, fun o ho => ?_⟩
    have e : ⁅a * b, o⁆ = a * ⁅b, o⁆ * a⁻¹ * ⁅a, o⁆ := by
      simp only [commutatorElement_def]; group
    have hc : a * ⁅b, o⁆ * a⁻¹ = ⁅b, o⁆ := by
      rw [hZ _ (hb o ho) a haM]; group
    rw [e, hc]
    exact Z.mul_mem (hb o ho) (ha o ho)
  inv_mem' := by
    rintro a ⟨haM, ha⟩
    refine ⟨M.inv_mem haM, fun o ho => ?_⟩
    have e : ⁅a⁻¹, o⁆ = a⁻¹ * ⁅a, o⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    have hc : a⁻¹ * ⁅a, o⁆⁻¹ * a⁻¹⁻¹ = ⁅a, o⁆⁻¹ := by
      have := hZ _ (Z.inv_mem (ha o ho)) a⁻¹ (M.inv_mem haM)
      rw [this]; group
    rw [e, hc]
    exact Z.inv_mem (ha o ho)

section Main

variable [Finite G]

theorem prop34_not_le {N S T : Subgroup G}
    (hN : N ⊓ Subgroup.centralizer (oTwoIn N : Set G) ≤ oTwoIn N)
    (hS : IsSylowOf 2 S N) (hT : IsSylowOf 2 T N) (hcS : ClassLETwo S) (hne : S ≠ T) :
    ¬ (S ⊓ Subgroup.centralizer (S : Set G) ≤ T ⊓ Subgroup.centralizer (T : Set G)) := by
  intro hZT
  have hMN : S ⊔ T ≤ N := sup_le hS.le hT.le
  have hSM : IsSylowOf 2 S (S ⊔ T) := hS.of_le le_sup_left hMN
  have hTM : IsSylowOf 2 T (S ⊔ T) := hT.of_le le_sup_right hMN
  have hZc : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set G), ∀ m ∈ S ⊔ T, m * z = z * m := by
    intro z hz m hm
    have hzS := Subgroup.mem_centralizer_iff.1 hz.2
    have hzT := Subgroup.mem_centralizer_iff.1 (hZT hz).2
    have hle : S ⊔ T ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun s hs => ?_) (fun t ht => ?_)
      · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        exact (hzS s hs).symm
      · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        exact (hzT t ht).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle hm) z (Set.mem_singleton z)).symm
  have hZ2 : IsPGroup 2 ↥(S ⊓ Subgroup.centralizer (S : Set G)) :=
    hS.isPGroup.to_le inf_le_left
  have hOM : oTwoIn (S ⊔ T) ≤ S ⊔ T := oTwoIn_le _
  have hOn : S ⊔ T ≤ Subgroup.normalizer (oTwoIn (S ⊔ T) : Set G) := le_normalizer_oTwoIn _
  have hOp : IsPGroup 2 (oTwoIn (S ⊔ T)) := isPGroup_oTwoIn _
  have hOS : oTwoIn (S ⊔ T) ≤ S := le_of_isSylowOf_of_normal hSM hOM hOn hOp
  have hOT : oTwoIn (S ⊔ T) ≤ T := le_of_isSylowOf_of_normal hTM hOM hOn hOp
  have hNO : oTwoIn N ≤ oTwoIn (S ⊔ T) :=
    le_oTwoIn_of_normal ((oTwoIn_le_of_isSylowOf hS).trans le_sup_left)
      (hMN.trans (le_normalizer_oTwoIn N)) (isPGroup_oTwoIn N)
  have hcent : ∀ c ∈ S ⊔ T, (∀ o ∈ oTwoIn (S ⊔ T), c * o = o * c) → c ∈ oTwoIn (S ⊔ T) := by
    intro c hc hcO
    have hc' : c ∈ N ⊓ Subgroup.centralizer (oTwoIn N : Set G) :=
      ⟨hMN hc, Subgroup.mem_centralizer_iff.2 fun h hh => (hcO h (hNO hh)).symm⟩
    exact hNO (hN hc')
  set C : Subgroup G := centralizerMod (S ⊔ T) (S ⊓ Subgroup.centralizer (S : Set G))
    (oTwoIn (S ⊔ T)) hZc with hCdef
  have hCM : C ≤ S ⊔ T := fun c hc => hc.1
  have hCn : S ⊔ T ≤ Subgroup.normalizer (C : Set G) := by
    have key : ∀ g ∈ S ⊔ T, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      refine ⟨mul_mem (mul_mem hg hc.1) (inv_mem hg), fun o ho => ?_⟩
      have hgo : g⁻¹ * o * g ∈ oTwoIn (S ⊔ T) := by
        have := conj_mem_oTwoIn (X := S ⊔ T) (Subgroup.le_normalizer (inv_mem hg)) ho
        simpa using this
      have h1 := hc.2 _ hgo
      have e : ⁅g * c * g⁻¹, o⁆ = g * ⁅c, g⁻¹ * o * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e, hZc _ h1 g hg]
      simpa using h1
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hh
    simpa [mul_assoc] using this
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨k, b, hb, hkb⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (c : G)).ne'
    refine ⟨k, Subtype.ext ?_⟩
    have hm'C : (c : G) ^ 2 ^ k ∈ C := C.pow_mem c.2 _
    have hm'b : ((c : G) ^ 2 ^ k) ^ b = 1 := by
      rw [← pow_mul, ← hkb]
      exact pow_orderOf_eq_one _
    have hZc' : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set G),
        (c : G) ^ 2 ^ k * z = z * (c : G) ^ 2 ^ k :=
      fun z hz => hZc z hz _ hm'C.1
    have hcomm := commute_of_odd_pow hZ2 hb hm'b hZc' hm'C.2
    have hm'O : (c : G) ^ 2 ^ k ∈ oTwoIn (S ⊔ T) := hcent _ hm'C.1 hcomm
    obtain ⟨j, hj⟩ := hOp ⟨(c : G) ^ 2 ^ k, hm'O⟩
    have hj' : ((c : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have := eq_one_of_pow_odd_of_pow_two_pow hb hm'b hj'
    simpa using this
  have hCO : C ≤ oTwoIn (S ⊔ T) := le_oTwoIn_of_normal hCM hCn hCp
  have hSC : S ≤ C := by
    intro s hs
    refine ⟨(le_sup_left : S ≤ S ⊔ T) hs, fun o ho => ?_⟩
    have hos : o ∈ S := hOS ho
    refine ⟨S.mul_mem (S.mul_mem (S.mul_mem hs hos) (S.inv_mem hs)) (S.inv_mem hos), ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
    exact (commutatorElement_eq_one_iff_mul_comm.1 (hcS s hs o hos c hc)).symm
  have hST : S ≤ T := (hSC.trans hCO).trans hOT
  exact hne (hS.eq_of_le hST hT.le hT.isPGroup).symm

end Main

end CFSG.CGT.PushingUpLit.C2L

