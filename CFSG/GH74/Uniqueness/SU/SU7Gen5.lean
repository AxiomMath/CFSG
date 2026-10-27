module

public import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.GH74.Uniqueness.SU.SU7Gen2

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup

theorem exists_cent_lift {X : Type*} [Group X] [Finite X] {O : Subgroup X} [O.Normal]
    (hO : Odd (Nat.card O)) {a : X} (ha : a * a = 1) {g : X}
    (hg : QuotientGroup.mk' O g * QuotientGroup.mk' O a =
      QuotientGroup.mk' O a * QuotientGroup.mk' O g) :
    ∃ g' : X, g' * a = a * g' ∧ QuotientGroup.mk' O g' = QuotientGroup.mk' O g := by
  classical
  by_cases ha1 : a = 1
  · exact ⟨g, by rw [ha1]; simp, rfl⟩
  have hy : g * a * g⁻¹ = a * (a⁻¹ * (g * a * g⁻¹)) := by group
  have hmk : QuotientGroup.mk' O (g * a * g⁻¹) = QuotientGroup.mk' O a := by
    rw [map_mul, map_mul, map_inv, hg]; group
  have hO' : a⁻¹ * (g * a * g⁻¹) ∈ O := QuotientGroup.eq.1 hmk.symm
  have hyS : g * a * g⁻¹ ∈ O ⊔ zpowers a := by
    rw [sup_comm, hy]
    exact Subgroup.mul_mem_sup (mem_zpowers a) hO'
  have hy2 : (g * a * g⁻¹) ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha]; group
  obtain ⟨k, hk, hkS⟩ := exists_conj_mem_of_two_element hO (isPGroup_zpowers_of_pow
    (show a ^ (2 ^ 1) = 1 by rw [pow_one, pow_two]; exact ha)) (isPGroup_zpowers_of_pow hy2) hyS
  have hk1 : k⁻¹ * (g * a * g⁻¹) * k ≠ 1 := by
    intro h
    apply ha1
    have : g * a * g⁻¹ = 1 := by
      have h2 : k * (k⁻¹ * (g * a * g⁻¹) * k) * k⁻¹ = k * 1 * k⁻¹ := by rw [h]
      simpa [mul_assoc] using h2
    have h3 : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [h3, this]; group
  have hka : k⁻¹ * (g * a * g⁻¹) * k = a := by
    obtain ⟨j, hj⟩ := hkS
    have hj' : a ^ j = k⁻¹ * (g * a * g⁻¹) * k := hj
    have ha2' : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
    · exfalso
      apply hk1
      rw [← hj', zpow_mul, ha2', one_zpow]
    · rw [← hj', zpow_add, zpow_mul, ha2', one_zpow, one_mul, zpow_one]
  have hk1' : (QuotientGroup.mk' O) k = 1 := (QuotientGroup.eq_one_iff k).2 hk
  refine ⟨k⁻¹ * g, ?_, ?_⟩
  · calc k⁻¹ * g * a = (k⁻¹ * (g * a * g⁻¹) * k) * (k⁻¹ * g) := by group
      _ = a * (k⁻¹ * g) := by rw [hka]
  · rw [map_mul, map_inv, hk1', inv_one, one_mul]

theorem odd_normal_cent_eq_bot {Y : Type*} [Group Y] [Finite Y] {P Q : Subgroup Y} {a : Y}
    (hPn : ∀ y : Y, ∀ t ∈ P, y * t * y⁻¹ ∈ P) (hP2 : IsPGroup 2 P)
    (hCP : ∀ y : Y, (∀ t ∈ P, y * t = t * y) → y ∈ P)
    (hcl : ∀ t ∈ P, (t * a * t⁻¹) * a = a * (t * a * t⁻¹)) (haP : a ∈ P)
    (hQodd : Odd (Nat.card Q)) (hQa : ∀ q ∈ Q, q * a = a * q)
    (hQn : ∀ y : Y, y * a = a * y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) : Q = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hPQ : P ⊓ Q = ⊥ := inf_eq_bot_of_isPGroup hP2 hQodd
  have stepA : ∀ s ∈ P, s * a = a * s → q * s = s * q := by
    intro s hsP hsa
    have h1 : s * q⁻¹ * s⁻¹ ∈ Q := hQn s hsa q⁻¹ (Q.inv_mem hq)
    have h2 : q * (s * q⁻¹ * s⁻¹) ∈ Q := Q.mul_mem hq h1
    have h3 : (q * s * q⁻¹) * s⁻¹ ∈ P := P.mul_mem (hPn q s hsP) (P.inv_mem hsP)
    have e : q * (s * q⁻¹ * s⁻¹) = q * s * q⁻¹ * s⁻¹ := by group
    have h4 : q * s * q⁻¹ * s⁻¹ ∈ P ⊓ Q := ⟨h3, by rw [← e]; exact h2⟩
    rw [hPQ, Subgroup.mem_bot] at h4
    calc q * s = (q * s * q⁻¹ * s⁻¹) * (s * q) := by group
      _ = s * q := by rw [h4, one_mul]
  have hqa := hQa q hq
  have hqa' : q⁻¹ * a * q = a := by
    calc q⁻¹ * a * q = q⁻¹ * (a * q) := by group
      _ = q⁻¹ * (q * a) := by rw [hqa]
      _ = a := by group
  have hn : Odd (orderOf q) := Odd.of_dvd_nat hQodd (Subgroup.orderOf_dvd_natCard Q hq)
  have hcomm : ∀ t ∈ P, q * t = t * q := by
    intro t ht
    set w := t⁻¹ * (q * t * q⁻¹) with hw
    have hwP : w ∈ P := P.mul_mem (P.inv_mem ht) (hPn q t ht)
    have ha'P : t * a * t⁻¹ ∈ P := hPn t a haP
    have hqa'' : q * (t * a * t⁻¹) = (t * a * t⁻¹) * q := stepA _ ha'P (hcl t ht)
    have hwa : w * a = a * w := by
      have h1 : (q * t * q⁻¹) * a * (q * t * q⁻¹)⁻¹ = t * a * t⁻¹ := by
        calc (q * t * q⁻¹) * a * (q * t * q⁻¹)⁻¹ = q * t * (q⁻¹ * a * q) * t⁻¹ * q⁻¹ := by group
          _ = q * (t * a * t⁻¹) * q⁻¹ := by rw [hqa']; group
          _ = (t * a * t⁻¹) * q * q⁻¹ := by rw [hqa'']
          _ = t * a * t⁻¹ := by group
      have h2 : w * a * w⁻¹ = a := by
        calc w * a * w⁻¹ = t⁻¹ * ((q * t * q⁻¹) * a * (q * t * q⁻¹)⁻¹) * t := by rw [hw]; group
          _ = a := by rw [h1]; group
      calc w * a = (w * a * w⁻¹) * w := by group
        _ = a * w := by rw [h2]
    have hqw : q * w = w * q := stepA w hwP hwa
    have hqt : q * t * q⁻¹ = t * w := by rw [hw]; group
    have hit : ∀ i : ℕ, q ^ i * t * (q ^ i)⁻¹ = t * w ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have hqwi : q * w ^ i * q⁻¹ = w ^ i := by
          have : Commute q (w ^ i) := (show Commute q w from hqw).pow_right i
          rw [this.eq]; group
        calc q ^ (i + 1) * t * (q ^ (i + 1))⁻¹ = q * (q ^ i * t * (q ^ i)⁻¹) * q⁻¹ := by group
          _ = q * (t * w ^ i) * q⁻¹ := by rw [ih]
          _ = (q * t * q⁻¹) * (q * w ^ i * q⁻¹) := by group
          _ = (t * w) * w ^ i := by rw [hqt, hqwi]
          _ = t * w ^ (i + 1) := by group
    have hwn : w ^ orderOf q = 1 := by
      have h := hit (orderOf q)
      rw [pow_orderOf_eq_one, inv_one] at h
      have h' : t * 1 = t * w ^ orderOf q := by simpa using h
      exact (mul_left_cancel h').symm
    have hw1 : w = 1 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP2 ⟨w, hwP⟩
      have hk' : orderOf w = 2 ^ k := by simpa using hk
      have hdvd : orderOf w ∣ orderOf q := orderOf_dvd_of_pow_eq_one hwn
      have hodd : Odd (orderOf w) := Odd.of_dvd_nat hn hdvd
      have hk0 : k = 0 := by
        by_contra hne
        rw [hk'] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
      rw [hk0, pow_zero] at hk'
      exact orderOf_eq_one_iff.1 hk'
    rw [hw1, mul_one] at hqt
    calc q * t = (q * t * q⁻¹) * q := by group
      _ = t * q := by rw [hqt]
  have hqP : q ∈ P := hCP q hcomm
  have : q ∈ P ⊓ Q := ⟨hqP, hq⟩
  rw [hPQ, Subgroup.mem_bot] at this
  exact this

theorem comm_mem_of_sq_mem {G : Type*} [Group G] {T Z : Subgroup G}
    (hZc : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hsq : ∀ y ∈ T, y * y ∈ Z) :
    ∀ t ∈ T, ∀ a ∈ T, t * a * t⁻¹ * a⁻¹ ∈ Z := by
  intro t ht a ha
  have hu := hsq (t * a) (T.mul_mem ht ha)
  have hv := hsq t ht
  have hs := hsq a ha
  have hvi : (t * t)⁻¹ ∈ Z := Z.inv_mem hv
  have hcom : a * (t * t)⁻¹ = (t * t)⁻¹ * a := (hZc _ hvi a ha).symm
  have e : ((t * a) * (t * a)) * (t * t)⁻¹ * (a * a)⁻¹ = t * a * t⁻¹ * a⁻¹ := by
    calc ((t * a) * (t * a)) * (t * t)⁻¹ * (a * a)⁻¹
        = t * a * t * (a * (t * t)⁻¹) * (a * a)⁻¹ := by group
      _ = t * a * t * ((t * t)⁻¹ * a) * (a * a)⁻¹ := by rw [hcom]
      _ = t * a * t⁻¹ * a⁻¹ := by group
  rw [← e]
  exact Z.mul_mem (Z.mul_mem hu hvi) (Z.inv_mem hs)

theorem alt5_exists_three_fpf {P : Subgroup (alternatingGroup (Fin 5))}
    (hP4 : Nat.card P = 4) (hPe : ∀ g ∈ P, g * g = 1) :
    ∃ c : alternatingGroup (Fin 5), c ≠ 1 ∧ c * c * c = 1 ∧ (∀ p ∈ P, c * p * c⁻¹ ∈ P) ∧
      ∀ p ∈ P, p ≠ 1 → c * p * c⁻¹ ≠ p := by
  obtain ⟨a, ha, ha1, b, hb, hb1, hba⟩ := exists_two_ne_one_of_card_four hP4
  have haa := hPe a ha
  have hbb := hPe b hb
  have hab : a * b = b * a := by
    have h1 := hPe (a * b) (P.mul_mem ha hb)
    have ainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    have binv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    have h2 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [mul_inv_rev, ainv, binv] at h2
    exact h2.symm
  have hall := eq_four_of_card hP4 ha hb ha1 hb1 hba haa hab
  have hsign : ∀ y : alternatingGroup (Fin 5), Equiv.Perm.sign (y : Equiv.Perm (Fin 5)) = 1 :=
    fun y => MonoidHom.mem_ker.1 y.2
  obtain ⟨c, hcs, hc1, hc3, hca, hcb⟩ := a5_three_elt (a : Equiv.Perm (Fin 5)) b (hsign a)
    (hsign b) (fun h => ha1 (Subtype.ext h)) (fun h => hb1 (Subtype.ext h))
    (fun h => hba (Subtype.ext h.symm))
    (by simpa using congrArg Subtype.val haa) (by simpa using congrArg Subtype.val hbb)
    (by simpa using congrArg Subtype.val hab)
  let c' : alternatingGroup (Fin 5) := ⟨c, MonoidHom.mem_ker.2 hcs⟩
  have hc'a : c' * a * c'⁻¹ = b := Subtype.ext (by simpa using hca)
  have hc'b : c' * b * c'⁻¹ = a * b := Subtype.ext (by simpa using hcb)
  have hc'ab : c' * (a * b) * c'⁻¹ = a := by
    calc c' * (a * b) * c'⁻¹ = (c' * a * c'⁻¹) * (c' * b * c'⁻¹) := by group
      _ = b * (a * b) := by rw [hc'a, hc'b]
      _ = (b * a) * b := by group
      _ = (a * b) * b := by rw [hab]
      _ = a * (b * b) := by group
      _ = a := by rw [hbb, mul_one]
  refine ⟨c', fun h => hc1 (congrArg Subtype.val h), Subtype.ext (by simpa using hc3),
    fun p hp => ?_, fun p hp hp1 => ?_⟩
  · rcases hall p hp with rfl | rfl | rfl | rfl
    · simp
    · rw [hc'a]; exact hb
    · rw [hc'b]; exact P.mul_mem ha hb
    · rw [hc'ab]; exact ha
  · rcases hall p hp with rfl | rfl | rfl | rfl
    · exact absurd rfl hp1
    · rw [hc'a]; exact hba
    · rw [hc'b]
      intro h
      apply ha1
      have : a * p = 1 * p := by rw [h, one_mul]
      exact mul_right_cancel this
    · rw [hc'ab]
      intro h
      apply hb1
      have : a * 1 = a * b := by rw [mul_one]; exact h
      exact (mul_left_cancel this).symm

end CFSG.GH74.Uniqueness.SU.SU7.Gen
