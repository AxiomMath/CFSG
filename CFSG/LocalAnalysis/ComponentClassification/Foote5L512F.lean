module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511I

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem exists_mem_L_conj_t_of_noncentral (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    {x : G} (hx : x ∈ S ⊓ L) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    ∃ y ∈ L, y * x * y⁻¹ = x ∧ y * t * y⁻¹ = x * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 := h.t_mul_self
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨k, hkL, hk⟩ := h.exists_conj_t hx hxo
  have hxtc : x * t = t * x := (h.tZ x (mem_inf.mp hx).1)
  set A := kleinFourOfCommutingInvolutions x t hx2 ht2 hxtc with hAdef
  have hA4 : Nat.card A = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions x t hx2 ht2 hx1 h.t_ne_one hxt hxtc).card_four
  have hAR : A ≤ S ⊓ L := fun a ha => by
    rcases (mem_kleinFour_iff hx2 ht2 hxtc).mp ha with rfl | rfl | rfl | rfl
    · exact mul_mem hx h.tR
    · exact hx
    · exact h.tR
    · exact one_mem _
  have hAx : ∀ a ∈ A, a * x = x * a := fun a ha => by
    rcases (mem_kleinFour_iff hx2 ht2 hxtc).mp ha with rfl | rfl | rfl | rfl
    · rw [mul_assoc, ← hxtc, ← mul_assoc]
    · rfl
    · exact hxtc.symm
    · rw [one_mul, mul_one]
  set A' := conjugate A k with hA'def
  have hA'X : A' ≤ L ⊓ centralizer ({t} : Set G) := by
    intro a ha
    rw [hA'def, mem_conjugate_iff] at ha
    refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · have h1 := mul_mem (mul_mem (inv_mem hkL) (mem_inf.mp (hAR ha)).2) hkL
      rwa [show k⁻¹ * (k * a * k⁻¹) * k = a by group] at h1
    · have h1 := hAx _ ha
      calc a * t = k⁻¹ * ((k * a * k⁻¹) * x) * k := by rw [← hk]; group
        _ = k⁻¹ * (x * (k * a * k⁻¹)) * k := by rw [h1]
        _ = t * a := by rw [← hk]; group
  have hA'2 : IsPGroup 2 A' := IsPGroup.of_card (n := 2) (by
    rw [hA'def, card_conjugate_eq_card, hA4]
    norm_num)
  have hRX : IsSylowOf 2 (S ⊓ L) (L ⊓ centralizer ({t} : Set G)) :=
    h.R_sylow.of_le (le_inf inf_le_right fun ρ hρ =>
      mem_centralizer_singleton_iff.mpr (h.tZ ρ (mem_inf.mp hρ).1)) inf_le_left
  obtain ⟨c, hcX, hc⟩ := exists_conj_le_of_isSylowOf hRX hA'X hA'2
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hcX).2
  set g := k * c with hg
  have hgx : g⁻¹ * x * g = t := by
    calc g⁻¹ * x * g = c⁻¹ * (k⁻¹ * x * k) * c := by rw [hg]; group
      _ = c⁻¹ * (t * c) := by rw [hk, mul_assoc]
      _ = t := by rw [← hct]; group
  have ht₁ : g⁻¹ * t * g ∈ S ⊓ L := by
    have h1 := hc (k⁻¹ * t * k) (by
      rw [hA'def, mem_conjugate_iff, show k * (k⁻¹ * t * k) * k⁻¹ = t by group]
      exact (mem_kleinFour_iff hx2 ht2 hxtc).mpr (Or.inr (Or.inr (Or.inl rfl))))
    rwa [show c⁻¹ * (k⁻¹ * t * k) * c = g⁻¹ * t * g by rw [hg]; group] at h1
  have ht₁2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]
    group
  have ht₁1 : g⁻¹ * t * g ≠ 1 := fun h1 => h.t_ne_one (by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have ht₁t : g⁻¹ * t * g ≠ t := fun h1 => hxt (by
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hgx, h1]
      _ = t := by group)
  obtain ⟨d₀, hd₀, hd₀c⟩ := h.exists_conj_mul_t_R hna ht₁ ht₁2 ht₁1 ht₁t
  have hd₀t : d₀ * t = t * d₀ := h.tZ d₀ (mem_inf.mp hd₀).1
  have hgt : g * t * g⁻¹ = x := by
    calc g * t * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hgx]
      _ = x := by group
  have hgL : g ∈ L := mul_mem hkL (mem_inf.mp hcX).1
  refine ⟨g * d₀ * g⁻¹, mul_mem (mul_mem hgL (mem_inf.mp hd₀).2) (inv_mem hgL), ?_, ?_⟩
  · calc g * d₀ * g⁻¹ * x * (g * d₀ * g⁻¹)⁻¹ = g * (d₀ * (g⁻¹ * x * g) * d₀⁻¹) * g⁻¹ := by
          group
      _ = g * (d₀ * t * d₀⁻¹) * g⁻¹ := by rw [hgx]
      _ = g * t * g⁻¹ := by rw [hd₀t, mul_inv_cancel_right]
      _ = x := hgt
  · calc g * d₀ * g⁻¹ * t * (g * d₀ * g⁻¹)⁻¹ = g * (d₀ * (g⁻¹ * t * g) * d₀⁻¹) * g⁻¹ := by
          group
      _ = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by rw [hd₀c]
      _ = (g * t * g⁻¹) * t := by group
      _ = x * t := by rw [hgt]

theorem exists_three_cycle_L512 (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {a : G}
    (ha : a ∈ S ⊓ L) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t) :
    ∃ n ∈ L, n * t * n⁻¹ = a ∧ n * a * n⁻¹ = a * t := by
  have ht2 := h.t_mul_self
  have hatc : a * t = t * a := h.tZ a (mem_inf.mp ha).1
  obtain ⟨y, hyL, hya, hyt⟩ := h.exists_mem_L_conj_t_of_noncentral hna ha ha2 ha1 hat
  have hb : a * t ∈ S ⊓ L := mul_mem ha h.tR
  have hb2 : a * t * (a * t) = 1 := by
    rw [show a * t * (a * t) = a * (t * a) * t by group, ← hatc,
      show a * (a * t) * t = (a * a) * (t * t) by group, ha2, ht2, one_mul]
  have hb1 : a * t ≠ 1 := fun h1 => hat (by
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left ht2])
  have hbt : a * t ≠ t := fun h1 => ha1 (by simpa using h1)
  obtain ⟨y', hy'L, hy'b, hy't⟩ := h.exists_mem_L_conj_t_of_noncentral hna hb hb2 hb1 hbt
  refine ⟨y * y', mul_mem hyL hy'L, ?_, ?_⟩
  · have h1 : y' * t * y'⁻¹ = a := by rw [hy't, mul_assoc, ht2, mul_one]
    calc y * y' * t * (y * y')⁻¹ = y * (y' * t * y'⁻¹) * y⁻¹ := by group
      _ = a := by rw [h1, hya]
  · have h1 : y' * a * y'⁻¹ = t := by
      calc y' * a * y'⁻¹ = (y' * (a * t) * y'⁻¹) * (y' * t * y'⁻¹) := by
            rw [show y' * (a * t) * y'⁻¹ * (y' * t * y'⁻¹) = y' * (a * (t * t)) * y'⁻¹ by group,
              ht2, mul_one]
        _ = a * t * (a * t * t) := by rw [hy'b, hy't]
        _ = t := by rw [mul_assoc a t t, ht2, mul_one, hatc, mul_assoc, ha2, mul_one]
    calc y * y' * a * (y * y')⁻¹ = y * (y' * a * y'⁻¹) * y⁻¹ := by group
      _ = a * t := by rw [h1, hyt]

theorem exists_odd_three_cycle_L512 (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {a : G}
    (ha : a ∈ S ⊓ L) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPQ : P ≤ Q) (hPa : ∀ p ∈ P, p * a = a * p)
    (hPt : ∀ p ∈ P, p * t = t * p) :
    ∃ h₁ ∈ L, h₁ * t * h₁⁻¹ = a ∧ h₁ * a * h₁⁻¹ = a * t ∧ (∀ p ∈ P, h₁ * p = p * h₁) ∧
      Odd (orderOf h₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε⟩ := h.quotient_simple.2
  have ht2 := h.t_mul_self
  have hatc : a * t = t * a := h.tZ a (mem_inf.mp ha).1
  obtain ⟨n, hnL, hnt, hna'⟩ := h.exists_three_cycle_L512 hna ha ha2 ha1 hat
  have hPN : P ≤ normalizer (L : Set G) := fun p hp => h.S_le (h.QS (hPQ hp))
  have hP1 : ∀ p ∈ P, actG L ε p = 1 := fun p hp =>
    (h.actG_eq_one_iff_mem_Q ε (h.QS (hPQ hp))).mpr (hPQ hp)
  have hna2 : n * a = a * t * n := by
    calc n * a = n * a * n⁻¹ * n := by group
      _ = a * t * n := by rw [hna']
  have hnt2 : n * t = a * n := by
    calc n * t = n * t * n⁻¹ * n := by group
      _ = a * n := by rw [hnt]
  set N := oddCoreIn L ⊓ (centralizer ({a} : Set G) ⊓ centralizer ({t} : Set G)) with hN
  have hNodd : ¬ 2 ∣ Nat.card N := fun h2 => by
    have h3 := Subgroup.card_dvd_of_le (inf_le_left : N ≤ oddCoreIn L)
    have h4 := Nat.odd_iff.mp (odd_card_oddCoreIn L)
    have h5 := dvd_trans h2 h3
    omega
  have hNn : ∀ p ∈ P, ∀ o ∈ N, p * o * p⁻¹ ∈ N := by
    intro p hp o ho
    have ho1 := (mem_inf.mp ho).1
    have hoa := mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp ho).2).1
    have hot := mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp ho).2).2
    have hpa := hPa p hp
    have hpt := hPt p hp
    have hpa' : p⁻¹ * a = a * p⁻¹ := (Commute.inv_left hpa).eq
    have hpt' : p⁻¹ * t = t * p⁻¹ := (Commute.inv_left hpt).eq
    refine mem_inf.mpr ⟨conj_mem_oddCoreIn ε (hPN hp) ho1, mem_inf.mpr
      ⟨mem_centralizer_singleton_iff.mpr ?_, mem_centralizer_singleton_iff.mpr ?_⟩⟩
    · calc p * o * p⁻¹ * a = p * o * (p⁻¹ * a) := by group
        _ = p * (o * a) * p⁻¹ := by rw [hpa']; group
        _ = (p * a) * o * p⁻¹ := by rw [hoa]; group
        _ = a * (p * o * p⁻¹) := by rw [hpa]; group
    · calc p * o * p⁻¹ * t = p * o * (p⁻¹ * t) := by group
        _ = p * (o * t) * p⁻¹ := by rw [hpt']; group
        _ = (p * t) * o * p⁻¹ := by rw [hot]; group
        _ = t * (p * o * p⁻¹) := by rw [hpt]; group
  have hy : ∀ p ∈ P, n⁻¹ * (p * n * p⁻¹) ∈ N := by
    intro p hp
    have hpnL : p * n * p⁻¹ ∈ L := (mem_normalizer_iff.mp (hPN hp) n).mp hnL
    have hpa := hPa p hp
    have hpt := hPt p hp
    have hpa' : p⁻¹ * a = a * p⁻¹ := (Commute.inv_left hpa).eq
    have hpt' : p⁻¹ * t = t * p⁻¹ := (Commute.inv_left hpt).eq
    have hpat : p * (a * t) = a * t * p := by
      rw [← mul_assoc, hpa, mul_assoc, hpt, mul_assoc]
    refine mem_inf.mpr ⟨?_, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      mem_centralizer_singleton_iff.mpr ?_⟩⟩
    · have h1 := actG_psi ε (hPN hp) ⟨n, hnL⟩
      rw [hP1 p hp, MulAut.one_apply] at h1
      exact (psi_eq_iff ε ⟨n, hnL⟩ ⟨p * n * p⁻¹, hpnL⟩).mp h1
    · have hc : p * n * p⁻¹ * a = a * t * (p * n * p⁻¹) := by
        calc p * n * p⁻¹ * a = p * n * (p⁻¹ * a) := by group
          _ = p * (n * a) * p⁻¹ := by rw [hpa']; group
          _ = p * (a * t) * n * p⁻¹ := by rw [hna2]; group
          _ = a * t * (p * n * p⁻¹) := by rw [hpat]; group
      have hn1 : n⁻¹ * (a * t) * n = a := by rw [← hna']; group
      calc n⁻¹ * (p * n * p⁻¹) * a = n⁻¹ * (p * n * p⁻¹ * a) := by group
        _ = n⁻¹ * (a * t) * n * (n⁻¹ * (p * n * p⁻¹)) := by rw [hc]; group
        _ = a * (n⁻¹ * (p * n * p⁻¹)) := by rw [hn1]
    · have hc : p * n * p⁻¹ * t = a * (p * n * p⁻¹) := by
        calc p * n * p⁻¹ * t = p * n * (p⁻¹ * t) := by group
          _ = p * (n * t) * p⁻¹ := by rw [hpt']; group
          _ = p * a * n * p⁻¹ := by rw [hnt2]; group
          _ = a * (p * n * p⁻¹) := by rw [hpa]; group
      have hn1 : n⁻¹ * a * n = t := by rw [← hnt]; group
      calc n⁻¹ * (p * n * p⁻¹) * t = n⁻¹ * (p * n * p⁻¹ * t) := by group
        _ = n⁻¹ * a * n * (n⁻¹ * (p * n * p⁻¹)) := by rw [hc]; group
        _ = t * (n⁻¹ * (p * n * p⁻¹)) := by rw [hn1]
  obtain ⟨n', hn'N, hn'P⟩ := exists_commute_of_coprime hP2 hNodd hNn hy
  have hcL : n⁻¹ * n' ∈ L := mem_of_mem_oddCoreIn (mem_inf.mp hn'N).1
  have hca := mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hn'N).2).1
  have hct := mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hn'N).2).2
  have hn'L : n' ∈ L := by
    rw [show n' = n * (n⁻¹ * n') by group]
    exact mul_mem hnL hcL
  have hn't : n' * t * n'⁻¹ = a := by
    calc n' * t * n'⁻¹ = n * ((n⁻¹ * n') * t) * (n⁻¹ * n')⁻¹ * n⁻¹ := by group
      _ = n * t * n⁻¹ := by rw [hct]; group
      _ = a := hnt
  have hn'a : n' * a * n'⁻¹ = a * t := by
    calc n' * a * n'⁻¹ = n * ((n⁻¹ * n') * a) * (n⁻¹ * n')⁻¹ * n⁻¹ := by group
      _ = n * a * n⁻¹ := by rw [hca]; group
      _ = a * t := hna'
  have hn'at : n' * (a * t) * n'⁻¹ = t := by
    calc n' * (a * t) * n'⁻¹ = (n' * a * n'⁻¹) * (n' * t * n'⁻¹) := by group
      _ = t := by rw [hn'a, hn't, hatc, mul_assoc, ha2, mul_one]
  have h3t : n' ^ 3 * t * (n' ^ 3)⁻¹ = t := by
    calc n' ^ 3 * t * (n' ^ 3)⁻¹ = n' * (n' * (n' * t * n'⁻¹) * n'⁻¹) * n'⁻¹ := by
          rw [pow_succ, sq]; group
      _ = t := by rw [hn't, hn'a, hn'at]
  have h3a : n' ^ 3 * a * (n' ^ 3)⁻¹ = a := by
    calc n' ^ 3 * a * (n' ^ 3)⁻¹ = n' * (n' * (n' * a * n'⁻¹) * n'⁻¹) * n'⁻¹ := by
          rw [pow_succ, sq]; group
      _ = a := by rw [hn'a, hn'at, hn't]
  have h3j : ∀ j : ℕ, n' ^ (3 * j) * t * (n' ^ (3 * j))⁻¹ = t ∧
      n' ^ (3 * j) * a * (n' ^ (3 * j))⁻¹ = a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [mul_add, mul_one, pow_add]
      constructor
      · calc n' ^ (3 * j) * n' ^ 3 * t * (n' ^ (3 * j) * n' ^ 3)⁻¹ =
            n' ^ (3 * j) * (n' ^ 3 * t * (n' ^ 3)⁻¹) * (n' ^ (3 * j))⁻¹ := by group
          _ = t := by rw [h3t, ih.1]
      · calc n' ^ (3 * j) * n' ^ 3 * a * (n' ^ (3 * j) * n' ^ 3)⁻¹ =
            n' ^ (3 * j) * (n' ^ 3 * a * (n' ^ 3)⁻¹) * (n' ^ (3 * j))⁻¹ := by group
          _ = a := by rw [h3a, ih.2]
  obtain ⟨m, hm, k, hk⟩ := exists_odd_pow_two_element n'
  have h4k : ∀ r : ℕ, ∃ j : ℕ, 4 ^ r = 3 * j + 1 := by
    intro r
    induction r with
    | zero => exact ⟨0, rfl⟩
    | succ r ih =>
      obtain ⟨j, hj⟩ := ih
      exact ⟨4 * j + 1, by rw [pow_succ, hj]; ring⟩
  obtain ⟨j, hj⟩ := h4k k
  refine ⟨n' ^ 4 ^ k, pow_mem hn'L _, ?_, ?_, fun p hp => ?_, ?_⟩
  · rw [hj, pow_succ', show n' * n' ^ (3 * j) * t * (n' * n' ^ (3 * j))⁻¹ =
      n' * (n' ^ (3 * j) * t * (n' ^ (3 * j))⁻¹) * n'⁻¹ by group, (h3j j).1, hn't]
  · rw [hj, pow_succ', show n' * n' ^ (3 * j) * a * (n' * n' ^ (3 * j))⁻¹ =
      n' * (n' ^ (3 * j) * a * (n' ^ (3 * j))⁻¹) * n'⁻¹ by group, (h3j j).2, hn'a]
  · exact (Commute.pow_left (hn'P p hp).symm _).eq
  · have h1 : (n' ^ 4 ^ k) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, show (4 : ℕ) ^ k = 2 ^ k * 2 ^ k by
        rw [← mul_pow]; norm_num, pow_mul, hk, one_pow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)

end Sec5

end CFSG.ComponentClassification.Foote5
