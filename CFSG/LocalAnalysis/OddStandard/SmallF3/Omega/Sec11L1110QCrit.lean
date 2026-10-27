module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {E : Type} [Group E] {z : E} {Q1 Q2 : Subgroup E}

private lemma sq_eq_one_of_mem_zpowers {x : E} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x * x = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz
  have hpow : (z ^ k)⁻¹ = z ^ k := by rw [← inv_zpow z k, hzinv]
  calc z ^ k * z ^ k = z ^ k * (z ^ k)⁻¹ := by rw [hpow]
    _ = 1 := mul_inv_cancel _

private lemma zpow_eq_one_or_eq_z (hz : z * z = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have hz2 : z ^ (2 : ℤ) = 1 := by
    show z ^ ((2 : ℕ) : ℤ) = 1
    rw [zpow_natCast, pow_two, hz]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, hz2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

private lemma mem_zpowers_eq_one_or_eq_z (hz : z * z = 1) {x : E} (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact zpow_eq_one_or_eq_z hz k

private lemma natCard_zpowers_eq_two (P : Sec11Q8Pair z Q1 Q2) : Nat.card (zpowers z) = 2 := by
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact P.z_sq
  have h : orderOf z = 2 := orderOf_eq_prime hz2 P.z_ne
  rw [Nat.card_zpowers, h]

private lemma exists_notMem_zpowers₁ (P : Sec11Q8Pair z Q1 Q2) :
    ∃ a ∈ Q1, a ∉ zpowers z := by
  by_contra h
  push Not at h
  have hle : Q1 ≤ zpowers z := fun a ha => h a ha
  haveI : Finite ↥(zpowers z) := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_zpowers_eq_two P]
    norm_num
  have hcard : Nat.card ↥Q1 ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hle
  rw [P.card1, natCard_zpowers_eq_two P] at hcard
  exact absurd hcard (by norm_num)

private lemma sq_eq_z_of_mem₁ (P : Sec11Q8Pair z Q1 Q2) {a : E} (ha : a ∈ Q1)
    (hna : a ∉ zpowers z) : a * a = z := by
  have hmem : a * a ∈ zpowers z := (P.elem1 a ha a ha).2
  rcases mem_zpowers_eq_one_or_eq_z P.z_sq hmem with h1 | hz
  · exact absurd (P.invol1 a ha h1) hna
  · exact hz

theorem Sec11Q8Pair.swap_crit (P : Sec11Q8Pair z Q1 Q2) {s : E} (hsz : s * z * s⁻¹ = z)
    (hs : ∀ a ∈ Q1, s * a * s⁻¹ ∈ Q2) :
    ∃ q ∈ Q1 ⊔ Q2, q * (s * q⁻¹ * s⁻¹) * (q * (s * q⁻¹ * s⁻¹)) = 1 ∧
      q * (s * q⁻¹ * s⁻¹) ∉ zpowers z := by
  obtain ⟨a, ha1, hna⟩ := exists_notMem_zpowers₁ P
  have haa : a * a = z := sq_eq_z_of_mem₁ P ha1 hna
  let a' := s * a * s⁻¹
  have ha'2 : a' ∈ Q2 := hs a ha1
  have hna' : a' ∉ zpowers z := by
    intro hmem
    have hsq : a' * a' = 1 := sq_eq_one_of_mem_zpowers P.z_sq hmem
    have haa1 : a * a = 1 := by
      have haeq : a = s⁻¹ * a' * s := by
        show a = s⁻¹ * (s * a * s⁻¹) * s
        group
      rw [haeq]
      calc (s⁻¹ * a' * s) * (s⁻¹ * a' * s) = s⁻¹ * (a' * a') * s := by group
        _ = 1 := by rw [hsq]; group
    exact P.z_ne (by rw [← haa, haa1])
  have ha'a' : a' * a' = z := sq_eq_z_of_mem₁ P.symm ha'2 hna'
  have hinv : s * a⁻¹ * s⁻¹ = a'⁻¹ := by
    show s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹
    group
  refine ⟨a, Subgroup.mem_sup_left ha1, ?_, ?_⟩
  · rw [hinv]
    have hcomm : a * a'⁻¹ = a'⁻¹ * a := P.comm a ha1 a'⁻¹ (inv_mem ha'2)
    calc (a * a'⁻¹) * (a * a'⁻¹) = (a * a) * (a'⁻¹ * a'⁻¹) := by
          rw [show (a * a'⁻¹) * (a * a'⁻¹) = a * (a'⁻¹ * a) * a'⁻¹ by group,
            ← hcomm]
          group
      _ = z * (a' * a')⁻¹ := by rw [haa, ← mul_inv_rev]
      _ = z * z⁻¹ := by rw [ha'a']
      _ = 1 := mul_inv_cancel z
  · rw [hinv]
    intro hmem
    have hprod : a * a'⁻¹ ∈ Q2 := (Subgroup.zpowers_le.mpr P.z_mem2) hmem
    have haQ2 : a ∈ Q2 := by
      have : a = (a * a'⁻¹) * a' := by group
      rw [this]
      exact mul_mem hprod ha'2
    exact hna (P.inf a ha1 haQ2)

theorem Sec11Q8Pair.double_crit (P : Sec11Q8Pair z Q1 Q2) {s : E} (hsz : s * z * s⁻¹ = z)
    (h1 : ∀ a ∈ Q1, s * a * s⁻¹ ∈ Q1) (h2 : ∀ a ∈ Q2, s * a * s⁻¹ ∈ Q2)
    (n1 : ¬ ActsTrivModZ z s Q1) (n2 : ¬ ActsTrivModZ z s Q2) :
    ∃ q ∈ Q1 ⊔ Q2, q * (s * q⁻¹ * s⁻¹) * (q * (s * q⁻¹ * s⁻¹)) = 1 ∧
      q * (s * q⁻¹ * s⁻¹) ∉ zpowers z := by
  simp only [ActsTrivModZ] at n1 n2
  push Not at n1 n2
  obtain ⟨a1, ha1, hn1⟩ := n1
  obtain ⟨a2, ha2, hn2⟩ := n2
  let σ1 := s * a1 * s⁻¹
  let σ2 := s * a2 * s⁻¹
  let c1 := a1 * σ1⁻¹
  let c2 := a2 * σ2⁻¹
  let q := a1 * a2
  have hσ1 : σ1 ∈ Q1 := h1 a1 ha1
  have hσ2 : σ2 ∈ Q2 := h2 a2 ha2
  have hc1mem : c1 ∈ Q1 := mul_mem ha1 (inv_mem hσ1)
  have hc2mem : c2 ∈ Q2 := mul_mem ha2 (inv_mem hσ2)
  have hc1 : c1 ∉ zpowers z := by
    intro hmem
    apply hn1
    have hcinv : c1⁻¹ = s * a1 * s⁻¹ * a1⁻¹ := by
      simp only [c1, σ1]
      group
    rw [← hcinv]
    exact inv_mem hmem
  have hc2 : c2 ∉ zpowers z := by
    intro hmem
    apply hn2
    have hcinv : c2⁻¹ = s * a2 * s⁻¹ * a2⁻¹ := by
      simp only [c2, σ2]
      group
    rw [← hcinv]
    exact inv_mem hmem
  have hc1sq : c1 * c1 = z := sq_eq_z_of_mem₁ P hc1mem hc1
  have hc2sq : c2 * c2 = z := sq_eq_z_of_mem₁ P.symm hc2mem hc2
  have hqinv : s * q⁻¹ * s⁻¹ = σ2⁻¹ * σ1⁻¹ := by
    simp only [q]
    calc s * (a1 * a2)⁻¹ * s⁻¹ = (s * a2 * s⁻¹)⁻¹ * (s * a1 * s⁻¹)⁻¹ := by
          group
      _ = σ2⁻¹ * σ1⁻¹ := by simp only [σ1, σ2]
  have hca : σ1⁻¹ * a2 = a2 * σ1⁻¹ := P.comm σ1⁻¹ (inv_mem hσ1) a2 ha2
  have hcb : σ1⁻¹ * σ2⁻¹ = σ2⁻¹ * σ1⁻¹ :=
    P.comm σ1⁻¹ (inv_mem hσ1) σ2⁻¹ (inv_mem hσ2)
  have hcq : q * (s * q⁻¹ * s⁻¹) = c1 * c2 := by
    rw [hqinv]
    simp only [q, c1, c2]
    calc a1 * a2 * (σ2⁻¹ * σ1⁻¹) = a1 * (a2 * (σ2⁻¹ * σ1⁻¹)) := by group
      _ = a1 * (a2 * (σ1⁻¹ * σ2⁻¹)) := by rw [← hcb]
      _ = a1 * (σ1⁻¹ * (a2 * σ2⁻¹)) := by
            rw [show a2 * (σ1⁻¹ * σ2⁻¹) = σ1⁻¹ * (a2 * σ2⁻¹) by
              rw [← mul_assoc, ← mul_assoc, ← hca]]
      _ = a1 * σ1⁻¹ * (a2 * σ2⁻¹) := by group
  have hqmem : q ∈ Q1 ⊔ Q2 :=
    mul_mem (Subgroup.mem_sup_left ha1) (Subgroup.mem_sup_right ha2)
  refine ⟨q, hqmem, ?_, ?_⟩
  · rw [hcq]
    have hcomm12 : c1 * c2 = c2 * c1 := P.comm c1 hc1mem c2 hc2mem
    calc (c1 * c2) * (c1 * c2) = (c1 * c1) * (c2 * c2) := by
          rw [show (c1 * c2) * (c1 * c2) = c1 * (c2 * c1) * c2 by group,
            ← hcomm12]
          group
      _ = z * z := by rw [hc1sq, hc2sq]
      _ = 1 := P.z_sq
  · rw [hcq]
    intro hmem
    apply hc2
    have hprod : c1 * c2 ∈ Q1 := (Subgroup.zpowers_le.mpr P.z_mem1) hmem
    have hc2Q1 : c2 ∈ Q1 := by
      have : c2 = c1⁻¹ * (c1 * c2) := by group
      rw [this]
      exact mul_mem (inv_mem hc1mem) hprod
    exact P.inf c2 hc2Q1 hc2mem

end CFSG.OddStandard.SmallF3.Omega
