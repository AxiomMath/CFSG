module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrH

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private theorem fzc_sy3_sp_sP (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {s : G}
    (hs_mem : s = a ∨ s = b ∨ s = a * b) : s ∈ P := by
  rcases hs_mem with rfl | rfl | rfl
  · exact hs.chain.2.1 hs.a_mem
  · exact hs.b_mem
  · exact mul_mem (hs.chain.2.1 hs.a_mem) hs.b_mem

private theorem fzc_sy3_sp_sqWp (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {s : G}
    (hs_mem : s = a ∨ s = b ∨ s = a * b) : s * s ∈ Wp := by
  rcases hs_mem with rfl | rfl | rfl
  · exact hs.sq_mem.1
  · exact hs.sq_mem.2.1
  · exact hs.sq_mem.2.2.2.1

private theorem fzc_sy3_sp_nonZ (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {s s' : G}
    (hs_mem : s = a ∨ s = b ∨ s = a * b)
    (hs'_mem : s' = a ∨ s' = b ∨ s' = a * b) (hne : s ≠ s') :
    s * s * (s' * s')⁻¹ ∉ fourGrp x₁ x₂ := by
  rcases hs_mem with rfl | rfl | rfl <;> rcases hs'_mem with rfl | rfl | rfl
  · exact absurd rfl hne
  · simpa [pow_two] using hs.sp_ab
  · simpa [pow_two] using hs.sp_a
  · intro h
    apply hs.sp_ab
    simpa [pow_two, mul_inv_rev] using inv_mem h
  · exact absurd rfl hne
  · simpa [pow_two] using hs.sp_b
  · intro h
    apply hs.sp_a
    simpa [pow_two, mul_inv_rev] using inv_mem h
  · intro h
    apply hs.sp_b
    simpa [pow_two, mul_inv_rev] using inv_mem h
  · exact absurd rfl hne

private theorem fzc_sy3_sp_P_Wp (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ p ∈ P, ∀ w ∈ Wp, p * w * p⁻¹ * w⁻¹ ∈ fourGrp x₁ x₂ := by
  intro p hp w hw
  have ht2 : t * t = 1 := by simpa [pow_two] using hs.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rcases (Wp_mem hs).mp hw with hwE | htwE
  · exact hs.P_E p hp w hwE
  · set e := t * w with he_def
    have hweq : w = e * t := by rw [he_def]; exact fzc_eq_mul_t hs htwE
    have hwinv : w⁻¹ = t * e⁻¹ := by rw [hweq, mul_inv_rev, htinv]
    have hz1 : p * e * p⁻¹ * e⁻¹ ∈ fourGrp x₁ x₂ := hs.P_E p hp e htwE
    have hz2 : p * t * p⁻¹ * t ∈ fourGrp x₁ x₂ := hs.P_t p hp
    have hid : p * w * p⁻¹ * w⁻¹
        = (p * e * p⁻¹ * e⁻¹) * (e * (p * t * p⁻¹ * t) * e⁻¹) := by
      rw [hwinv, hweq]
      group
    have hconj : e * (p * t * p⁻¹ * t) * e⁻¹ = p * t * p⁻¹ * t := by
      rw [hs.E_comm e htwE (p * t * p⁻¹ * t) (hs.Z_le_E hz2)]
      group
    rw [hid, hconj]
    exact mul_mem hz1 hz2

private theorem fzc_sy3_sp_shift (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ p ∈ P, ∀ w ∈ Wp, w * (p * w * p⁻¹) ∈ fourGrp x₁ x₂ := by
  intro p hp w hw
  have hz : p * w * p⁻¹ * w⁻¹ ∈ fourGrp x₁ x₂ := fzc_sy3_sp_P_Wp hs p hp w hw
  have hzW : p * w * p⁻¹ * w⁻¹ ∈ Wp := (hs.Z_le_E.trans hs.E_le_Wp) hz
  have hpeq : p * w * p⁻¹ = (p * w * p⁻¹ * w⁻¹) * w := by group
  have hww : w * w ∈ fourGrp x₁ x₂ := by
    simpa [pow_two] using hs.Wp_sq w hw
  rw [hpeq, ← mul_assoc, Wp_comm hs w hw (p * w * p⁻¹ * w⁻¹) hzW, mul_assoc]
  exact mul_mem hz hww

private theorem fzc_sy3_sp_aux (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {p p' : G}
    (hp : p ∈ P) (hp' : p' ∈ P) (hpp : p * p ∈ Wp) (hp'p' : p' * p' ∈ Wp)
    (hne : p * p * (p' * p')⁻¹ ∉ fourGrp x₁ x₂) :
    ∀ w ∈ Wp, ∀ w' ∈ Wp,
      (w * p) ^ 2 * ((w' * p') ^ 2)⁻¹ ∉ fourGrp x₁ x₂ := by
  intro w hw w' hw'
  set m := w * (p * w * p⁻¹) with hm_def
  set m' := w' * (p' * w' * p'⁻¹) with hm'_def
  have hZle : fourGrp x₁ x₂ ≤ Wp := hs.Z_le_E.trans hs.E_le_Wp
  have hmZ : m ∈ fourGrp x₁ x₂ := fzc_sy3_sp_shift hs p hp w hw
  have hm'Z : m' ∈ fourGrp x₁ x₂ := fzc_sy3_sp_shift hs p' hp' w' hw'
  have hmW : m ∈ Wp := hZle hmZ
  have hm'W : m' ∈ Wp := hZle hm'Z
  have hmm'inv : m * m'⁻¹ ∈ fourGrp x₁ x₂ := mul_mem hmZ (inv_mem hm'Z)
  have hmq : (w * p) ^ 2 = m * (p * p) := by
    rw [hm_def, pow_two]
    group
  have hm'q' : (w' * p') ^ 2 = m' * (p' * p') := by
    rw [hm'_def, pow_two]
    group
  have hkey : (m * (p * p)) * (m' * (p' * p'))⁻¹
      = (m * m'⁻¹) * ((p * p) * (p' * p')⁻¹) := by
    have hqinvW : (p * p) * (p' * p')⁻¹ ∈ Wp := mul_mem hpp (inv_mem hp'p')
    have hcomm2 : ((p * p) * (p' * p')⁻¹) * m'⁻¹
        = m'⁻¹ * ((p * p) * (p' * p')⁻¹) :=
      Wp_comm hs ((p * p) * (p' * p')⁻¹) hqinvW m'⁻¹ (inv_mem hm'W)
    calc (m * (p * p)) * (m' * (p' * p'))⁻¹
        = (m * (p * p)) * ((p' * p')⁻¹ * m'⁻¹) := by rw [mul_inv_rev]
      _ = m * ((p * p) * (p' * p')⁻¹) * m'⁻¹ := by group
      _ = m * (((p * p) * (p' * p')⁻¹) * m'⁻¹) := by group
      _ = m * (m'⁻¹ * ((p * p) * (p' * p')⁻¹)) := by rw [hcomm2]
      _ = (m * m'⁻¹) * ((p * p) * (p' * p')⁻¹) := by group
  intro hA
  apply hne
  have hq_eq : (p * p) * (p' * p')⁻¹
      = (m * m'⁻¹)⁻¹ * ((w * p) ^ 2 * ((w' * p') ^ 2)⁻¹) := by
    rw [hmq, hm'q', hkey]
    group
  rw [hq_eq]
  exact mul_mem (inv_mem hmm'inv) hA

private theorem fzc_sy3_sp_decomp (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G}
    (hg : g ∈ P) (hgW : g ∉ Wp) :
    ∃ w ∈ Wp, ∃ s : G, (s = a ∨ s = b ∨ s = a * b) ∧ g = w * s := by
  obtain ⟨f, hfF, hf | hf⟩ := (hs.P_mem).mp hg
  · obtain ⟨w, hwW, hw | hw⟩ := (hs.F_mem).mp hfF
    · exact absurd (by rw [hf, hw]; exact hwW) hgW
    · exact ⟨w, hwW, a, Or.inl rfl, by rw [hf, hw]⟩
  · obtain ⟨w, hwW, hw | hw⟩ := (hs.F_mem).mp hfF
    · exact ⟨w, hwW, b, Or.inr (Or.inl rfl), by rw [hf, hw]⟩
    · exact ⟨w, hwW, a * b, Or.inr (Or.inr rfl), by rw [hf, hw]; group⟩

theorem SP (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ x ∈ P, ∀ y ∈ P, x ∉ Wp → y ∉ Wp → x * y⁻¹ ∉ Wp →
      x ^ 2 * (y ^ 2)⁻¹ ∉ fourGrp x₁ x₂ := by
  intro x hx y hy hxW hyW hxy
  obtain ⟨wx, hwxW, sx, hsx, rfl⟩ := fzc_sy3_sp_decomp hs hx hxW
  obtain ⟨wy, hwyW, sy, hsy, rfl⟩ := fzc_sy3_sp_decomp hs hy hyW
  by_cases hss : sx = sy
  · exfalso
    apply hxy
    rw [hss]
    have h1 : (wx * sy) * (wy * sy)⁻¹ = wx * wy⁻¹ := by group
    rw [h1]
    exact mul_mem hwxW (inv_mem hwyW)
  · exact fzc_sy3_sp_aux hs (fzc_sy3_sp_sP hs hsx) (fzc_sy3_sp_sP hs hsy)
      (fzc_sy3_sp_sqWp hs hsx) (fzc_sy3_sp_sqWp hs hsy)
      (fzc_sy3_sp_nonZ hs hsx hsy hss) wx hwxW wy hwyW

theorem c_act (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    (∀ y : G, c⁻¹ * y ∈ Wp → ∀ e ∈ baseGrp x₁ x₂, y⁻¹ * e * y = c⁻¹ * e * c) ∧
      c⁻¹ * x₁ * c = x₂ ∧ c⁻¹ * x₂ * c = x₁ := by
  have hcU : c ∈ U := hs.chain.2.2.2.2.1 hs.c_mem
  have hcUinv : c⁻¹ ∈ U := inv_mem hcU
  refine ⟨?_, ?_, ?_⟩
  · intro y hy e he
    set w := c⁻¹ * y with hw_def
    have hw : w ∈ Wp := hy
    have hy_eq : y = c * w := by rw [hw_def]; group
    have huE : c⁻¹ * e * c ∈ baseGrp x₁ x₂ := by
      have h := hs.nrm_E c⁻¹ hcUinv e he
      simpa using h
    have huWp : c⁻¹ * e * c ∈ Wp := hs.E_le_Wp huE
    have hcomm : w⁻¹ * (c⁻¹ * e * c) = (c⁻¹ * e * c) * w⁻¹ :=
      Wp_comm hs w⁻¹ (inv_mem hw) (c⁻¹ * e * c) huWp
    rw [hy_eq]
    calc (c * w)⁻¹ * e * (c * w)
        = w⁻¹ * (c⁻¹ * e * c) * w := by group
      _ = (c⁻¹ * e * c) * w⁻¹ * w := by rw [hcomm]
      _ = c⁻¹ * e * c := by group
  · calc c⁻¹ * x₁ * c = c⁻¹ * (c * x₂ * c⁻¹) * c := by rw [hs.c_x₂]
      _ = x₂ := by group
  · calc c⁻¹ * x₂ * c = c⁻¹ * (c * x₁ * c⁻¹) * c := by rw [hs.c_x₁]
      _ = x₁ := by group

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
