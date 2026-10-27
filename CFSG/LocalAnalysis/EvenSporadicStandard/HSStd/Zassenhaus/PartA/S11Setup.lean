module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

set_option linter.unusedSectionVars false

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem s11_exists_mul_of_mem_sup {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
      _ = a * a' * (b * b') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := hc a ha b hb
    calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [this]
      _ = a⁻¹ * b⁻¹ := by group

theorem s11_oddCoreOf_conj (H : Subgroup G) {g o : G} (hg : g ∈ H)
    (ho : o ∈ Open.fusionOddCoreOf H) : g * o * g⁻¹ ∈ Open.fusionOddCoreOf H := by
  obtain ⟨o', ho', rfl⟩ := ho
  refine ⟨(⟨g, hg⟩ : ↥H) * o' * (⟨g, hg⟩ : ↥H)⁻¹, ?_, rfl⟩
  exact Normal.conj_mem inferInstance o' ho' _

variable (hb : PAB G L t E W z) (a : PA10 L t E z)

include hb a

theorem S11_u_sq : a.u * a.u = 1 := by
  have h2 : orderOf a.u = 2 := a.ub_eq ▸ a.ub_ord
  have := pow_orderOf_eq_one a.u
  rw [h2, pow_two] at this
  exact this

theorem S11_u_L : a.u ∈ L := (a.K₀_le a.u_mem).1

theorem S11_u_y : a.u * a.y = a.y * a.u := mem_Cen.1 (a.K₀_le a.u_mem).2

theorem S11_y_L : a.y ∈ L := a.y_mem.2

theorem S11_L_t : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 hb.t_cent l hl

theorem S11_u_t : a.u * t = t * a.u := S11_L_t hb a _ (S11_u_L hb a)

theorem S11_y_t : a.y * t = t * a.y := S11_L_t hb a _ (S11_y_L hb a)

theorem S11_hZ : ∀ z ∈ center ↥a.L₁, (z : G) ∈ zpowers a.u := by
  intro z hz
  have := a.Z_le ⟨z, hz, rfl⟩
  rwa [a.ub_eq] at this

theorem S11_comm_L₁t : ∀ p ∈ a.L₁, ∀ q ∈ conjSub t a.L₁, p * q = q * p := by
  rintro p hp _ ⟨q, hq, rfl⟩
  exact (a.L₁_comm p hp q hq).eq

theorem S11_inter_le {g : G} (hg : g ∈ a.L₁) (hgt : g ∈ conjSub t a.L₁) : g ∈ zpowers a.u := by
  have hc : (⟨g, hg⟩ : ↥a.L₁) ∈ center ↥a.L₁ := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (S11_comm_L₁t hb a k.1 k.2 g hgt)
  exact S11_hZ hb a _ hc

theorem S11_L₁_u : ∀ l ∈ a.L₁, l * a.u = a.u * l := by
  intro l hl
  have h : l ∈ Cen a.ub := a.L₁_comp.1 hl
  rw [a.ub_eq] at h
  exact mem_Cen.1 h

theorem S11_conj_u : ∀ l ∈ a.L₁, (t * l * t⁻¹) * a.u = a.u * (t * l * t⁻¹) := by
  intro l hl
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right hb.t_mul_t
  have h1 := S11_L₁_u hb a l hl
  have h2 := S11_u_t hb a
  rw [ht']
  calc t * l * t * a.u = t * l * (t * a.u) := by simp only [mul_assoc]
    _ = t * l * (a.u * t) := by rw [h2]
    _ = t * (l * a.u) * t := by simp only [mul_assoc]
    _ = t * (a.u * l) * t := by rw [h1]
    _ = (t * a.u) * l * t := by simp only [mul_assoc]
    _ = (a.u * t) * l * t := by rw [h2]
    _ = a.u * (t * l * t) := by simp only [mul_assoc]

theorem S11_exists_x : ∃ x ∈ a.L₁, orderOf x = 3 ∧ a.y = x * (t * x * t⁻¹) := by
  have ht := hb.t_mul_t
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hu := S11_u_sq hb a
  obtain ⟨a₀, ha₀, b₁, hb₁, hy⟩ :=
    s11_exists_mul_of_mem_sup (S11_comm_L₁t hb a) (a.J_le a.y_J)
  obtain ⟨b₀, hb₀, rfl⟩ := hb₁
  have hB' : (MulAut.conj t).toMonoidHom b₀ = t * b₀ * t⁻¹ := rfl
  rw [hB'] at hy
  set A' : G := t * a₀ * t⁻¹ with hA'
  set B' : G := t * b₀ * t⁻¹ with hB'def
  have hA't : A' ∈ conjSub t a.L₁ := ⟨a₀, ha₀, rfl⟩
  have hB't : B' ∈ conjSub t a.L₁ := ⟨b₀, hb₀, rfl⟩
  have hyt : t * a.y * t⁻¹ = a.y := by
    have := S11_y_t hb a
    rw [← this]; group
  have hconj : t * B' * t⁻¹ = b₀ := by
    rw [hB'def, ht']
    calc t * (t * b₀ * t) * t = (t * t) * b₀ * (t * t) := by simp only [mul_assoc]
      _ = b₀ := by rw [ht]; group
  have hy2 : a.y = A' * b₀ := by
    have : t * a.y * t⁻¹ = A' * (t * B' * t⁻¹) := by
      rw [hy, hA']
      group
    rw [hyt, hconj] at this
    exact this
  have hb₀A' : b₀ * A' = A' * b₀ := S11_comm_L₁t hb a b₀ hb₀ A' hA't
  have ha₀B' : a₀ * B' = b₀ * A' := by rw [← hy, hy2, hb₀A']
  set ζ : G := b₀⁻¹ * a₀ with hζ
  have hζL₁ : ζ ∈ a.L₁ := a.L₁.mul_mem (a.L₁.inv_mem hb₀) ha₀
  have hζeq : ζ = A' * B'⁻¹ := by
    rw [hζ]
    have : a₀ = b₀ * A' * B'⁻¹ := by rw [← ha₀B']; group
    calc b₀⁻¹ * a₀ = b₀⁻¹ * (b₀ * A' * B'⁻¹) := by rw [← this]
      _ = A' * B'⁻¹ := by group
  have hζt : ζ ∈ conjSub t a.L₁ := by
    rw [hζeq]; exact (conjSub t a.L₁).mul_mem hA't ((conjSub t a.L₁).inv_mem hB't)
  have hζu : ζ ∈ zpowers a.u := S11_inter_le hb a hζL₁ hζt
  have hζ2 : ζ * ζ = 1 := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hζu
    rw [← hn, ← zpow_add, ← two_mul, zpow_mul]
    have : a.u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
    rw [this, one_zpow]
  have hζinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ2
  have hζc : ∀ g : G, g * a.u = a.u * g → g * ζ = ζ * g := by
    intro g hg
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hζu
    rw [← hn]
    exact ((show Commute g a.u from hg).zpow_right n).eq
  have hζa₀ : a₀ * ζ = ζ * a₀ := hζc _ (S11_L₁_u hb a a₀ ha₀)
  have hζA' : A' * ζ = ζ * A' := hζc _ (S11_conj_u hb a a₀ ha₀)
  have hζy : a.y * ζ = ζ * a.y := hζc _ (S11_u_y hb a).symm
  have haA' : a₀ * A' = A' * a₀ := S11_comm_L₁t hb a a₀ ha₀ A' hA't
  have hy3 : a.y = a₀ * A' * ζ := by
    have hb₀' : b₀ = a₀ * ζ := by
      rw [← hζinv, hζ]; group
    rw [hy2, hb₀', ← mul_assoc, haA']
  have hy3' : a.y ^ 3 = 1 := by
    have := pow_orderOf_eq_one a.y
    rw [a.y_ord] at this
    exact this
  have hPζ : Commute (a₀ * A') ζ := by
    show a₀ * A' * ζ = ζ * (a₀ * A')
    rw [mul_assoc, hζA', ← mul_assoc, hζa₀]; simp only [mul_assoc]
  have hP3 : (a₀ * A') ^ 3 = ζ := by
    have h1 : (a₀ * A') ^ 3 * ζ ^ 3 = 1 := by
      rw [← hPζ.mul_pow, ← hy3]; exact hy3'
    have h2 : ζ ^ 3 = ζ := by
      rw [pow_succ, pow_two, hζ2, one_mul]
    rw [h2] at h1
    have := mul_eq_one_iff_eq_inv.1 h1
    rw [this, hζinv]
  have ha3 : a₀ ^ 3 * A' ^ 3 = ζ := by
    rw [← hP3, (show Commute a₀ A' from haA').mul_pow]
  have ha3L₁t : a₀ ^ 3 ∈ conjSub t a.L₁ := by
    have : a₀ ^ 3 = ζ * (A' ^ 3)⁻¹ := by
      rw [← ha3]; group
    rw [this]
    exact (conjSub t a.L₁).mul_mem hζt ((conjSub t a.L₁).inv_mem ((conjSub t a.L₁).pow_mem hA't 3))
  have ha3u : a₀ ^ 3 ∈ zpowers a.u := S11_inter_le hb a (a.L₁.pow_mem ha₀ 3) ha3L₁t
  have ha32 : (a₀ ^ 3) * (a₀ ^ 3) = 1 := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 ha3u
    rw [← hn, ← zpow_add, ← two_mul, zpow_mul]
    have : a.u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
    rw [this, one_zpow]
  have hx3 : (a₀ ^ 4) ^ 3 = 1 := by
    have h2 : (a₀ ^ 3) ^ 2 = 1 := by rw [pow_two]; exact ha32
    calc (a₀ ^ 4) ^ 3 = ((a₀ ^ 3) ^ 2) ^ 2 := by rw [← pow_mul, ← pow_mul, ← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  have hxt : a₀ ^ 4 * (t * a₀ ^ 4 * t⁻¹) = a.y := by
    have h1 : t * a₀ ^ 4 * t⁻¹ = A' ^ 4 := (conj_pow).symm
    rw [h1]
    calc a₀ ^ 4 * A' ^ 4 = (a₀ * A') ^ 4 := ((show Commute a₀ A' from haA').mul_pow 4).symm
      _ = (a₀ * A') ^ 3 * (a₀ * A') := pow_succ _ _
      _ = ζ * (a₀ * A') := by rw [hP3]
      _ = (a₀ * A') * ζ := hPζ.eq.symm
      _ = a.y := hy3.symm
  have hne : a₀ ^ 4 ≠ 1 := by
    intro h1
    rw [h1] at hxt
    have : a.y = 1 := by rw [← hxt]; group
    have := a.y_ord
    rw [‹a.y = 1›, orderOf_one] at this
    omega
  exact ⟨a₀ ^ 4, a.L₁.pow_mem ha₀ 4, orderOf_eq_prime hx3 hne, hxt.symm⟩

end Basic

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
