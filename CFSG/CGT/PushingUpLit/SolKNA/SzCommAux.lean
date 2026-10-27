module

public import CFSG.CGT.PushingUpLit.SolKNA.Prop18

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

variable {X : Type} [Group X] [Finite X]

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem comm_eq_of_mul_mem_L {r s r' s' : X} (hr : r ∈ R) (hs : s ∈ R) (hr' : r⁻¹ * r' ∈ L)
    (hs' : s⁻¹ * s' ∈ L) : r' * s' * r'⁻¹ * s'⁻¹ = r * s * r⁻¹ * s⁻¹ := by
  obtain ⟨l, hl, rfl⟩ : ∃ l ∈ L, r' = r * l := ⟨r⁻¹ * r', hr', by group⟩
  obtain ⟨m, hm, rfl⟩ : ∃ m ∈ L, s' = s * m := ⟨s⁻¹ * s', hs', by group⟩
  have c1 : l * s = s * l := S.L_cent l hl s hs
  have c2 : l * m = m * l := S.comm_N (S.L_le_N hl) (S.L_le_N hm)
  have c3 : Commute m r := S.L_cent m hm r hr
  have e1 : l * (s * m) = (s * m) * l := by
    rw [← mul_assoc, c1, mul_assoc, c2, ← mul_assoc]
  have e2 : m * r⁻¹ = r⁻¹ * m := c3.inv_right.eq
  calc r * l * (s * m) * (r * l)⁻¹ * (s * m)⁻¹
      = r * (l * (s * m)) * (l⁻¹ * r⁻¹) * (m⁻¹ * s⁻¹) := by group
    _ = r * ((s * m) * l) * (l⁻¹ * r⁻¹) * (m⁻¹ * s⁻¹) := by rw [e1]
    _ = r * s * (m * r⁻¹) * (m⁻¹ * s⁻¹) := by group
    _ = r * s * (r⁻¹ * m) * (m⁻¹ * s⁻¹) := by rw [e2]
    _ = r * s * r⁻¹ * s⁻¹ := by group

theorem comm_mul_left {r r₁ s : X} (hr : r ∈ R) (hr₁ : r₁ ∈ R) (hs : s ∈ R) :
    (r * r₁) * s * (r * r₁)⁻¹ * s⁻¹ = (r * s * r⁻¹ * s⁻¹) * (r₁ * s * r₁⁻¹ * s⁻¹) := by
  have hc : r₁ * s * r₁⁻¹ * s⁻¹ ∈ L := S.comm_R r₁ hr₁ s hs
  have hcent : r * (r₁ * s * r₁⁻¹ * s⁻¹) = (r₁ * s * r₁⁻¹ * s⁻¹) * r :=
    (S.L_cent _ hc r hr).symm
  have hcomm : (r * s * r⁻¹ * s⁻¹) * (r₁ * s * r₁⁻¹ * s⁻¹) =
      (r₁ * s * r₁⁻¹ * s⁻¹) * (r * s * r⁻¹ * s⁻¹) :=
    S.comm_N (S.L_le_N (S.comm_R r hr s hs)) (S.L_le_N hc)
  rw [hcomm]
  calc (r * r₁) * s * (r * r₁)⁻¹ * s⁻¹
      = (r * (r₁ * s * r₁⁻¹ * s⁻¹)) * (s * r⁻¹ * s⁻¹) := by group
    _ = ((r₁ * s * r₁⁻¹ * s⁻¹) * r) * (s * r⁻¹ * s⁻¹) := by rw [hcent]
    _ = (r₁ * s * r₁⁻¹ * s⁻¹) * (r * s * r⁻¹ * s⁻¹) := by group

theorem comm_mul_right {r s s₁ : X} (hr : r ∈ R) (hs : s ∈ R) (hs₁ : s₁ ∈ R) :
    r * (s * s₁) * r⁻¹ * (s * s₁)⁻¹ = (r * s * r⁻¹ * s⁻¹) * (r * s₁ * r⁻¹ * s₁⁻¹) := by
  have hd : r * s₁ * r⁻¹ * s₁⁻¹ ∈ L := S.comm_R r hr s₁ hs₁
  have hcent : s * (r * s₁ * r⁻¹ * s₁⁻¹) = (r * s₁ * r⁻¹ * s₁⁻¹) * s :=
    (S.L_cent _ hd s hs).symm
  calc r * (s * s₁) * r⁻¹ * (s * s₁)⁻¹
      = (r * s * r⁻¹) * (r * s₁ * r⁻¹ * s₁⁻¹) * s⁻¹ := by group
    _ = (r * s * r⁻¹ * s⁻¹) * (s * (r * s₁ * r⁻¹ * s₁⁻¹) * s⁻¹) := by group
    _ = (r * s * r⁻¹ * s⁻¹) * ((r * s₁ * r⁻¹ * s₁⁻¹) * s * s⁻¹) := by rw [hcent]
    _ = (r * s * r⁻¹ * s⁻¹) * (r * s₁ * r⁻¹ * s₁⁻¹) := by group

end Prop18Setup

end CFSG.CGT.PushingUpLit.SolKNA
