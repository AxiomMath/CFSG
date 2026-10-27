module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubStab
public import CFSG.ClassicalInvolution.Asc77.AscT7ASetup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7D

section Frame

variable {G : Type} [Group G] {W : Subgroup G}

omit [Group G] in
theorem mul_aux {G : Type} [Group G] {z u j x : G} (hzu : z * u = u * z) (hz2 : z * z = 1)
    (hx : x = z * u) : x * (z * j) = u * j := by
  rw [hx]
  calc z * u * (z * j) = (z * u) * z * j := by group
    _ = (u * z) * z * j := by rw [hzu]
    _ = u * (z * z) * j := by group
    _ = u * j := by rw [hz2, mul_one]

theorem eq_or_eq_mul_of_orderOf_four {K : Subgroup G} {z b₁ b₂ : G}
    (hz : IsUniqueInvolution K z) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (h₁ : b₁ ∈ K ⊓ W)
    (h₂ : b₂ ∈ K ⊓ W) (o₁ : orderOf b₁ = 4) (o₂ : orderOf b₂ = 4) :
    b₂ = b₁ ∨ b₂ = z * b₁ := by
  have s₁ : b₁ * b₁ = z := T7A.sq_eq_of_orderOf_four hz h₁.1 o₁
  have s₂ : b₂ * b₂ = z := T7A.sq_eq_of_orderOf_four hz h₂.1 o₂
  have hc : b₂ * b₁⁻¹ = b₁⁻¹ * b₂ := hWab b₂ h₂.2 b₁⁻¹ (W.inv_mem h₁.2)
  have hsq : (b₂ * b₁⁻¹) * (b₂ * b₁⁻¹) = 1 := by
    calc (b₂ * b₁⁻¹) * (b₂ * b₁⁻¹) = b₂ * (b₁⁻¹ * b₂) * b₁⁻¹ := by group
      _ = b₂ * (b₂ * b₁⁻¹) * b₁⁻¹ := by rw [← hc]
      _ = (b₂ * b₂) * (b₁ * b₁)⁻¹ := by group
      _ = 1 := by rw [s₁, s₂, mul_inv_cancel]
  rcases hz.unique (b₂ * b₁⁻¹) (K.mul_mem h₂.1 (K.inv_mem h₁.1)) hsq with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)

@[expose] def FrameEps (W K K' : Subgroup G) (s j ε : G) : Prop :=
  ∃ b b' : G, b ∈ K ⊓ W ∧ b' ∈ K' ⊓ W ∧ orderOf b = 4 ∧ orderOf b' = 4 ∧
    s * (b * b') * s⁻¹ = b * b' ∧ ε = b * b' * j

theorem FrameEps.unique {K K' : Subgroup G} {z s s' j ε₁ ε₂ : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hsz : s * z * s⁻¹ ≠ z) (hss : ∀ w ∈ W, s * w * s⁻¹ = s' * w * s'⁻¹)
    (h₁ : FrameEps W K K' s j ε₁) (h₂ : FrameEps W K K' s' j ε₂) : ε₁ = ε₂ := by
  obtain ⟨b₁, b₁', hb₁, hb₁', o₁, o₁', hf₁, rfl⟩ := h₁
  obtain ⟨b₂, b₂', hb₂, hb₂', o₂, o₂', hf₂, rfl⟩ := h₂
  have hzW : z ∈ W := by
    rw [← T7A.sq_eq_of_orderOf_four hz hb₁.1 o₁]
    exact W.mul_mem hb₁.2 hb₁.2
  have hz2 : z * z = 1 := hz.sq
  have hzb₁ : z * b₁ = b₁ * z := hWab z hzW b₁ hb₁.2
  have hzb₁' : z * b₁' = b₁' * z := hWab z hzW b₁' hb₁'.2
  have hbad : ∀ u₁ u₂ : G, u₁ ∈ W → u₂ ∈ W → s * u₁ * s⁻¹ = u₁ → s' * u₂ * s'⁻¹ = u₂ →
      u₂ = z * u₁ → False := by
    intro u₁ u₂ hu₁ hu₂ hs₁ hs₂ h
    apply hsz
    have h2 : s * u₂ * s⁻¹ = u₂ := (hss u₂ hu₂).trans hs₂
    have hz : z = u₂ * u₁⁻¹ := by rw [h]; group
    calc s * z * s⁻¹ = (s * u₂ * s⁻¹) * (s * u₁ * s⁻¹)⁻¹ := by rw [hz]; group
      _ = u₂ * u₁⁻¹ := by rw [h2, hs₁]
      _ = z := hz.symm
  have hu₁W : b₁ * b₁' ∈ W := W.mul_mem hb₁.2 hb₁'.2
  have hu₂W : b₂ * b₂' ∈ W := W.mul_mem hb₂.2 hb₂'.2
  have key : b₂ * b₂' = b₁ * b₁' := by
    rcases eq_or_eq_mul_of_orderOf_four hz hWab hb₁ hb₂ o₁ o₂ with e | e <;>
      rcases eq_or_eq_mul_of_orderOf_four hz' hWab hb₁' hb₂' o₁' o₂' with e' | e'
    · rw [e, e']
    · exfalso
      refine hbad _ _ hu₁W hu₂W hf₁ hf₂ ?_
      rw [e, e']
      calc b₁ * (z * b₁') = b₁ * (b₁' * z) := by rw [hzb₁']
        _ = (b₁ * b₁') * z := by group
        _ = z * (b₁ * b₁') := by
          have := hWab z hzW (b₁ * b₁') hu₁W
          exact this.symm
    · exfalso
      refine hbad _ _ hu₁W hu₂W hf₁ hf₂ ?_
      rw [e, e']
      group
    · rw [e, e']
      calc z * b₁ * (z * b₁') = z * (b₁ * z) * b₁' := by group
        _ = z * (z * b₁) * b₁' := by rw [hzb₁]
        _ = (z * z) * b₁ * b₁' := by group
        _ = b₁ * b₁' := by rw [hz2, one_mul]
  rw [key]

theorem FrameEps.conj {K K' : Subgroup G} {s j ε n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (h : FrameEps W K K' s j ε) :
    FrameEps W (conjSub n K) (conjSub n K') (n * s * n⁻¹) (n * j * n⁻¹) (n * ε * n⁻¹) := by
  obtain ⟨b, b', hb, hb', ob, ob', hf, rfl⟩ := h
  have hcW : ∀ x ∈ W, n * x * n⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have hord : ∀ x : G, orderOf (n * x * n⁻¹) = orderOf x := fun x => by
    have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
    simpa [MulAut.conj_apply] using this
  refine ⟨n * b * n⁻¹, n * b' * n⁻¹, ⟨conj_mem_conjSub hb.1, hcW b hb.2⟩,
    ⟨conj_mem_conjSub hb'.1, hcW b' hb'.2⟩, by rw [hord, ob], by rw [hord, ob'], ?_, ?_⟩
  · calc n * s * n⁻¹ * (n * b * n⁻¹ * (n * b' * n⁻¹)) * (n * s * n⁻¹)⁻¹
        = n * (s * (b * b') * s⁻¹) * n⁻¹ := by group
      _ = n * (b * b') * n⁻¹ := by rw [hf]
      _ = n * b * n⁻¹ * (n * b' * n⁻¹) := by group
  · group

end Frame

section CtxFrame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem frame_fixed (c : Thompson.Ctx p f Ω W) (ρ ρ' ρ₃ : Thompson.Rep Ω W) {z j b b' : G}
    (hK'K : ρ'.K ∈ omegaNbr Ω ρ.K) (hKK' : ρ.K ∈ omegaNbr Ω ρ'.K)
    (hne₁ : ρ.K ≠ ρ₃.K) (hne₂ : ρ'.K ≠ ρ₃.K)
    (hn₁ : ρ₃.K ∉ omegaNbr Ω ρ.K) (hn₂ : ρ₃.K ∉ omegaNbr Ω ρ'.K)
    (hn₁' : ρ.K ∉ omegaNbr Ω ρ₃.K) (hn₂' : ρ'.K ∉ omegaNbr Ω ρ₃.K)
    (hz : IsUniqueInvolution ρ.K z) (hz' : IsUniqueInvolution ρ'.K z)
    (hj : IsUniqueInvolution ρ₃.K j)
    (hb : b ∈ ρ.K ⊓ W) (hb' : b' ∈ ρ'.K ⊓ W) (ob : orderOf b = 4) (ob' : orderOf b' = 4) :
    ∃ u₁, (u₁ = b * b' ∨ u₁ = b⁻¹ * b') ∧ ρ₃.r * u₁ * ρ₃.r⁻¹ = u₁ ∧
      ρ.r * (u₁ * j) * ρ.r⁻¹ = u₁ * j ∧ ρ'.r * (u₁ * j) * ρ'.r⁻¹ = u₁ * j ∧
      ρ₃.r * (u₁ * j) * ρ₃.r⁻¹ = u₁ * j := by
  have hWab := c.comm_W
  have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hb.1 ob
  have hb'b' : b' * b' = z := T7A.sq_eq_of_orderOf_four hz' hb'.1 ob'
  have hz2 : z * z = 1 := hz.sq
  have hjW : j ∈ ρ₃.K ⊓ W :=
    Thompson.uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW ρ₃.hK ρ₃.hR ρ₃.hRK hj
  have hzW : z ∈ W := by
    rw [← hbb]
    exact W.mul_mem hb.2 hb.2
  have hbinv : b⁻¹ = z * b := (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hbb, hz2])).symm
  have hb'inv : b'⁻¹ = z * b' := (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hb'b', hz2])).symm
  have e1 : ρ.r * b * ρ.r⁻¹ = b⁻¹ := c.conj_inv ρ hb
  have e1' : ρ.r * b' * ρ.r⁻¹ = b' := by
    rw [c.centralizes ρ ρ' hK'K hb']
    group
  have e2 : ρ.r * j * ρ.r⁻¹ = z * j := c.conj_involution ρ ρ₃ hne₁ hn₁ hz hj
  have f1 : ρ'.r * b' * ρ'.r⁻¹ = b'⁻¹ := c.conj_inv ρ' hb'
  have f1' : ρ'.r * b * ρ'.r⁻¹ = b := by
    rw [c.centralizes ρ' ρ hKK' hb]
    group
  have f2 : ρ'.r * j * ρ'.r⁻¹ = z * j := c.conj_involution ρ' ρ₃ hne₂ hn₂ hz' hj
  have g2 : ρ₃.r * j * ρ₃.r⁻¹ = j := by
    have := c.conj_inv ρ₃ hjW
    rw [this]
    exact inv_eq_of_mul_eq_one_left hj.sq
  have hdich := c.stab_dichotomy ρ₃ ρ ρ' hne₁.symm hne₂.symm hn₁' hn₂' hb hb' hj hz hz' hbb hb'b'
  have hcz : ∀ x ∈ W, z * x = x * z := fun x hx => hWab z hzW x hx
  have hzu : z * (b * b') = (b * b') * z := hcz _ (W.mul_mem hb.2 hb'.2)
  have hzu' : z * (b⁻¹ * b') = (b⁻¹ * b') * z := hcz _ (W.mul_mem (W.inv_mem hb.2) hb'.2)
  have hbz : b * z = z * b := (hcz b hb.2).symm
  have hbiz : b⁻¹ * z = z * b⁻¹ := (hcz b⁻¹ (W.inv_mem hb.2)).symm
  rcases hdich with h | h
  ·
    have hr : ρ.r * (b * b') * ρ.r⁻¹ = z * (b * b') := by
      calc ρ.r * (b * b') * ρ.r⁻¹ = (ρ.r * b * ρ.r⁻¹) * (ρ.r * b' * ρ.r⁻¹) := by group
        _ = b⁻¹ * b' := by rw [e1, e1']
        _ = z * (b * b') := by rw [hbinv, mul_assoc]
    have hr' : ρ'.r * (b * b') * ρ'.r⁻¹ = z * (b * b') := by
      calc ρ'.r * (b * b') * ρ'.r⁻¹ = (ρ'.r * b * ρ'.r⁻¹) * (ρ'.r * b' * ρ'.r⁻¹) := by group
        _ = b * b'⁻¹ := by rw [f1, f1']
        _ = z * (b * b') := by rw [hb'inv, ← mul_assoc, hbz, mul_assoc]
    refine ⟨b * b', Or.inl rfl, h, ?_, ?_, ?_⟩
    · have : ρ.r * (b * b' * j) * ρ.r⁻¹ = (ρ.r * (b * b') * ρ.r⁻¹) * (ρ.r * j * ρ.r⁻¹) := by
        group
      rw [this, hr, e2]
      exact mul_aux hzu hz2 rfl
    · have : ρ'.r * (b * b' * j) * ρ'.r⁻¹ =
          (ρ'.r * (b * b') * ρ'.r⁻¹) * (ρ'.r * j * ρ'.r⁻¹) := by group
      rw [this, hr', f2]
      exact mul_aux hzu hz2 rfl
    · have : ρ₃.r * (b * b' * j) * ρ₃.r⁻¹ =
          (ρ₃.r * (b * b') * ρ₃.r⁻¹) * (ρ₃.r * j * ρ₃.r⁻¹) := by group
      rw [this, h, g2]
  ·
    have hr : ρ.r * (b⁻¹ * b') * ρ.r⁻¹ = z * (b⁻¹ * b') := by
      calc ρ.r * (b⁻¹ * b') * ρ.r⁻¹ = (ρ.r * b * ρ.r⁻¹)⁻¹ * (ρ.r * b' * ρ.r⁻¹) := by group
        _ = b * b' := by rw [e1, e1', inv_inv]
        _ = z * (b⁻¹ * b') := by
          rw [hbinv, ← mul_assoc, ← mul_assoc, hz2, one_mul]
    have hr' : ρ'.r * (b⁻¹ * b') * ρ'.r⁻¹ = z * (b⁻¹ * b') := by
      calc ρ'.r * (b⁻¹ * b') * ρ'.r⁻¹ = (ρ'.r * b * ρ'.r⁻¹)⁻¹ * (ρ'.r * b' * ρ'.r⁻¹) := by group
        _ = b⁻¹ * b'⁻¹ := by rw [f1, f1']
        _ = z * (b⁻¹ * b') := by
          conv_lhs => rw [hb'inv]
          rw [← mul_assoc, hbiz, mul_assoc]
    refine ⟨b⁻¹ * b', Or.inr rfl, h, ?_, ?_, ?_⟩
    · have : ρ.r * (b⁻¹ * b' * j) * ρ.r⁻¹ = (ρ.r * (b⁻¹ * b') * ρ.r⁻¹) * (ρ.r * j * ρ.r⁻¹) := by
        group
      rw [this, hr, e2]
      exact mul_aux hzu' hz2 rfl
    · have : ρ'.r * (b⁻¹ * b' * j) * ρ'.r⁻¹ =
          (ρ'.r * (b⁻¹ * b') * ρ'.r⁻¹) * (ρ'.r * j * ρ'.r⁻¹) := by group
      rw [this, hr', f2]
      exact mul_aux hzu' hz2 rfl
    · have : ρ₃.r * (b⁻¹ * b' * j) * ρ₃.r⁻¹ =
          (ρ₃.r * (b⁻¹ * b') * ρ₃.r⁻¹) * (ρ₃.r * j * ρ₃.r⁻¹) := by group
      rw [this, h, g2]

end CtxFrame

end T7D

end CFSG.ClassicalInvolution.Asc77
