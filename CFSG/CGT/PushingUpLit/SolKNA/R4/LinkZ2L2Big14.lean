module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big9
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big12

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section CentQ

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem rho_comm_qEmb (E : PGamEmb X F) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {β : MulAut X}
    (hβ : ∀ x ∈ Q, β x = x) (c : QuaternionGroup (2 ^ (r - 2))) :
    E.ρ β * qEmb E e c = qEmb E e c * E.ρ β := by
  have hconj : β * MulAut.conj ((e.symm c : ↥Q) : X) * β⁻¹ =
      MulAut.conj ((e.symm c : ↥Q) : X) := by
    rw [mulAut_mul_conj_mul_inv, hβ _ (e.symm c).2]
  have hcomm : β * MulAut.conj ((e.symm c : ↥Q) : X) =
      MulAut.conj ((e.symm c : ↥Q) : X) * β := by
    calc β * MulAut.conj ((e.symm c : ↥Q) : X)
        = (β * MulAut.conj ((e.symm c : ↥Q) : X) * β⁻¹) * β := by group
      _ = MulAut.conj ((e.symm c : ↥Q) : X) * β := by rw [hconj]
  calc E.ρ β * qEmb E e c
      = E.ρ β * E.ρ (MulAut.conj ((e.symm c : ↥Q) : X)) := by simp only [qEmb_apply]
    _ = E.ρ (β * MulAut.conj ((e.symm c : ↥Q) : X)) := by rw [map_mul]
    _ = E.ρ (MulAut.conj ((e.symm c : ↥Q) : X) * β) := by rw [hcomm]
    _ = E.ρ (MulAut.conj ((e.symm c : ↥Q) : X)) * E.ρ β := by rw [map_mul]
    _ = qEmb E e c * E.ρ β := by simp only [qEmb_apply]

theorem rho_conj_comm_qEmb (E : PGamEmb X F) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {x : X}
    (hx : ∀ y ∈ Q, x * y = y * x) (c : QuaternionGroup (2 ^ (r - 2))) :
    E.ρ (MulAut.conj x) * qEmb E e c = qEmb E e c * E.ρ (MulAut.conj x) := by
  apply rho_comm_qEmb E e ?_ c
  intro y hy
  rw [MulAut.conj_apply, hx y hy]
  group

theorem centralizer_qEmb [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) {g : PGammaL2 F}
    (hgc : ∀ c : QuaternionGroup (2 ^ (r - 2)), g * qEmb E e c = qEmb E e c * g)
    (hgr : g.right * g.right = 1) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g = 1 ∨ g = ubar F ∨
      (g.right = σ₀ ∧ g * g = ubar F ∧ ∀ x : X, E.ρ (MulAut.conj x) ≠ g) := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h2 : (2 : F) ≠ 0 := (field_facts (Fact.out : p.Prime) hp2 hF h4).2
  have hσ : ∀ σ : F ≃+* F, σ * σ = 1 → σ = 1 ∨ σ = σ₀ :=
    fun σ hσ2 => ringAut_sq_eq_one hF hp2 h4 hσ₀1 hσ₀2 hσ2
  obtain ⟨x₀, y, hx₀, hA, hB⟩ := quat_structure E e hF hp2 h4 hidx hr hz hσ₀1 hσ₀2
  have hgmon : IsMon g := (isMon_iff_comm_ubar h2).mpr (by
    have h := hgc (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))
    rwa [qEmb_a_two_pow E e hz] at h)
  have hgA : g * gD x₀ 1 = gD x₀ 1 * g := by
    have h := hgc (QuaternionGroup.a 1)
    rwa [hA] at h
  rcases hB with ⟨hBd, hx, hy⟩ | ⟨hBa, hx, hy⟩
  · have hgB : g * gD y σ₀ = gD y σ₀ * g := by
      have h := hgc (QuaternionGroup.xa 0)
      rwa [hBd] at h
    rcases centralizer_diag h2 hσ₀2 hσ hq hr hx₀ hx hy hgmon hgr hgA hgB hk with
      h1 | h1 | ⟨u, hgu, hu⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [hgu, gA_right]
      · rw [hgu, gA_mul_self u σ₀ hσ₀2, hu, ubar_eq]
      · intro x hxg
        have hbρ : E.ρ (MulAut.conj ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X)) = gD y σ₀ := by
          rw [← qEmb_apply E e (QuaternionGroup.xa 0), hBd]
        have hb : (E.ρ (MulAut.conj ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X))).right ≠ 1 := by
          rw [hbρ, gD_right]
          exact hσ₀1
        have hxr : (E.ρ (MulAut.conj x)).right ≠ 1 := by
          rw [hxg, hgu, gA_right]
          exact hσ₀1
        obtain ⟨-, hmem⟩ := inner_quot_mem E hidx hb hxr
        have hquot : E.ρ (MulAut.conj x) *
            (E.ρ (MulAut.conj ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X)))⁻¹ = gA (u * y) 1 := by
          rw [hxg, hgu, hbρ, third_diag_quot hσ₀2 u y]
        have hleft : pA (u * y) ∈ pslRange F := by
          simpa [hquot, gA_left] using hmem
        exact not_isSquare_third_diag h2 hq (card_units_eq_sq_sub_one hF hf) hr hx₀ hx hy hu
          ((pA_mem_pslRange_iff (u * y)).mp hleft)
  · have hgB : g * gA y σ₀ = gA y σ₀ * g := by
      have h := hgc (QuaternionGroup.xa 0)
      rwa [hBa] at h
    rcases centralizer_anti h2 hσ₀2 hσ hq hr hx₀ hx hy hgmon hgr hgA hgB hk with
      h1 | h1 | ⟨u, hgu, hu⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [hgu, gD_right]
      · rw [hgu, gD_mul_self u σ₀ hσ₀2, hu, ubar_eq]
      · intro x hxg
        have hbρ : E.ρ (MulAut.conj ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X)) = gA y σ₀ := by
          rw [← qEmb_apply E e (QuaternionGroup.xa 0), hBa]
        have hb : (E.ρ (MulAut.conj ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X))).right ≠ 1 := by
          rw [hbρ, gA_right]
          exact hσ₀1
        have hxr : (E.ρ (MulAut.conj x)).right ≠ 1 := by
          rw [hxg, hgu, gD_right]
          exact hσ₀1
        obtain ⟨-, hmem⟩ := inner_quot_mem E hidx hb hxr
        have hquot : E.ρ (MulAut.conj x) *
            (E.ρ (MulAut.conj ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X)))⁻¹ = gA (u * y) 1 := by
          rw [hxg, hgu, hbρ, third_anti_quot hσ₀2 u y]
        have hleft : pA (u * y) ∈ pslRange F := by
          simpa [hquot, gA_left] using hmem
        exact not_isSquare_third_anti h2 hq (card_units_eq_sq_sub_one hF hf) hr hx₀ hx hy hu
          ((pA_mem_pslRange_iff (u * y)).mp hleft)

theorem cent_two_elements [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) {x : X} (hx : ∀ y ∈ Q, x * y = y * x)
    (hk : ∃ k : ℕ, x ^ 2 ^ k = 1) : x = 1 ∨ x = quatInvolution r e := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨k, hk⟩ := hk
  have hgc : ∀ c : QuaternionGroup (2 ^ (r - 2)),
      E.ρ (MulAut.conj x) * qEmb E e c = qEmb E e c * E.ρ (MulAut.conj x) :=
    rho_conj_comm_qEmb E e hx
  have hgr : (E.ρ (MulAut.conj x)).right * (E.ρ (MulAut.conj x)).right = 1 :=
    E.right_sq hidx x
  have hgk : (E.ρ (MulAut.conj x)) ^ 2 ^ k = 1 := by
    rw [← map_pow, ← map_pow, hk, map_one, map_one]
  rcases centralizer_qEmb E e hF hp2 h4 hf hidx hr hz hσ₀1 hσ₀2 hq
      (g := E.ρ (MulAut.conj x)) hgc hgr hgk with h1 | h1 | h3
  · left
    apply E.conjInj
    apply E.inj
    rw [h1, map_one, map_one]
  · right
    have hub : ubar F = E.ρ (MulAut.conj (quatInvolution r e)) := by
      rw [ubar_eq, ← inl_pD_eq, ← hz]
    apply E.conjInj
    apply E.inj
    rw [h1, hub]
  · exact absurd rfl (h3.2.2 x)

end CentQ

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
