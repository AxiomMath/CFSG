module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_polar_of_similitude {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) (x y : V) :
    Q.polarBilin (σ x) (σ y) = (c : ZMod 3) * Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  have h := hσ (x + y)
  rw [map_add] at h
  rw [h, hσ x, hσ y]
  ring

theorem fg_cplx_of_similitude {ρ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hρ : IsSimilitude Q ρ c) (hρρ : ∀ v, ρ (ρ v) = -v) :
    FGCplx Q.polarBilin (ρ : V →ₗ[ZMod 3] V) (c : ZMod 3) where
  symm x y := by
    simp only [QuadraticMap.polarBilin_apply_apply]
    exact QuadraticMap.polar_comm Q x y
  lam_eq := by
    have h : ∀ c : (ZMod 3)ˣ, (c : ZMod 3) = 1 ∨ (c : ZMod 3) = -1 := by decide
    exact h c
  sq := hρρ
  isom := fg_polar_of_similitude hρ

theorem fg_mk_eq_of_smul {γ γ' : ↥(simGroup Q)} {ε : ZMod 3} (hε : ε ≠ 0)
    (h : ∀ v, (γ : V ≃ₗ[ZMod 3] V) v = ε • (γ' : V ≃ₗ[ZMod 3] V) v) :
    (QuotientGroup.mk γ : ProjSim Q) = QuotientGroup.mk γ' := by
  have hε' : ε = 1 ∨ ε = -1 := by
    have h3 : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = -1 := by decide
    exact h3 ε hε
  rcases hε' with rfl | rfl
  · congr 1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simpa using h v
  · apply QuotientGroup.eq.mpr
    refine mem_piSim_iff.mpr (Or.inr ?_)
    rw [inv_mul_eq_iff_eq_mul]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (γ' : V ≃ₗ[ZMod 3] V) v =
      (γ : V ≃ₗ[ZMod 3] V) ((piOrth Q : V ≃ₗ[ZMod 3] V) v)
    rw [coe_piOrth_apply, map_neg, h v]
    simp

theorem fg_cplx_ab_zero {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V}
    (h : FGCplx B ρ (-1)) (hB : B.Nondegenerate) [Nontrivial V] {α β μ : ZMod 3}
    (hγ : ∀ x y, B (α • x + β • ρ x) (α • y + β • ρ y) = μ * B x y) : α * β = 0 := by
  by_contra hne
  set s : ZMod 3 := 2 * (α * β) with hs_def
  set t : ZMod 3 := μ - α * α + β * β with ht_def
  have hs : s ≠ 0 := mul_ne_zero (by decide) hne
  have key : ∀ x y, B x (s • ρ y - t • y) = 0 := by
    intro x y
    have h1 := hγ x y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [h.adj x y, h.isom x y] at h1
    simp only [map_sub, map_smul, smul_eq_mul, hs_def, ht_def]
    linear_combination h1
  have hker : ∀ y, s • ρ y = t • y := by
    intro y
    have h0 : s • ρ y - t • y = 0 := by
      refine hB.1 _ (fun x => ?_)
      rw [h.symm]
      exact key x y
    exact sub_eq_zero.mp h0
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  have e1 := hker y
  have e2 := hker (ρ y)
  rw [h.sq y] at e2
  have e3 : (s * s + t * t) • y = 0 := by
    calc (s * s + t * t) • y = s • (s • y) + t • (t • y) := by
          rw [add_smul, smul_smul, smul_smul]
      _ = s • (s • y) + t • (s • ρ y) := by rw [e1]
      _ = s • (s • y) + s • (t • ρ y) := by rw [smul_comm t s]
      _ = s • (s • y) + s • (s • (-y)) := by rw [← e2]
      _ = 0 := by rw [smul_neg, smul_neg, add_neg_cancel]
  have e4 : s * s + t * t = 0 := (smul_eq_zero.mp e3).resolve_right hy
  have h3 : ∀ a b : ZMod 3, a ≠ 0 → a * a + b * b ≠ 0 := by decide
  exact h3 s t hs e4

theorem fg_ab_ne_zero [Nontrivial V] {γ : V ≃ₗ[ZMod 3] V} {ρ : V →ₗ[ZMod 3] V} {α β : ZMod 3}
    (hγ : ∀ v, γ v = α • v + β • ρ v) : α ≠ 0 ∨ β ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  have h0 : γ y = γ 0 := by
    rw [hγ y, hc.1, hc.2, map_zero]
    simp
  exact hy (γ.injective h0)

theorem fg_class_of_ab_zero [Nontrivial V] {ρ γ : ↥(simGroup Q)} {α β : ZMod 3}
    (hγ : ∀ v, (γ : V ≃ₗ[ZMod 3] V) v = α • v + β • (ρ : V ≃ₗ[ZMod 3] V) v) (hab : α * β = 0) :
    (QuotientGroup.mk γ : ProjSim Q) = 1 ∨
      (QuotientGroup.mk γ : ProjSim Q) = QuotientGroup.mk ρ := by
  have hne := fg_ab_ne_zero hγ
  rcases mul_eq_zero.mp hab with ha | hb
  · right
    have hβ : β ≠ 0 := hne.resolve_left (not_not.mpr ha)
    exact fg_mk_eq_of_smul hβ (fun v => by rw [hγ v, ha]; simp)
  · left
    have hα : α ≠ 0 := hne.resolve_right (not_not.mpr hb)
    have := fg_mk_eq_of_smul (γ' := (1 : ↥(simGroup Q))) hα (fun v => by rw [hγ v, hb]; simp)
    rw [this]
    rfl

theorem fg_cplx_neg_class (hB : Q.polarBilin.Nondegenerate) [Nontrivial V] {ρ : ↥(simGroup Q)}
    (hρ : FGCplx Q.polarBilin (ρ : V ≃ₗ[ZMod 3] V).toLinearMap (-1)) {γ : ↥(simGroup Q)}
    {α β : ZMod 3}
    (hγ : ∀ v, (γ : V ≃ₗ[ZMod 3] V) v = α • v + β • (ρ : V ≃ₗ[ZMod 3] V) v) :
    (QuotientGroup.mk γ : ProjSim Q) = 1 ∨
      (QuotientGroup.mk γ : ProjSim Q) = QuotientGroup.mk ρ := by
  obtain ⟨μ, hμ⟩ := γ.2
  have hab : α * β = 0 := by
    refine fg_cplx_ab_zero hρ hB (μ := (μ : ZMod 3)) (fun x y => ?_)
    have := fg_polar_of_similitude hμ x y
    rw [hγ x, hγ y] at this
    exact this
  exact fg_class_of_ab_zero hγ hab

theorem fg_cplx_ab_zero_pos {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V}
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y) (hB : B.Nondegenerate)
    [Nontrivial V] {α β μ : ZMod 3} (hμ : μ ≠ 0)
    (hγ : ∀ x y, B (α • x + β • ρ x) (α • y + β • ρ y) = μ * B x y) : α * β = 0 := by
  have hskew : ∀ x y, B (ρ x) y = -B x (ρ y) := by
    intro x y
    have h := hρB x (ρ y)
    rw [hρ2 y] at h
    exact h
  have hexp : ∀ x y, (α * α - β * β - μ) * B x y = 0 := by
    intro x y
    have h1 := hγ x y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hskew x y, hρB x y] at h1
    linear_combination h1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hy : ∃ y, B x y ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (hB.1 x hc)
  obtain ⟨y, hy⟩ := hy
  have h0 : α * α - β * β - μ = 0 := (mul_eq_zero.mp (hexp x y)).resolve_right hy
  have h3 : ∀ a b m : ZMod 3, m ≠ 0 → a * a - b * b - m = 0 → a * b = 0 := by decide
  exact h3 α β μ hμ h0

theorem fg_mk_sq_eq_one {ρ : ↥(simGroup Q)}
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    (QuotientGroup.mk ρ : ProjSim Q) ^ 2 = 1 := by
  rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  refine mem_piSim_iff.mpr (Or.inr ?_)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) =
    ((orthToSim Q (piOrth Q) : ↥(simGroup Q)) : V ≃ₗ[ZMod 3] V) v
  rw [coe_orthToSim, coe_piOrth_apply, hρρ v]

end CFSG.OddStandard.SmallF3.Omega
