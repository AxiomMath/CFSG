module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockWreath
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

section Eight

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Γ] [DecidableEq Γ]

@[expose] noncomputable def wStabAction (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ↥(wStab ι Bool) →* Perm ι where
  toFun σ := wBlockMap σ.1 σ.2
  map_one' := by
    ext a
    rfl
  map_mul' x y := by
    ext a
    have h3 : wBlockMap (y.1 : Perm (ι × Bool)) y.2 a =
        (y.1 (a, Classical.arbitrary Bool)).1 :=
      wBlockMap_apply y.2 (a, Classical.arbitrary Bool)
    have h1 : wBlockMap (x.1 : Perm (ι × Bool)) x.2 (y.1 (a, Classical.arbitrary Bool)).1 =
        (x.1 (y.1 (a, Classical.arbitrary Bool))).1 := wBlockMap_apply x.2 _
    show (x.1 (y.1 (a, Classical.arbitrary Bool))).1 =
      wBlockMap (x.1 : Perm (ι × Bool)) x.2 (wBlockMap (y.1 : Perm (ι × Bool)) y.2 a)
    rw [h3, h1]

theorem wStabAction_apply (σ : ↥(wStab ι Bool)) (p : ι × Bool) :
    wStabAction ι σ p.1 = (σ.1 p).1 :=
  wBlockMap_apply σ.2 p

variable (ι Γ)

@[expose] def pTilde : Subgroup (Perm (ι × Bool) × Perm Γ) where
  carrier := {p | p.1 ∈ wStab ι Bool ∧ sign p.1 * sign p.2 = 1}
  mul_mem' := by
    intro a b ha hb
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    show sign (a.1 * b.1) * sign (a.2 * b.2) = 1
    rw [map_mul, map_mul, mul_mul_mul_comm]
    have h1 : sign a.1 * sign a.2 = 1 := ha.2
    have h2 : sign b.1 * sign b.2 = 1 := hb.2
    rw [h1, h2, mul_one]
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, ?_⟩
    show sign a.1⁻¹ * sign a.2⁻¹ = 1
    rw [map_inv, map_inv, ← mul_inv]
    have h1 : sign a.1 * sign a.2 = 1 := ha.2
    rw [h1, inv_one]

variable {ι Γ}

theorem mem_pTilde {p : Perm (ι × Bool) × Perm Γ} :
    p ∈ pTilde ι Γ ↔ p.1 ∈ wStab ι Bool ∧ sign p.1 * sign p.2 = 1 := Iff.rfl

@[expose] noncomputable def eightAction (ι Γ : Type*) [Fintype ι] [DecidableEq ι] [Fintype Γ]
    [DecidableEq Γ] : ↥(pTilde ι Γ) →* Perm ι × Perm Γ :=
  ((wStabAction ι).comp
    (MonoidHom.codRestrict (MonoidHom.fst _ _ |>.comp (pTilde ι Γ).subtype) (wStab ι Bool)
      (fun p => p.2.1))).prod ((MonoidHom.snd _ _).comp (pTilde ι Γ).subtype)

theorem eightAction_fst_apply (p : ↥(pTilde ι Γ)) (x : ι × Bool) :
    (eightAction ι Γ p).1 x.1 = (p.1.1 x).1 :=
  wStabAction_apply ⟨p.1.1, p.2.1⟩ x

theorem eightAction_snd (p : ↥(pTilde ι Γ)) : (eightAction ι Γ p).2 = p.1.2 := rfl

theorem eightAction_surjective [Nonempty ι] : Function.Surjective (eightAction ι Γ) := by
  rintro ⟨π, τ⟩
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set t : Perm (ι × Bool) := swap (i0, false) (i0, true) with ht
  have htsign : sign t = -1 := sign_swap (by simp)
  have htstab : t ∈ wStab ι Bool := by
    intro x y
    have : ∀ z : ι × Bool, (t z).1 = z.1 := by
      intro z
      rw [ht, swap_apply_def]
      split_ifs with h1 h2
      · rw [h1]
      · rw [h2]
      · rfl
    rw [this, this]
  have hlift : sign (wLift π : Perm (ι × Bool)) = 1 := wLift_sign (by decide) π
  rcases Int.units_eq_one_or (sign τ) with hτ | hτ
  · refine ⟨⟨(wLift π, τ), wLift_mem_wStab π, by simp [hlift, hτ]⟩, ?_⟩
    ext a
    · have := eightAction_fst_apply ⟨(wLift π, τ), wLift_mem_wStab π, by simp [hlift, hτ]⟩
        (a, false)
      simpa [wLift_apply] using this
    · rfl
  · refine ⟨⟨(wLift π * t, τ), mul_mem (wLift_mem_wStab π) htstab, by
      simp [hlift, hτ, htsign]⟩, ?_⟩
    ext a
    · have := eightAction_fst_apply ⟨(wLift π * t, τ), mul_mem (wLift_mem_wStab π) htstab, by
        simp [hlift, hτ, htsign]⟩ (a, false)
      have h2 : t (a, false) = (a, false) ∨ t (a, false) = (a, true) := by
        rw [ht, swap_apply_def]
        split_ifs <;> simp_all
      have h3 : ((wLift π : Perm (ι × Bool)) (t (a, false))).1 = π a := by
        rcases h2 with h | h <;> simp [h, wLift_apply]
      simpa [Perm.mul_apply, h3] using this
    · rfl

theorem isPGroup_ker_eightAction : IsPGroup 2 (eightAction ι Γ).ker := by
  intro g
  refine ⟨1, ?_⟩
  have hg := g.2
  rw [MonoidHom.mem_ker] at hg
  have hfst : ∀ x : ι × Bool, (g.1.1.1 x).1 = x.1 := by
    intro x
    have := eightAction_fst_apply g.1 x
    rw [show eightAction ι Γ g.1 = 1 from hg] at this
    exact this.symm
  obtain ⟨s, hs⟩ := (mem_range_wPermHom (ι := ι) (κ := Bool)).2 hfst
  have hsq : g.1.1.1 * g.1.1.1 = 1 := by
    rw [← hs, ← map_mul, ← map_one (wPermHom ι Bool)]
    congr 1
    funext i
    exact perm_bool_sq _
  have hb : g.1.1.2 = 1 := by
    have := eightAction_snd g.1
    rw [show eightAction ι Γ g.1 = 1 from hg] at this
    exact this.symm
  apply Subtype.ext
  apply Subtype.ext
  rw [pow_one, pow_two]
  exact Prod.ext hsq (by simp [hb])

end Eight

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
