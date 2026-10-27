module

public import CFSG.GH74.Generic.BProg.B3.S3SL2Basic
public import CFSG.GH74.Generic.S45.LAltLift

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Equiv Equiv.Perm
open scoped commutatorElement

structure AltSetting {Y : Type} [Group Y] (H : Subgroup Y) (n : ℕ) {s : Y}
    (hsN : s ∈ normalizer (H : Set Y)) where
  π : ↥H →* alternatingGroup (Fin n)
  surj : Function.Surjective π
  ker_eq : π.ker = center ↥H
  σ : Perm (Fin n)
  σ_sq : σ * σ = 1
  σ_ne : σ ≠ 1
  act : ∀ h : ↥H, ((π (S3SL2Basic.actH H hsN h) : alternatingGroup (Fin n)) : Perm (Fin n)) =
    σ * (π h : Perm (Fin n)) * σ⁻¹

namespace AltSetting

variable {Y : Type} [Group Y] {H : Subgroup Y} {n : ℕ} {s : Y} {hsN : s ∈ normalizer (H : Set Y)}

theorem σ_inv (S : AltSetting H n hsN) : S.σ⁻¹ = S.σ := inv_eq_of_mul_eq_one_right S.σ_sq

theorem commute_of_centralizes (S : AltSetting H n hsN) {h : ↥H} (hh : s * (h : Y) = (h : Y) * s) :
    S.σ * (S.π h : Perm (Fin n)) = (S.π h : Perm (Fin n)) * S.σ := by
  have h1 := S.act h
  rw [(S3SL2Basic.actH_eq_iff H hsN h).2 hh] at h1
  calc S.σ * (S.π h : Perm (Fin n)) = (S.σ * (S.π h : Perm (Fin n)) * S.σ⁻¹) * S.σ := by group
    _ = (S.π h : Perm (Fin n)) * S.σ := by rw [← h1]

theorem mem_ker_iff (S : AltSetting H n hsN) (h : ↥H) : S.π h = 1 ↔ h ∈ center ↥H := by
  rw [← S.ker_eq, MonoidHom.mem_ker]

end AltSetting

theorem exists_altSetting {Y : Type} [Group Y] {H : Subgroup Y} (hQ : CFSG.IsQuasisimple ↥H) {n : ℕ}
    (hn : 7 ≤ n) (he : Nonempty (↥H ⧸ center ↥H ≃* alternatingGroup (Fin n))) {s : Y}
    (hss : s * s = 1) (hsN : s ∈ normalizer (H : Set Y)) (hns : ∃ h ∈ H, s * h ≠ h * s) :
    Nonempty (AltSetting H n hsN) := by
  classical
  obtain ⟨e⟩ := he
  let π : ↥H →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥H))
  have hsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center ↥H := by
    ext h
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [← map_one e.toMonoidHom]
    constructor
    · intro h1
      exact (QuotientGroup.eq_one_iff h).1 (e.injective h1)
    · intro h1
      rw [(QuotientGroup.eq_one_iff h).2 h1]
  let α : MulAut ↥H := S3SL2Basic.actH H hsN
  have hαc : (center ↥H).map α.toMonoidHom = center ↥H := Subgroup.map_center_eq α
  let αq : (↥H ⧸ center ↥H) ≃* (↥H ⧸ center ↥H) := QuotientGroup.congr (center ↥H) (center ↥H) α hαc
  let ab : MulAut (alternatingGroup (Fin n)) := e.symm.trans (αq.trans e)
  have hab : ∀ h : ↥H, ab (π h) = π (α h) := by
    intro h
    have h1 : e.symm (π h) = QuotientGroup.mk h := by simp [π]
    show e (αq (e.symm (π h))) = π (α h)
    rw [h1]
    exact congrArg e (QuotientGroup.congr_mk (center ↥H) (center ↥H) α hαc h)
  have hα2 : α * α = 1 := S3SL2Basic.actH_mul_self H hsN hss
  have hab1 : ab ≠ 1 := by
    intro h1
    have hfix : ∀ k ∈ (⊤ : Subgroup ↥H), α k = k := by
      refine S45.LAlt.fixed_of_perfect α π hker.le (D := ⊤) ?_ ?_
      · have := Group.isPerfect_def.1 hQ.1
        rw [_root_.commutator_def] at this
        exact this
      · intro k _
        rw [← hab k, h1]
        rfl
    obtain ⟨h, hh, hne⟩ := hns
    exact hne ((S3SL2Basic.actH_eq_iff H hsN ⟨h, hh⟩).1 (hfix ⟨h, hh⟩ trivial))
  have hab2 : ab * ab = 1 := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨h, rfl⟩ := hsurj a
    show ab (ab (π h)) = π h
    have : α (α h) = h := by
      have := congrArg (fun f : MulAut ↥H => f h) hα2
      simpa using this
    rw [hab, hab, this]
  obtain ⟨σ, hσ2, hσ1, hσ⟩ := S45.LAlt.exists_sigma (Or.inr hn) ab hab1 hab2
  refine ⟨⟨π, hsurj, hker, σ, hσ2, hσ1, fun h => ?_⟩⟩
  rw [← hab h]
  exact hσ (π h)

end CFSG.GH74.Generic.BProg.B3
