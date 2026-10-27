module

public import CFSG.LargeExtraspecial.S10Six
public import CFSG.LargeExtraspecial.S10Dec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

section Op

variable {p : ℕ} {X : Type*} [Group X]

structure IsOp (p : ℕ) (R K : Subgroup X) : Prop where
  le : K ≤ R
  isPGroup : IsPGroup p K
  conj_mem : ∀ r ∈ R, ∀ k ∈ K, r * k * r⁻¹ ∈ K
  le_of : ∀ H : Subgroup X, H ≤ R → IsPGroup p H → (∀ r ∈ R, ∀ h ∈ H, r * h * r⁻¹ ∈ H) → H ≤ K

theorem IsOp.eq {R K₁ K₂ : Subgroup X} (h₁ : IsOp p R K₁) (h₂ : IsOp p R K₂) : K₁ = K₂ :=
  le_antisymm (h₂.le_of K₁ h₁.le h₁.isPGroup h₁.conj_mem)
    (h₁.le_of K₂ h₂.le h₂.isPGroup h₂.conj_mem)

theorem mem_map_conj_iff {K : Subgroup X} {m x : X} :
    x ∈ K.map (MulAut.conj m).toMonoidHom ↔ m⁻¹ * x * m ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩

theorem IsOp.map_conj {R K : Subgroup X} (h : IsOp p R K) (m : X) :
    IsOp p (R.map (MulAut.conj m).toMonoidHom) (K.map (MulAut.conj m).toMonoidHom) where
  le := Subgroup.map_mono h.le
  isPGroup := h.isPGroup.map _
  conj_mem := by
    intro r hr k hk
    rw [mem_map_conj_iff] at hr hk ⊢
    have := h.conj_mem _ hr _ hk
    simpa [mul_assoc] using this
  le_of := by
    intro H hHR hH hHn x hx
    rw [mem_map_conj_iff]
    refine h.le_of (H.map (MulAut.conj m⁻¹).toMonoidHom) (fun y hy => ?_) (hH.map _)
      (fun r hr y hy => ?_) ⟨x, hx, by simp⟩
    · rw [mem_map_conj_iff, inv_inv] at hy
      have := mem_map_conj_iff.mp (hHR hy)
      simpa [mul_assoc] using this
    · rw [mem_map_conj_iff, inv_inv] at hy ⊢
      have hr' : m * r * m⁻¹ ∈ R.map (MulAut.conj m).toMonoidHom :=
        mem_map_conj_iff.mpr (by simpa [mul_assoc] using hr)
      have := hHn _ hr' _ hy
      simpa [mul_assoc] using this

end Op

theorem eq_τ₂_of_stab_Γ₂ : ∀ γ : Gm, act γ E00 = E00 → γ.1 = 1 → γ ≠ 1 → γ = τ₂ := by
  decide +kernel

theorem stab_mem_Γ₁_or : ∀ γ : Gm, act γ E00 = E00 → γ.2 = 1 ∨ (γ * τ₂).2 = 1 := by
  decide +kernel

theorem act_Γ₂_ne : ∀ γ : Gm, γ.1 = 1 → γ ^ 3 = 1 → γ ≠ 1 → act γ E00 ≠ E00 := by
  decide +kernel

theorem pf_act_Γ₂ : ∀ γ : Gm, γ.1 = 1 → pf E00 (act γ E00) = 0 := by decide +kernel

theorem act_Γ₂_add : ∀ γ : Gm, γ.1 = 1 → γ ^ 3 = 1 → γ ≠ 1 →
    E00 + act γ E00 = act (γ * γ) E00 := by
  decide +kernel

theorem not_comm_of_stab : ∀ γ δ : Gm, act γ E00 = E00 → γ.2 ≠ 1 → δ.1 = 1 → δ ^ 3 = 1 →
    δ ≠ 1 → γ * δ ≠ δ * γ := by
  decide +kernel

theorem perm_three_gen : ∀ s σ : Equiv.Perm (Fin 3), s * s = 1 → s ≠ 1 →
    (∃ a, σ = a * s * a⁻¹) ∨ ∃ a b, σ = a * s * a⁻¹ * (b * s * b⁻¹) := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

variable (S g) in
@[expose] def NoPGL25 : Prop :=
  ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {τ : S.O} (hτ : τ ∈ S.Lbar g) (hτ1 : τ ≠ 1)
    (hVQ : ¬ V S g τ ≤ S.Qa g), Rbar S g τ ≠ S.Lbar g → S.Lbar g ⊓ Nbar S g τ ≠ zpowers τ →
    ¬ PGL25Case H C hτ hτ1 hVQ

structure Dec108 (X : Hyp10 S g t) (Xb Yb : Subgroup S.O) : Prop where
  dec : DirDec S g t Xb Yb
  fixW : ∀ r ∈ Xb, ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t
  exists_y : ∃ y ∈ Yb, y ∈ S.Lbar g ∧ y ∉ Nbar S g t

theorem exists_dec108
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    (h104 : ∃ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t)
    (h7 : 7 ≤ S.width) : ∃ Xb Yb : Subgroup S.O, Dec108 X Xb Yb := by
  obtain ⟨x, hxL, hxN, hxW⟩ := exists_mem_fixWstar hCE X h104 h7
  obtain ⟨Yb, -, hiso, hsup, hinf, hcomm, hW, y, hyY, hyL, hyN⟩ :=
    timmesfeld_10_2 hCE X hxL hxN hxW.2
  exact ⟨R0 S g t x, Yb, ⟨hsup, hinf, hcomm, hiso⟩, hW, y, hyY, hyL, hyN⟩

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem exists_frame (hCE : CentralExtInput.{u}) :
    ∃ F : Frame X, (D.dec.piY F).range = Γ₂ ∧ Xb = F.pre Γ₁ ∧
      ∃ y ∈ Yb, ∃ hyL : y ∈ S.Lbar g, F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂ := by
  obtain ⟨F, hFY, hFX⟩ := D.dec.exists_frame hCE X
  obtain ⟨y, hyY, hyL, hyN⟩ := D.exists_y
  refine ⟨F, hFY, hFX, y, hyY, hyL, ?_⟩
  have h2 : F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ ∈ Γ₂ := hFY ▸ ⟨⟨y, hyY⟩, rfl⟩
  exact eq_τ₂_of_stab_Γ₂ _ (F.π_mem_stabA hyL) (mem_Γ₂.mp h2)
    fun h => hyN ((F.ker _).mp h)

end Dec108

end CFSG.LargeExtraspecial.S10
