module

public import CFSG.LargeExtraspecial.S10TwoH
public import CFSG.LargeExtraspecial.S10TwoG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

variable (S g t) in
@[expose] noncomputable def R0 (x : S.O) : Subgroup S.O :=
  Nbar S g t ⊔ closure {z | ∃ r ∈ Rbar S g t, z = r * x * r⁻¹}

theorem conj_mem_R0 {x : S.O} {r : S.O} (hr : r ∈ Rbar S g t) : r * x * r⁻¹ ∈ R0 S g t x :=
  Subgroup.mem_sup_right (subset_closure ⟨r, hr, rfl⟩)

theorem Frame.pre_Γ₁_le_of {X : Hyp10 S g t} (F : Frame X) {x : S.O} (hxL : x ∈ S.Lbar g)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) {K : Subgroup S.O} (hNK : Nbar S g t ≤ K)
    (hxK : ∀ r ∈ Rbar S g t, r * x * r⁻¹ ∈ K) : F.pre Γ₁ ≤ K := by
  intro r hr
  obtain ⟨hrR, hrπ⟩ := (F.mem_pre).mp hr
  have hxR := Lbar_le_Rbar X.ht hxL
  obtain ⟨δ₁, δ₂, hδ⟩ := Γ₁_closure _ (mem_Γ₁.mp hrπ)
  obtain ⟨r₁, hr₁⟩ := F.surj δ₁
  obtain ⟨r₂, hr₂⟩ := F.surj δ₂
  have key : ∀ w : Rbar S g t, (w : S.O) ∈ K → F.π w = F.π ⟨r, hrR⟩ → r ∈ K := by
    intro w hwK hwπ
    have hn : ((w⁻¹ * ⟨r, hrR⟩ : Rbar S g t) : S.O) ∈ Nbar S g t :=
      (F.ker _).mp (by rw [map_mul, map_inv, hwπ, inv_mul_cancel])
    have := mul_mem hwK (hNK hn)
    simpa using this
  obtain ⟨w₁, hw₁⟩ : ∃ w : Rbar S g t, w = r₁ * ⟨x, hxR⟩ * r₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w : Rbar S g t, w = r₂ * ⟨x, hxR⟩ * r₂⁻¹ := ⟨_, rfl⟩
  have hw₁K : (w₁ : S.O) ∈ K := by
    have e : (w₁ : S.O) = (r₁ : S.O) * x * (r₁ : S.O)⁻¹ := by rw [hw₁]; simp
    rw [e]; exact hxK _ r₁.2
  have hw₂K : (w₂ : S.O) ∈ K := by
    have e : (w₂ : S.O) = (r₂ : S.O) * x * (r₂ : S.O)⁻¹ := by rw [hw₂]; simp
    rw [e]; exact hxK _ r₂.2
  have hπw₁ : F.π w₁ = δ₁ * τ₁ * δ₁⁻¹ := by rw [hw₁, map_mul, map_mul, map_inv, hr₁, hπx]
  have hπw₂ : F.π w₂ = δ₂ * τ₁ * δ₂⁻¹ := by rw [hw₂, map_mul, map_mul, map_inv, hr₂, hπx]
  rcases hδ with h1 | h2
  · exact key w₁ hw₁K (by rw [hπw₁, h1])
  · refine key (w₁ * w₂) ?_ (by rw [map_mul, hπw₁, hπw₂, h2])
    rw [Subgroup.coe_mul]
    exact mul_mem hw₁K hw₂K

theorem Frame.pre_Γ₁_eq_R0 {X : Hyp10 S g t} (F : Frame X) {x : S.O} (hxL : x ∈ S.Lbar g)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) : F.pre Γ₁ = R0 S g t x := by
  refine le_antisymm (F.pre_Γ₁_le_of hxL hπx le_sup_left fun r hr => conj_mem_R0 hr)
    (sup_le (F.Nbar_le_pre Γ₁) ((closure_le _).mpr ?_))
  rintro _ ⟨r, hr, rfl⟩
  refine F.conj_mem_pre_Γ₁ hr ((F.mem_pre).mpr ⟨Lbar_le_Rbar X.ht hxL, ?_⟩)
  rw [hπx]
  exact τ₁_mem_Γ₁

theorem timmesfeld_10_2_frame (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {x : S.O} (hxL : x ∈ S.Lbar g) (hxW : x ∈ fixWstar X)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) :
    R0 S g t x = F.pre Γ₁ ∧ ∃ Y : Subgroup S.O, Y ≤ F.pre Γ₂ ∧
      Nonempty (Y ≃* Equiv.Perm (Fin 3)) ∧ R0 S g t x ⊔ Y = Rbar S g t ∧
      R0 S g t x ⊓ Y = ⊥ ∧ (∀ a ∈ R0 S g t x, ∀ b ∈ Y, a * b = b * a) ∧
      (∀ r ∈ R0 S g t x, ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ∧
      ∃ y ∈ Y, ∃ hyL : y ∈ S.Lbar g, F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂ := by
  have hR0 := (F.pre_Γ₁_eq_R0 hxL hπx).symm
  obtain ⟨y, hyL, hyR, hπy, hR0y⟩ := exists_complement_y hCE X F hxL hxW hπx
  obtain ⟨d, hd3, hd1, hπd3, hdne, hR0d, hyd⟩ := exists_complement_d hCE X F hyL hπy hR0y
  have hK := pre_Γ₁_le_fixWstar hCE X F hxL hxW hπx
  refine ⟨hR0, Ybar y (d : S.O), Ybar_le_pre_Γ₂ X F hyL hπy hd1,
    nonempty_Ybar_mulEquiv X F hyL hπy hd3 hd1 hdne hπd3 hyd, ?_, ?_, ?_, ?_,
    y, Subgroup.mem_sup_left (mem_zpowers y), hyL, hπy⟩
  · rw [hR0]
    exact sup_Ybar_eq X F hyL hπy hd1 hdne hπd3
  · rw [hR0]
    exact inf_Ybar_eq_bot X F hyL hπy hd3 hd1 hdne hπd3 hyd
  · intro a ha b hb
    rw [hR0] at ha
    exact commute_of_mem_Ybar hR0y hR0d ha hb
  · intro r hr w hw
    rw [hR0] at hr
    exact (hK hr).2 w hw

theorem timmesfeld_10_2 (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {x : S.O}
    (hxL : x ∈ S.Lbar g) (hxN : x ∉ Nbar S g t)
    (hxW : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    ∃ Y : Subgroup S.O, Y ≤ Rbar S g t ∧ Nonempty (Y ≃* Equiv.Perm (Fin 3)) ∧
      R0 S g t x ⊔ Y = Rbar S g t ∧ R0 S g t x ⊓ Y = ⊥ ∧
      (∀ a ∈ R0 S g t x, ∀ b ∈ Y, a * b = b * a) ∧
      (∀ r ∈ R0 S g t x, ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ∧
      ∃ y ∈ Y, y ∈ S.Lbar g ∧ y ∉ Nbar S g t := by
  obtain ⟨F⟩ := X.exists_frame
  have hxK : x ∈ fixWstar X := ⟨Lbar_le_Rbar X.ht hxL, hxW⟩
  have key : ∀ F : Frame X, F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁ →
      ∃ Y : Subgroup S.O, Y ≤ Rbar S g t ∧ Nonempty (Y ≃* Equiv.Perm (Fin 3)) ∧
        R0 S g t x ⊔ Y = Rbar S g t ∧ R0 S g t x ⊓ Y = ⊥ ∧
        (∀ a ∈ R0 S g t x, ∀ b ∈ Y, a * b = b * a) ∧
        (∀ r ∈ R0 S g t x, ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ∧
        ∃ y ∈ Y, y ∈ S.Lbar g ∧ y ∉ Nbar S g t := by
    intro F hπx
    obtain ⟨-, Y, hY2, hiso, hsup, hinf, hcomm, hW, y, hyY, hyL, hπy⟩ :=
      timmesfeld_10_2_frame hCE X F hxL hxK hπx
    refine ⟨Y, hY2.trans (F.pre_le_Rbar Γ₂), hiso, hsup, hinf, hcomm, hW, y, hyY, hyL,
      fun hyN => τ₂_ne_one ?_⟩
    rw [← hπy]
    exact (F.ker _).mpr hyN
  rcases pi_eq_τ₁_or_τ₂ hCE X F hxL hxN hxK with h1 | h2
  · exact key F h1
  · refine key F.swap ?_
    rw [F.swap_π, h2, τ₂_swap]

end CFSG.LargeExtraspecial.S10
