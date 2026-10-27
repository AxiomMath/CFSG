module

public import CFSG.LargeExtraspecial.S10TwoC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Frame

variable {X : Hyp10 S g t} (F : Frame X)

theorem exists_pow_cube (hCE : CentralExtInput.{u}) {r : Rbar S g t} (hr : F.π r ^ 3 = 1) :
    ∃ e : ℕ, (r ^ (4 ^ e)) ^ 3 = 1 ∧ F.π (r ^ (4 ^ e)) = F.π r := by
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (X.isPGroup_Nbar hCE)
  have hr3 : ((r : S.O)) ^ 3 ∈ Nbar S g t := by
    have := (F.ker (r ^ 3)).mp (by rw [map_pow, hr])
    simpa using this
  have hpow : (((r : S.O)) ^ 3) ^ (2 ^ e) = 1 := by
    have := pow_card_eq_one' (G := Nbar S g t) (x := ⟨_, hr3⟩)
    rw [he] at this
    exact congrArg Subtype.val this
  refine ⟨e, Subtype.ext ?_, by rw [map_pow, pow_four_pow_of_cube hr e]⟩
  rw [Subgroup.coe_pow, Subgroup.coe_pow, ← pow_mul, show 4 ^ e * 3 = 3 * 2 ^ e * 2 ^ e by
    rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]; ring, pow_mul, pow_mul, hpow, one_pow]
  rfl

theorem conj_mem_pre_Γ₁ {r : S.O} (hr : r ∈ Rbar S g t) {z : S.O} (hz : z ∈ F.pre Γ₁) :
    r * z * r⁻¹ ∈ F.pre Γ₁ := by
  obtain ⟨hzR, hzπ⟩ := (F.mem_pre).mp hz
  obtain ⟨w, hwd⟩ : ∃ w : Rbar S g t, w = ⟨r, hr⟩ * ⟨z, hzR⟩ * ⟨r, hr⟩⁻¹ := ⟨_, rfl⟩
  have hw : r * z * r⁻¹ = (w : S.O) := by rw [hwd]; simp
  rw [hw]
  refine (F.mem_pre).mpr ⟨w.2, ?_⟩
  rw [Subtype.coe_eta, hwd, map_mul, map_mul, map_inv, mem_Γ₁]
  exact conj_mem_Γ₁ _ _ (mem_Γ₁.mp hzπ)

end Frame

section Assembly

variable (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) {x : S.O}
  (hxL : x ∈ S.Lbar g) (hxW : x ∈ fixWstar X) (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁)
include hCE hxW hπx

theorem pre_Γ₁_le_fixWstar : F.pre Γ₁ ≤ fixWstar X := by
  intro r hr
  obtain ⟨hrR, hrπ⟩ := (F.mem_pre).mp hr
  have hxR := Lbar_le_Rbar X.ht hxL
  obtain ⟨δ₁, δ₂, hδ⟩ := Γ₁_closure _ (mem_Γ₁.mp hrπ)
  obtain ⟨r₁, hr₁⟩ := F.surj δ₁
  obtain ⟨r₂, hr₂⟩ := F.surj δ₂
  have hc₁ : ((r₁ : S.O) * x * (r₁ : S.O)⁻¹) ∈ fixWstar X := conj_mem_fixWstar X r₁.2 hxW
  have hc₂ : ((r₂ : S.O) * x * (r₂ : S.O)⁻¹) ∈ fixWstar X := conj_mem_fixWstar X r₂.2 hxW
  have key : ∀ w : Rbar S g t, (w : S.O) ∈ fixWstar X → F.π w = F.π ⟨r, hrR⟩ →
      r ∈ fixWstar X := by
    intro w hwK hwπ
    have hn : ((w⁻¹ * ⟨r, hrR⟩ : Rbar S g t) : S.O) ∈ Nbar S g t :=
      (F.ker _).mp (by rw [map_mul, map_inv, hwπ, inv_mul_cancel])
    have := mul_mem hwK (Nbar_le_fixWstar hCE X hn)
    simpa using this
  obtain ⟨w₁, hw₁⟩ : ∃ w : Rbar S g t, w = r₁ * ⟨x, hxR⟩ * r₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w : Rbar S g t, w = r₂ * ⟨x, hxR⟩ * r₂⁻¹ := ⟨_, rfl⟩
  have hw₁K : (w₁ : S.O) ∈ fixWstar X := by
    have e : (w₁ : S.O) = (r₁ : S.O) * x * (r₁ : S.O)⁻¹ := by rw [hw₁]; simp
    rw [e]; exact hc₁
  have hw₂K : (w₂ : S.O) ∈ fixWstar X := by
    have e : (w₂ : S.O) = (r₂ : S.O) * x * (r₂ : S.O)⁻¹ := by rw [hw₂]; simp
    rw [e]; exact hc₂
  have hπw₁ : F.π w₁ = δ₁ * τ₁ * δ₁⁻¹ := by rw [hw₁, map_mul, map_mul, map_inv, hr₁, hπx]
  have hπw₂ : F.π w₂ = δ₂ * τ₁ * δ₂⁻¹ := by rw [hw₂, map_mul, map_mul, map_inv, hr₂, hπx]
  rcases hδ with h1 | h2
  · exact key w₁ hw₁K (by rw [hπw₁, h1])
  · refine key (w₁ * w₂) ?_ (by rw [map_mul, hπw₁, hπw₂, h2])
    rw [Subgroup.coe_mul]
    exact mul_mem hw₁K hw₂K

end Assembly

end CFSG.LargeExtraspecial.S10
