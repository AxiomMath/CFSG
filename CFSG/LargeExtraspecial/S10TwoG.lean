module

public import CFSG.LargeExtraspecial.S10TwoF
public import CFSG.LargeExtraspecial.S10TwoE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem commute_conj_of_commute {X : Type*} [Group X] {a r y : X}
    (h : Commute (a⁻¹ * r * a⁻¹⁻¹) y) : Commute r (a * y * a⁻¹) := by
  have h' : a⁻¹ * r * a⁻¹⁻¹ * y = y * (a⁻¹ * r * a⁻¹⁻¹) := h
  show r * (a * y * a⁻¹) = a * y * a⁻¹ * r
  calc r * (a * y * a⁻¹) = a * ((a⁻¹ * r * a⁻¹⁻¹) * y) * a⁻¹ := by group
    _ = a * (y * (a⁻¹ * r * a⁻¹⁻¹)) * a⁻¹ := by rw [h']
    _ = a * y * a⁻¹ * r := by group

theorem conj_mul_conj_eq_inv {X : Type*} [Group X] {a y : X} (hy : y * y = 1) :
    y * (y * (a * y * a⁻¹)) * y⁻¹ = (y * (a * y * a⁻¹))⁻¹ := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc y * (y * (a * y * a⁻¹)) * y⁻¹ = (y * y) * (a * y * a⁻¹) * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [hy, one_mul]
    _ = a * y⁻¹ * a⁻¹ * y⁻¹ := by rw [hyinv]
    _ = (y * (a * y * a⁻¹))⁻¹ := by group

theorem exists_complement_y (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {x : S.O} (hxL : x ∈ S.Lbar g) (hxW : x ∈ fixWstar X)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) :
    ∃ y ∈ S.Lbar g, ∃ hyR : y ∈ Rbar S g t, F.π ⟨y, hyR⟩ = τ₂ ∧
      (∀ r ∈ F.pre Γ₁, Commute r y) := by
  have hxR := Lbar_le_Rbar X.ht hxL
  obtain ⟨k, hkR, hk3, hπk⟩ := F.exists_cube_lift hCE σ₁_spec.2.1
  have hs : (F.π ⟨S.ρ k, hkR⟩).2 = 1 := by rw [hπk]; exact σ₁_spec.1
  have hs3 : (F.π ⟨S.ρ k, hkR⟩) ^ 3 = 1 := by rw [hπk]; exact σ₁_spec.2.1
  have hs1 : F.π ⟨S.ρ k, hkR⟩ ≠ 1 := by rw [hπk]; exact σ₁_spec.2.2
  have hkpre : S.ρ k ∈ F.pre Γ₁ := (F.mem_pre).mpr ⟨hkR, mem_Γ₁.mpr hs⟩
  have hkW : S.ρ k ∈ fixWstar X := pre_Γ₁_le_fixWstar hCE X F hxL hxW hπx hkpre
  have hinf := Abar_inf_Lbar_conj X F hkR hkW hs hs3 hs1
  have hN := Nbar_eq_sup_of_inf hCE X hkR hinf
  obtain ⟨y, hy, hπy⟩ := exists_Lbar_inf_π_eq_τ₂ hCE X F hkR hs hinf
  have hyR := Lbar_le_Rbar X.ht hy.1
  have hyN : ∀ n ∈ Nbar S g t, n * y = y * n := fun n hn =>
    comm_of_mem_sup_of_mem_inf X hy (hN ▸ hn)
  have hhy : Commute (S.ρ k) y := comm_h_of_mem_inf X F hxL hπx hkR hk3 hs hs3 hy hyN
  have hxy : Commute x y := S4.Lbar_comm S X.haQ hxL hy.1
  have hyy : y * y = 1 := S4.mul_self_of_mem_Lbar S X.haQ hy.1
  have hR0y : ∀ r ∈ F.pre Γ₁, Commute r y := by
    intro r hr
    obtain ⟨hrR, hrπ⟩ := (F.mem_pre).mp hr
    obtain ⟨i, -, j, -, hij⟩ := Γ₁_gen _ σ₁_spec.1 σ₁_spec.2.1 σ₁_spec.2.2 _ (mem_Γ₁.mp hrπ)
    obtain ⟨w, hwd⟩ : ∃ w : Rbar S g t, w = ⟨x, hxR⟩ ^ j * ⟨S.ρ k, hkR⟩ ^ i := ⟨_, rfl⟩
    have hwc : (w : S.O) = x ^ j * (S.ρ k) ^ i := by rw [hwd]; simp
    have hπw : F.π w = τ₁ ^ j * σ₁ ^ i := by rw [hwd, map_mul, map_pow, map_pow, hπx, hπk]
    have hn : ((w⁻¹ * ⟨r, hrR⟩ : Rbar S g t) : S.O) ∈ Nbar S g t :=
      (F.ker _).mp (by rw [map_mul, map_inv, hπw, ← hij, inv_mul_cancel])
    have hrw : r = (x ^ j * (S.ρ k) ^ i) * ((w⁻¹ * ⟨r, hrR⟩ : Rbar S g t) : S.O) := by
      rw [← hwc]; simp
    exact hrw ▸ ((hxy.pow_left j).mul_left (hhy.pow_left i)).mul_left (hyN _ hn)
  exact ⟨y, hy.1, hyR, hπy, hR0y⟩

theorem exists_complement_d (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {y : S.O} (hyL : y ∈ S.Lbar g) (hπy : F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂)
    (hR0y : ∀ r ∈ F.pre Γ₁, Commute r y) :
    ∃ d : Rbar S g t, d ^ 3 = 1 ∧ (F.π d).1 = 1 ∧ F.π d ^ 3 = 1 ∧ F.π d ≠ 1 ∧
      (∀ r ∈ F.pre Γ₁, Commute r (d : S.O)) ∧ y * (d : S.O) * y⁻¹ = (d : S.O)⁻¹ := by
  have hyy : y * y = 1 := S4.mul_self_of_mem_Lbar S X.haQ hyL
  obtain ⟨rd, hrd⟩ := F.surj σ₂
  obtain ⟨yR, hyRc⟩ : ∃ yR : Rbar S g t, yR = ⟨y, Lbar_le_Rbar X.ht hyL⟩ := ⟨_, rfl⟩
  have hπyR : F.π yR = τ₂ := by rw [hyRc]; exact hπy
  have hyRv : (yR : S.O) = y := by rw [hyRc]
  have hexd : ∃ d₀ : Rbar S g t, d₀ = yR * (rd * yR * rd⁻¹) := ⟨_, rfl⟩
  obtain ⟨d₀, hd₀⟩ := hexd
  have hd₀c : (d₀ : S.O) = y * ((rd : S.O) * y * (rd : S.O)⁻¹) := by
    rw [hd₀, ← hyRv]
    simp
  have hδall := τ₂_conj_mul σ₂ σ₂_spec.1 σ₂_spec.2.1 σ₂_spec.2.2
  have hπd₀ : F.π d₀ = τ₂ * (σ₂ * τ₂ * σ₂⁻¹) := by
    rw [hd₀]
    simp only [map_mul, map_inv, hrd, hπyR]
  have hcube : F.π d₀ ^ 3 = 1 := by rw [hπd₀]; exact hδall.1
  have hpow := F.exists_pow_cube hCE hcube
  obtain ⟨e, he3, heπ⟩ := hpow
  have hR0y' : ∀ r ∈ F.pre Γ₁, Commute r ((rd : S.O) * y * (rd : S.O)⁻¹) := fun r hr =>
    commute_conj_of_commute (hR0y _ (F.conj_mem_pre_Γ₁ (inv_mem rd.2) hr))
  have hR0d₀ : ∀ r ∈ F.pre Γ₁, Commute r (d₀ : S.O) := fun r hr =>
    (congrArg (Commute r) hd₀c).mpr ((hR0y r hr).mul_right (hR0y' r hr))
  have hconj : y * (d₀ : S.O) * y⁻¹ = (d₀ : S.O)⁻¹ := by
    have := conj_mul_conj_eq_inv (a := (rd : S.O)) hyy
    rw [← hd₀c] at this
    exact this
  refine ⟨d₀ ^ (4 ^ e), he3, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [heπ, hπd₀]
    exact hδall.2.2
  · rw [heπ, hπd₀]
    exact hδall.1
  · rw [heπ, hπd₀]
    exact hδall.2.1
  · rw [Subgroup.coe_pow]
    exact (hR0d₀ r hr).pow_right _
  · rw [Subgroup.coe_pow, ← conj_pow, hconj, inv_pow]

end CFSG.LargeExtraspecial.S10
