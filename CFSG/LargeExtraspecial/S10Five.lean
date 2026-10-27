module

public import CFSG.LargeExtraspecial.S10FiveB
public import CFSG.LargeExtraspecial.S10Conj
public import CFSG.LargeExtraspecial.S5Fus
public import CFSG.LargeExtraspecial.S10FlagC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem stab_c2 : ∀ γ δ : Gm, act γ E00 = E00 → act δ E00 = E00 → γ ≠ 1 → δ ≠ 1 →
    δ * γ ≠ 1 → γ = τ₁ * τ₂ ∨ δ = τ₁ * τ₂ ∨ δ * γ = τ₁ * τ₂ := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem exists_normalizer_conj (X : Hyp10 S g t) {k₀ : S.M}
    (hk₀ : S.ρ k₀ * t * (S.ρ k₀)⁻¹ ∈ S.Lbar g) :
    ∃ k : S.M, S.ρ k ∈ normalizer (S.Lbar g : Set S.O) ∧
      S.ρ k * t * (S.ρ k)⁻¹ = S.ρ k₀ * t * (S.ρ k₀)⁻¹ := by
  obtain ⟨n, hnM, hnN, hn⟩ := S5.exists_mem_normalizer_conj X.H X.C
    (MonoidHom.mem_range.mpr ⟨k₀, rfl⟩) (fun l hl => S4.Lbar_comm S X.haQ X.ht hl)
    (fun l hl => S4.Lbar_comm S X.haQ hk₀ hl)
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hnM
  exact ⟨k, hnN, hn.symm⟩

theorem timmesfeld_10_5 (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    (h104 : ∃ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t) :
    S.width ≤ 6 ∨ ∃ k : S.M, S.ρ k ∈ normalizer (S.Lbar g : Set S.O) ∧
      S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ⊓ Nbar S g t ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h7, hcl'⟩ := hcon
  have hcl : ∀ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ⊓ Nbar S g t →
      S.ρ k * t * (S.ρ k)⁻¹ = t := by
    intro k₁ hk₁
    obtain ⟨k, hk, hkk₁⟩ := exists_normalizer_conj X hk₁.1
    rw [← hkk₁] at hk₁ ⊢
    exact hcl' k hk hk₁
  obtain ⟨k₀, hk₀L, hk₀t⟩ := h104
  obtain ⟨k, hk, hkk₀⟩ := exists_normalizer_conj X hk₀L
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = S.ρ k * t * (S.ρ k)⁻¹ := ⟨_, rfl⟩
  have hτt : τ ≠ t := by
    rw [hτ, hkk₀]
    exact hk₀t
  have Y := X.conj' hk hτ
  have hNc : Nbar S g τ = (Nbar S g t).map (cK S k) := by
    subst hτ
    exact Nbar_conj X.haQ k t
  have htN : t ∉ Nbar S g τ := by
    intro htN
    rw [hNc, mem_map_cK_iff] at htN
    have hL : (S.ρ k)⁻¹ * t * S.ρ k ∈ S.Lbar g := by
      have := (mem_normalizer_iff.mp (inv_mem hk) t).mp X.ht
      simpa using this
    have h1 := hcl k⁻¹ (by
      rw [map_inv, inv_inv]
      exact Subgroup.mem_inf.mpr ⟨hL, htN⟩)
    rw [map_inv, inv_inv] at h1
    apply hτt
    rw [hτ]
    calc S.ρ k * t * (S.ρ k)⁻¹ = S.ρ k * ((S.ρ k)⁻¹ * t * S.ρ k) * (S.ρ k)⁻¹ := by rw [h1]
      _ = t := by group
  have hW : t ∈ fixWstar Y := mem_fixWstar_of_finrank_le Y X.ht htN (finrank_commSpace_t X).le
  obtain ⟨α, hα, β, hβ, hα1, hβ1, hβα1, hmα, hmβ, hmβα⟩ :=
    exists_conj_pair hCE Y (by omega) X.ht htN hW
  have key : ∀ γ ∈ S.Lbar g ⊓ Nbar S g τ, γ ≠ 1 →
      (∃ m ∈ Nbar S g τ, m * t * m⁻¹ = γ * t) → γ ∉ Nbar S g t := by
    rintro γ hγ hγ1 ⟨m, hm, e⟩ hγN
    obtain ⟨k', hk'⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (Nbar_le_Rbar hm))
    have h1 := hcl k' (by
      rw [hk', e]
      exact mul_mem (Subgroup.mem_inf.mpr ⟨hγ.1, hγN⟩) X.t_mem_Abar)
    rw [hk', e] at h1
    exact hγ1 (by simpa using h1)
  have hαN := key α hα hα1 hmα
  have hβN := key β hβ hβ1 hmβ
  have hβαN := key (β * α) (mul_mem hβ hα) hβα1 hmβα
  obtain ⟨F⟩ := X.exists_frame
  have hne : ∀ x (hx : x ∈ S.Lbar g), x ∉ Nbar S g t → F.π ⟨x, Lbar_le_Rbar X.ht hx⟩ ≠ 1 :=
    fun x hx hxN h => hxN ((F.ker _).mp h)
  have hmul : F.π ⟨β * α, Lbar_le_Rbar X.ht (mul_mem hβ.1 hα.1)⟩ =
      F.π ⟨β, Lbar_le_Rbar X.ht hβ.1⟩ * F.π ⟨α, Lbar_le_Rbar X.ht hα.1⟩ := by
    have e : (⟨β * α, Lbar_le_Rbar X.ht (mul_mem hβ.1 hα.1)⟩ : Rbar S g t) =
        ⟨β, Lbar_le_Rbar X.ht hβ.1⟩ * ⟨α, Lbar_le_Rbar X.ht hα.1⟩ := Subtype.ext (by simp)
    rw [e, map_mul]
  have hc2 : ∀ x (hx : x ∈ S.Lbar g ⊓ Nbar S g τ),
      F.π ⟨x, Lbar_le_Rbar X.ht hx.1⟩ ≠ τ₁ * τ₂ := by
    intro x hx h
    have h1 := width_le_finrank_commSpace hCE X F hx.1 h
    have h2 := finrank_commSpace_le_six hCE Y hx
    omega
  rcases stab_c2 _ _ (F.π_mem_stabA hα.1) (F.π_mem_stabA hβ.1) (hne α hα.1 hαN)
    (hne β hβ.1 hβN) (by rw [← hmul]; exact hne _ (mul_mem hβ.1 hα.1) hβαN) with h | h | h
  · exact hc2 α hα h
  · exact hc2 β hβ h
  · exact hc2 (β * α) (mul_mem hβ hα) (by rw [hmul]; exact h)

end CFSG.LargeExtraspecial.S10
