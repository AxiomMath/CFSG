module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWMLab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWMModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section Twin

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} (I : AEIdent P 7)

theorem twin_calculus {R₁ R₁' R₂ : Subgroup G} (hR₁ : R₁ ≤ pSpan P) (hR₁' : R₁' ≤ pSpan P)
    (hR₂ : R₂ ≤ pSpan P) (h8₁ : Nat.card R₁ = 8) (h8₁' : Nat.card R₁' = 8) (h8₂ : Nat.card R₂ = 8)
    (hl₁ : ∃ (α : Finset (Fin 7)) (h : α.card = 4) (c : Bool),
      (R₁.subgroupOf (pSpan P)).map I.φ = memBar α h c)
    (hl₁' : ∃ (α : Finset (Fin 7)) (h : α.card = 4) (c : Bool),
      (R₁'.subgroupOf (pSpan P)).map I.φ = memBar α h c)
    (hl₂ : ∃ (α : Finset (Fin 7)) (h : α.card = 4) (c : Bool),
      (R₂.subgroupOf (pSpan P)).map I.φ = memBar α h c)
    {t v b₁ b' k e : G} (ht₁ : IsUniqueInvolution R₁ t) (ht₁' : IsUniqueInvolution R₁' t)
    (hv₂ : IsUniqueInvolution R₂ v) (hb₁ : b₁ ∈ R₁) (hb' : b' ∈ R₁')
    (hcomm : ∀ x ∈ R₁, ∀ y ∈ R₁', x * y = y * x)
    (hk : k ∈ R₁) (hkb : k * b₁ ≠ b₁ * k) (hkt : k * t = t * k)
    (he : e = b₁ * b' * v) (heR₁ : ∀ x ∈ R₁, x * e = e * x) (heR₁' : ∀ x ∈ R₁', x * e = e * x) :
    ∃ (he' : e ∈ pSpan P) (α₀ : Finset (Fin 7)) (h₀ : α₀.card = 4),
      I.φ ⟨t, hR₁ ht₁.mem⟩ = zBar α₀ h₀ ∧ I.φ ⟨e, he'⟩ ≠ 1 ∧ I.φ ⟨e, he'⟩ ≠ zBar α₀ h₀ ∧
      ∀ c : Bool, ∀ x ∈ memBar α₀ h₀ c, I.φ ⟨e, he'⟩ * x = x * I.φ ⟨e, he'⟩ := by
  classical
  have hn : (5 : ℕ) ≤ 7 := by norm_num
  obtain ⟨α₀, h₀, c₀, hl₁⟩ := hl₁
  obtain ⟨α₁, h₁, c₁, hl₁'⟩ := hl₁'
  obtain ⟨αg, hg, cg, hl₂⟩ := hl₂
  have ht₁X : t ∈ pSpan P := hR₁ ht₁.mem
  have hφt₀ : I.φ ⟨t, ht₁X⟩ = zBar α₀ h₀ := map_eq_zBar_of_label I hn hR₁ h8₁ hl₁ ht₁
  have hφt₁ : I.φ ⟨t, ht₁X⟩ = zBar α₁ h₁ := map_eq_zBar_of_label I hn hR₁' h8₁' hl₁' ht₁'
  have hα₁ : α₁ = α₀ := eq_of_zBar_eq (by norm_num) (hφt₁.symm.trans hφt₀)
  subst hα₁
  have hφv : I.φ ⟨v, hR₂ hv₂.mem⟩ = zBar αg hg := map_eq_zBar_of_label I hn hR₂ h8₂ hl₂ hv₂
  have hcc : c₁ ≠ c₀ := by
    intro hc
    subst hc
    obtain ⟨x, hx, x', hx', hne⟩ := exists_not_comm_memBar hn α₁ h₁ c₁
    rw [← hl₁] at hx
    rw [← hl₁'] at hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hx'
    apply hne
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp hy) _ (Subgroup.mem_subgroupOf.mp hy'))
  have hb₁X : b₁ ∈ pSpan P := hR₁ hb₁
  have hb'X : b' ∈ pSpan P := hR₁' hb'
  have hubX : b₁ * b' ∈ pSpan P := (pSpan P).mul_mem hb₁X hb'X
  have hφb₁ : I.φ ⟨b₁, hb₁X⟩ ∈ memBar α₁ h₁ c₀ := by
    rw [← hl₁]
    exact ⟨⟨b₁, hb₁X⟩, Subgroup.mem_subgroupOf.mpr hb₁, rfl⟩
  have hφb' : I.φ ⟨b', hb'X⟩ ∈ memBar α₁ h₁ c₁ := by
    rw [← hl₁']
    exact ⟨⟨b', hb'X⟩, Subgroup.mem_subgroupOf.mpr hb', rfl⟩
  obtain ⟨k₁, hk₁, hk₁φ⟩ := hφb₁
  obtain ⟨k₂, hk₂, hk₂φ⟩ := hφb'
  have hu_supp : SupportedOn (k₁ * k₂) (↑α₁ : Set (Fin 7)) := by
    have s1 := supportedOn_of_mem_memAt hk₁
    have s2 := supportedOn_of_mem_memAt hk₂
    rw [range_emb] at s1 s2
    exact s1.mul s2
  have hu_ae : k₁ * k₂ ∈ aeSub 7 :=
    (aeSub 7).mul_mem (mem_aeSub_of_mem_memAt hk₁) (mem_aeSub_of_mem_memAt hk₂)
  have hs : I.φ ⟨b₁ * b', hubX⟩ = mkQ 7 (k₁ * k₂) := by
    have : (⟨b₁ * b', hubX⟩ : ↥(pSpan P)) = ⟨b₁, hb₁X⟩ * ⟨b', hb'X⟩ := rfl
    rw [this, map_mul, ← hk₁φ, ← hk₂φ, map_mul]
  have hvX : v ∈ pSpan P := hR₂ hv₂.mem
  have heX : e ∈ pSpan P := by
    rw [he]
    exact (pSpan P).mul_mem hubX hvX
  have hφe : I.φ ⟨e, heX⟩ = mkQ 7 (k₁ * k₂) * zBar αg hg := by
    have : (⟨e, heX⟩ : ↥(pSpan P)) = ⟨b₁ * b', hubX⟩ * ⟨v, hvX⟩ := Subtype.ext he
    rw [this, map_mul, hs, hφv]
  have hnu : I.φ ⟨b₁ * b', hubX⟩ ≠ 1 := by
    intro h1
    have hker : (⟨b₁ * b', hubX⟩ : ↥(pSpan P)) ∈ I.φ.ker := h1
    have hcent := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (I.ker_le hker) ⟨k, hR₁ hk⟩)
    have hcent' : k * (b₁ * b') = b₁ * b' * k := hcent
    apply hkb
    have hkb' : k * b' = b' * k := hcomm k hk b' hb'
    calc k * b₁ = (k * (b₁ * b')) * b'⁻¹ := by group
      _ = ((b₁ * b') * k) * b'⁻¹ := by rw [hcent']
      _ = b₁ * (b' * k) * b'⁻¹ := by group
      _ = b₁ * (k * b') * b'⁻¹ := by rw [hkb']
      _ = b₁ * k := by group
  have hnut : I.φ ⟨b₁ * b', hubX⟩ ≠ I.φ ⟨t, ht₁X⟩ := by
    intro h1
    have hker : (⟨b₁ * b', hubX⟩ * ⟨t, ht₁X⟩ : ↥(pSpan P)) ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, h1, hφt₀]
      exact zBar_mul_self α₁ h₀
    have hcent := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (I.ker_le hker) ⟨k, hR₁ hk⟩)
    have hcent' : k * (b₁ * b' * t) = b₁ * b' * t * k := hcent
    apply hkb
    have hkb' : k * b' = b' * k := hcomm k hk b' hb'
    calc k * b₁ = (k * (b₁ * b' * t)) * (b' * t)⁻¹ := by group
      _ = ((b₁ * b' * t) * k) * (b' * t)⁻¹ := by rw [hcent']
      _ = b₁ * (b' * (t * k)) * (b' * t)⁻¹ := by group
      _ = b₁ * (b' * (k * t)) * (b' * t)⁻¹ := by rw [hkt]
      _ = b₁ * ((b' * k) * t) * (b' * t)⁻¹ := by group
      _ = b₁ * ((k * b') * t) * (b' * t)⁻¹ := by rw [hkb']
      _ = b₁ * k := by group
  have hnd1 : I.φ ⟨e, heX⟩ ≠ 1 := by
    intro h1
    rw [hφe] at h1
    have h2 : mkQ 7 (k₁ * k₂) = zBar αg hg := by
      have : mkQ 7 (k₁ * k₂) = (zBar αg hg)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right (zBar_mul_self αg hg)
    have hαg := eq_of_supported_eq_zBar hu_ae h₁ hg hu_supp h2
    subst hαg
    exact hnut (by rw [hs, h2, hφt₀])
  have hnd2 : I.φ ⟨e, heX⟩ ≠ zBar α₁ h₁ := by
    intro h1
    rw [hφe] at h1
    have h2 : mkQ 7 (k₁ * k₂) = zBar α₁ h₁ * zBar αg hg := by
      have h3 : mkQ 7 (k₁ * k₂) = zBar α₁ h₁ * (zBar αg hg)⁻¹ := eq_mul_inv_of_mul_eq h1
      rw [h3, inv_eq_of_mul_eq_one_right (zBar_mul_self αg hg)]
    have hαg := eq_of_supported_eq_zBar_mul hu_ae h₁ hg hu_supp h2
    subst hαg
    apply hnu
    rw [hs, h2]
    exact zBar_mul_self _ _
  refine ⟨heX, α₁, h₁, hφt₀, hnd1, hnd2, ?_⟩
  intro c x hx
  have hc : c = c₀ ∨ c = c₁ := by
    cases c <;> cases c₀ <;> cases c₁ <;> simp_all
  rcases hc with rfl | rfl
  · rw [← hl₁] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (heR₁ _ (Subgroup.mem_subgroupOf.mp hy)).symm
  · rw [← hl₁'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (heR₁' _ (Subgroup.mem_subgroupOf.mp hy)).symm

end Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM
