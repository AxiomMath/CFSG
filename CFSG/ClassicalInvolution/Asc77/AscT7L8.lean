module

public import CFSG.ClassicalInvolution.Asc77.AscT7L7

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T7L

section QuotGen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_oddCore_of_mk_conj {Y : Subgroup G} {t t' : G} (ht : t ∈ Y) (ht' : t' ∈ Y)
    (y : ↥Y)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨t, ht⟩ *
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y)⁻¹ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨t', ht'⟩) :
    t⁻¹ * ((y : G)⁻¹ * t' * (y : G)) ∈ oddCoreOf Y := by
  set e₀ : ↥Y := (⟨t, ht⟩ : ↥Y)⁻¹ * (y⁻¹ * ⟨t', ht'⟩ * y) with he₀
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) e₀ = 1 := by
    simp only [he₀, map_mul, map_inv]
    rw [← h]
    group
  have h2 : e₀ ∈ classicalInvolutionOddCore ↥Y := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_map.mpr ⟨e₀, h2, rfl⟩

theorem layer_le_of_quot_gen {Y : Subgroup G} {s₁ s₂ s₃ : G} (h₁ : s₁ ∈ Y) (h₂ : s₂ ∈ Y)
    (h₃ : s₃ ∈ Y) (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1) (hs₃ : s₃ * s₃ = 1) (hn₁ : s₁ ≠ 1)
    (hn₂ : s₂ ≠ 1) (hn₃ : s₃ ≠ 1)
    (hgen : (⊤ : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)) =
      Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨s₁, h₁⟩} :
          Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)) ⊔
        Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨s₂, h₂⟩} :
          Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)) ⊔
        Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨s₃, h₃⟩} :
          Set (↥Y ⧸ classicalInvolutionOddCore ↥Y))) :
    Y ≤ oddCoreOf Y ⊔ (Y ⊓ Subgroup.centralizer ({s₁} : Set G)) ⊔
      (Y ⊓ Subgroup.centralizer ({s₂} : Set G)) ⊔ (Y ⊓ Subgroup.centralizer ({s₃} : Set G)) := by
  classical
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  set π := QuotientGroup.mk' N₀ with hπ
  set Λ : Subgroup G := oddCoreOf Y ⊔ (Y ⊓ Subgroup.centralizer ({s₁} : Set G)) ⊔
    (Y ⊓ Subgroup.centralizer ({s₂} : Set G)) ⊔ (Y ⊓ Subgroup.centralizer ({s₃} : Set G))
    with hΛ
  have hNodd : Odd (Nat.card ↥(oddCoreOf Y)) := oddCoreOf_odd_natCard Y
  have hNΛ : oddCoreOf Y ≤ Λ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hA₁ : Y ⊓ Subgroup.centralizer ({s₁} : Set G) ≤ Λ :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hA₂ : Y ⊓ Subgroup.centralizer ({s₂} : Set G) ≤ Λ := le_sup_right.trans le_sup_left
  have hA₃ : Y ⊓ Subgroup.centralizer ({s₃} : Set G) ≤ Λ := le_sup_right
  have hN₀Λ : N₀ ≤ Λ.subgroupOf Y := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    exact hNΛ (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  have hlift : ∀ (s : G) (hsY : s ∈ Y), s * s = 1 → s ≠ 1 →
      Y ⊓ Subgroup.centralizer ({s} : Set G) ≤ Λ → ∀ y : ↥Y,
        π y ∈ Subgroup.centralizer ({π ⟨s, hsY⟩} : Set (↥Y ⧸ N₀)) → y ∈ Λ.subgroupOf Y := by
    intro s hsY hs2 hs1 hA y hy
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    set e₀ : ↥Y := (⟨s, hsY⟩ : ↥Y)⁻¹ * (y * ⟨s, hsY⟩ * y⁻¹) with he₀
    have h1 : π e₀ = 1 := by
      simp only [he₀, map_mul, map_inv]
      rw [hy']
      group
    have h2 : e₀ ∈ N₀ := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : s⁻¹ * ((y : G) * s * (y : G)⁻¹) ∈ oddCoreOf Y :=
      Subgroup.mem_map.mpr ⟨e₀, h2, rfl⟩
    obtain ⟨n, hn, c, hc, hyc⟩ := exists_mul_centralizer_of_comm_mod hNodd hs2 hs1
      (normalizer_oddCoreIn Y hsY) h3
    have hnY : n ∈ Y := oddCoreIn_le Y hn
    have hcY : c ∈ Y := by
      have : c = n⁻¹ * (y : G) := by rw [hyc]; group
      rw [this]
      exact Y.mul_mem (Y.inv_mem hnY) y.2
    rw [Subgroup.mem_subgroupOf, hyc]
    exact Λ.mul_mem (hNΛ hn) (hA ⟨hcY, hc⟩)
  have hC₁ : Subgroup.centralizer ({π ⟨s₁, h₁⟩} : Set (↥Y ⧸ N₀)) ≤ (Λ.subgroupOf Y).map π := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact Subgroup.mem_map.mpr ⟨y, hlift s₁ h₁ hs₁ hn₁ hA₁ y hx, rfl⟩
  have hC₂ : Subgroup.centralizer ({π ⟨s₂, h₂⟩} : Set (↥Y ⧸ N₀)) ≤ (Λ.subgroupOf Y).map π := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact Subgroup.mem_map.mpr ⟨y, hlift s₂ h₂ hs₂ hn₂ hA₂ y hx, rfl⟩
  have hC₃ : Subgroup.centralizer ({π ⟨s₃, h₃⟩} : Set (↥Y ⧸ N₀)) ≤ (Λ.subgroupOf Y).map π := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact Subgroup.mem_map.mpr ⟨y, hlift s₃ h₃ hs₃ hn₃ hA₃ y hx, rfl⟩
  intro y hyY
  have hmem : π ⟨y, hyY⟩ ∈ (⊤ : Subgroup (↥Y ⧸ N₀)) := Subgroup.mem_top _
  rw [hgen] at hmem
  obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.mp ((sup_le (sup_le hC₁ hC₂) hC₃) hmem)
  have hq : l⁻¹ * ⟨y, hyY⟩ ∈ N₀ := by
    have h1 : π (l⁻¹ * ⟨y, hyY⟩) = 1 := by
      rw [map_mul, map_inv, hly]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have : (⟨y, hyY⟩ : ↥Y) = l * (l⁻¹ * ⟨y, hyY⟩) := by group
  have hyΛ : (⟨y, hyY⟩ : ↥Y) ∈ Λ.subgroupOf Y := by
    rw [this]
    exact (Λ.subgroupOf Y).mul_mem hl (hN₀Λ hq)
  exact Subgroup.mem_subgroupOf.mp hyΛ

end QuotGen

end T7L

end CFSG.ClassicalInvolution.Asc77
