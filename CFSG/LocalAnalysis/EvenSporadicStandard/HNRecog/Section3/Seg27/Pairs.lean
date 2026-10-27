module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Pair01
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem seg27_pair_six_six {H : Type} [Group H] [Finite H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    (hA : ∀ h, θ h ∈ alternatingGroup (Fin 8)) {K₀ K₁ : Subgroup H}
    (h₀ : IsShapeZ2TimesSym 6 ↥K₀) (h₁ : IsShapeZ2TimesSym 6 ↥K₁) :
    ∃ t ∈ K₀ ⊓ K₁, orderOf t = 2 := by
  obtain ⟨p, q, -, hY₀⟩ := seg27_bridge_six φ hθ hA h₀
  obtain ⟨p', q', -, hY₁⟩ := seg27_bridge_six φ hθ hA h₁
  obtain ⟨g, hg, hg2⟩ := seg27_exists_inv_altFix_inf p q p' q'
  have hg₁ : g ∈ seg27AltFix {p, q} := (Subgroup.mem_inf.mp hg).1
  have hg₂ : g ∈ seg27AltFix {p', q'} := (Subgroup.mem_inf.mp hg).2
  have hs₀ : g ∈ (derivedOf K₀).map θ := by rw [hY₀]; exact hg₁
  have hs₁ : g ∈ (derivedOf K₁).map θ := by rw [hY₁]; exact hg₂
  obtain ⟨k, hk, hk2⟩ := seg27_lift_comm φ hθ (seg27_derivedOf_le_commutator K₀)
    (seg27_derivedOf_le_commutator K₁) hs₀ hs₁ hg2
  have hk₀ : k ∈ derivedOf K₀ := (Subgroup.mem_inf.mp hk).1
  have hk₁ : k ∈ derivedOf K₁ := (Subgroup.mem_inf.mp hk).2
  exact ⟨k, Subgroup.mem_inf.mpr ⟨derivedOf_le K₀ hk₀, derivedOf_le K₁ hk₁⟩, hk2⟩

theorem seg27_pair_five_six {H : Type} [Group H] [Finite H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    (hA : ∀ h, θ h ∈ alternatingGroup (Fin 8)) (hker : θ.ker = Subgroup.center H)
    {a : H} {K₀ K₁ : Subgroup H} (h₀ : Seg27Five φ a K₀) (h₁ : IsShapeZ2TimesSym 6 ↥K₁) :
    ∃ t ∈ K₀ ⊓ K₁, orderOf t = 2 := by
  obtain ⟨-, p, q, hSix⟩ := seg27_bridge_five φ hθ hA hker h₀
  obtain ⟨p', q', -, hY₁⟩ := seg27_bridge_six φ hθ hA h₁
  obtain ⟨t, ht, ht2, htp, htq⟩ := hSix.inv_fix2 p' q'
  have htA : t ∈ alternatingGroup (Fin 8) := hSix.le_alt ht
  have htfix : t ∈ seg27AltFix {p', q'} := by
    rw [seg27_mem_altFix]
    refine ⟨htA, ?_⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact htp
    · exact htq
  have ht₁ : t ∈ (derivedOf K₁).map θ := by rw [hY₁]; exact htfix
  obtain ⟨k, hk, hk2⟩ := seg27_lift_comm φ hθ (seg27_derivedOf_le_commutator K₀)
    (seg27_derivedOf_le_commutator K₁) ht ht₁ ht2
  have hk₀ : k ∈ derivedOf K₀ := (Subgroup.mem_inf.mp hk).1
  have hk₁ : k ∈ derivedOf K₁ := (Subgroup.mem_inf.mp hk).2
  exact ⟨k, Subgroup.mem_inf.mpr ⟨derivedOf_le K₀ hk₀, derivedOf_le K₁ hk₁⟩, hk2⟩

theorem seg27_pair_five_five {H : Type} [Group H] [Finite H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    (hA : ∀ h, θ h ∈ alternatingGroup (Fin 8)) (hker : θ.ker = Subgroup.center H) {a b : H}
    (hZ : (Subgroup.center H : Set H) = {1, a, b, a * b})
    (hsq : ∀ z ∈ Subgroup.center H, z * z = 1) (hab : a ≠ b) {K₀ K₁ : Subgroup H}
    (h₀ : Seg27Five φ a K₀) (h₁ : Seg27Five φ b K₁) :
    ∃ t ∈ K₀ ⊓ K₁, orderOf t = 2 := by
  obtain ⟨hc₀, p₀, q₀, hX₀⟩ := seg27_bridge_five φ hθ hA hker h₀
  obtain ⟨hc₁, p₁, q₁, hX₁⟩ := seg27_bridge_five φ hθ hA hker h₁
  have hS₀ : K₀.map θ ≤ alternatingGroup (Fin 8) := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hA k
  have hS₁ : K₁.map θ ≤ alternatingGroup (Fin 8) := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hA k
  have hle₀ : (derivedOf K₀).map θ ≤ K₀.map θ := Subgroup.map_mono (derivedOf_le K₀)
  have hle₁ : (derivedOf K₁).map θ ≤ K₁.map θ := Subgroup.map_mono (derivedOf_le K₁)
  obtain ⟨s, hs, hs2⟩ := seg27_pair01 hX₀ hX₁ hS₀ hS₁ hc₀ hc₁ hle₀ hle₁
  exact seg27_lift_center hker hZ hsq hab h₀.inf_center h₁.inf_center
    (Subgroup.mem_inf.mp hs).1 (Subgroup.mem_inf.mp hs).2 hs2

end CFSG.EvenSporadicStandard.HNRecog.Section3
