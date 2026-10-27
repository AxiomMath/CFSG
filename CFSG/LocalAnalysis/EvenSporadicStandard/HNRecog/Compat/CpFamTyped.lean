module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.TypingGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Ext2A

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem cp_typed_base (h : F5Std a z) (h' : F5Std a' z') {t : G} {t' : G'} (ht : IsConj a t)
    (ht' : IsConj a' t') {φ : G → G'} (hφ : IsIsoOn (Gx t) (Gx t') φ) {x : G} (hx : x ∈ Gx t)
    (hxA : IsConj a x) : IsConj a' (φ x) := by
  have hT : F5Std t z := h.of_isConj ht (IsConj.refl z)
  have hT' : F5Std t' z' := h'.of_isConj ht' (IsConj.refl z')
  have hxi : x ∈ InvIn (Gx t) := ⟨hx, h.orderOf_eq_two (Or.inl hxA)⟩
  have hnc : ¬ IsConj a z := h.not_isConj
  rcases inv_cover hT hxi with rfl | h2A | h2B | h2AB | h2BB
  · rw [iso_apply_self hT hT' hφ]
    exact ht'
  · exact ht'.trans (typing_2A hT hT' hφ h2A).1
  · exact ht'.trans (typing_2B hT hT' hφ h2B).1
  · exact absurd (hxA.trans h2AB.1.symm) hnc
  · exact absurd (hxA.trans h2BB.1.symm) hnc

theorem cp_witness_2AB (h : F5Std a z) {b t : G} (hb : IsConj a b) (ht : t ∈ orb2AB b z b) :
    ∃ d : G, IsConj a d ∧ d ∈ Gxy b t ∧ IsConj z (t * d) := by
  have hzt : IsConj z t := ht.1
  have hbQ : b ∈ Qz t := ((h.loc.fusion3 b z hb (IsConj.refl z)).shape_2AB t ht).2
  obtain ⟨z₀, b₀, u, hF, hz₀, -, -, -, -, -⟩ := h.loc.fusion1.self.rep_z
  have hbu := h.loc.fusion2.self.reps_bu z₀ b₀ u hF hz₀
  have huB : IsConj z (u : G) := hbu.2.1
  have hauB : IsConj z (a * (u : G)) := hbu.2.2.1
  obtain ⟨g, hg⟩ := isConj_iff.mp (huB.symm.trans hzt)
  set a₁ : G := g * a * g⁻¹ with ha₁_def
  have ha₁A : IsConj a a₁ := isConj_iff.mpr ⟨g, ha₁_def.symm⟩
  have hua : a * (u : G) = (u : G) * a := mem_Gx.1 u.2
  have ha₁t : a₁ ∈ Gx t := by
    rw [mem_Gx, ha₁_def]
    calc t * (g * a * g⁻¹) = (g * (u : G) * g⁻¹) * (g * a * g⁻¹) := by rw [← hg]
      _ = g * ((u : G) * a) * g⁻¹ := by group
      _ = g * (a * (u : G)) * g⁻¹ := by rw [← hua]
      _ = (g * a * g⁻¹) * (g * (u : G) * g⁻¹) := by group
      _ = (g * a * g⁻¹) * t := by rw [← hg]
  have hta₁ : IsConj z (t * a₁) := by
    have h1 : IsConj z ((u : G) * a) := by
      rw [← hua]
      exact hauB
    refine h1.trans (isConj_iff.mpr ⟨g, ?_⟩)
    show g * ((u : G) * a) * g⁻¹ = t * a₁
    rw [ha₁_def, ← hg]
    group
  have hat : a₁ * t = t * a₁ := (mem_Gx.1 ha₁t).symm
  have hq : IsConj t (a₁ * t) := by
    have h2 : IsConj z (a₁ * t) := by rw [hat]; exact hta₁
    exact hzt.symm.trans h2
  have hstruct := h.loc.structGz a t (IsConj.refl a) hzt
  have hy4afacts := h.loc.y4a a t (IsConj.refl a) hzt
  obtain ⟨c, hcO2, hcA⟩ := (hstruct.y4b a₁ ha₁t ha₁A hq).orbit_2A.nonempty
  have hy4a := hy4afacts.y4a a₁ ha₁t ha₁A hq
  have hcO2' : c ∈ derivedOf (Gxy a₁ t) ⊓ Qz t ⊓ Qz (a₁ * t) := by
    simpa [hy4a.pCore] using hcO2
  have hcD : c ∈ derivedOf (Gxy a₁ t) := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hcO2').1).1
  have hcQ : c ∈ Qz t := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hcO2').1).2
  have hcGx_a₁ : c ∈ Gx a₁ := (mem_Gxy.1 (derivedOf_le _ hcD)).1
  obtain ⟨k, hkGxt, hkc⟩ :=
    (h.loc.gzOrbit a t (IsConj.refl a) hzt).orbit_QA.1.transitive c ⟨hcQ, hcA⟩ b ⟨hbQ, hb⟩
  refine ⟨k * a₁ * k⁻¹, ha₁A.trans (isConj_iff.mpr ⟨k, rfl⟩), ?_, ?_⟩
  · refine mem_Gxy.mpr ⟨?_, ?_⟩
    · rw [mem_Gx]
      calc b * (k * a₁ * k⁻¹) = (k * c * k⁻¹) * (k * a₁ * k⁻¹) := by rw [hkc]
        _ = k * (c * a₁) * k⁻¹ := by group
        _ = k * (a₁ * c) * k⁻¹ := by rw [(mem_Gx.1 hcGx_a₁).symm]
        _ = (k * a₁ * k⁻¹) * (k * c * k⁻¹) := by group
        _ = (k * a₁ * k⁻¹) * b := by rw [hkc]
    · exact (Gx t).mul_mem ((Gx t).mul_mem hkGxt ha₁t) ((Gx t).inv_mem hkGxt)
  · refine hta₁.trans (isConj_iff.mpr ⟨k, ?_⟩)
    show k * (t * a₁) * k⁻¹ = t * (k * a₁ * k⁻¹)
    calc k * (t * a₁) * k⁻¹ = (k * t) * a₁ * k⁻¹ := by group
      _ = (t * k) * a₁ * k⁻¹ := by rw [← mem_Gx.1 hkGxt]
      _ = t * (k * a₁ * k⁻¹) := by group

theorem cp_typed_of_iso (h : F5Std a z) (h' : F5Std a' z') {b : G} (hb : IsConj a b) {β : G → G'}
    (hb' : IsConj a' (β b)) (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {t : G} (ht : t ∈ InvIn (Gx b))
    {φ : G → G'} (hφ : IsIsoOn (Gx t) (Gx (β t)) φ) (hres : ∀ x ∈ Gxy b t, φ x = β x) {x : G}
    (hx : x ∈ Gx t) (hxA : IsConj a x) : IsConj a' (φ x) := by
  have hB : F5Std b z := h.of_isConj hb (IsConj.refl z)
  have hB' : F5Std (β b) z' := h'.of_isConj hb' (IsConj.refl z')
  have hbt : b ∈ Gx t := mem_Gx.2 (mem_Gx.1 ht.1).symm
  rcases inv_cover hB ht with rfl | h2A | h2B | h2AB | h2BB
  · exact cp_typed_base h h' hb hb' hφ hx hxA
  · exact cp_typed_base h h' (hb.trans h2A.1) (hb'.trans (typing_2A hB hB' hβ h2A).1) hφ hx hxA
  · exact cp_typed_base h h' (hb.trans h2B.1) (hb'.trans (typing_2B hB hB' hβ h2B).1) hφ hx hxA
  · obtain ⟨d, hdA, hdbt, hdz⟩ := cp_witness_2AB h hb h2AB
    have hw' : IsConj z' (β t) := (typing_2AB hB hB' hβ h2AB).1
    have hd : IsConj a' (φ d) := by
      rw [hres d hdbt]
      exact cp_typed_base h h' hb hb' hβ (mem_Gxy.1 hdbt).1 hdA
    exact typing_Gz h h' h2AB.1 hw' hφ hdA ⟨(mem_Gxy.1 hdbt).2, hdz⟩ hd x hx hxA
  · have hw' : IsConj z' (β t) := (typing_2BB hB hB' hβ h2BB).1
    have hd : IsConj a' (φ b) := by
      rw [hres b (mem_Gxy.2 ⟨self_mem_Gx b, hbt⟩)]
      exact hb'
    have hbz : IsConj z (t * b) := by
      rw [← mem_Gx.1 ht.1]
      exact h2BB.2
    exact typing_Gz h h' h2BB.1 hw' hφ hb ⟨hbt, hbz⟩ hd x hx hxA

end CFSG.EvenSporadicStandard.HNRecog.Section4
