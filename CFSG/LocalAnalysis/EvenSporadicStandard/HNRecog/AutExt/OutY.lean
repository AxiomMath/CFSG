module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthOut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.ShapeHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Derived

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem exists_orthCoord_Y (h : F5Base a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) :
    ∃ (ρ : ↥(derivedOf (Gxy x w)) →* Equiv.Perm (Fin 5)) (θ : G → Fv5),
      OrthCoord (derivedOf (Gxy x w)) (CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w))) ρ θ := by
  haveI : Finite G := h.finite
  have hcomm : w * x = x * w := h.mul_comm (Or.inr hw) (Or.inl hx) (Or.inr hwx)
  have hxmem : x ∈ Gx w := mem_Gx.2 hcomm
  have hwx' : IsConj w (x * w) := by
    have h1 : IsConj w (w * x) := hw.symm.trans hwx
    rwa [hcomm] at h1
  have hF : F5Base a w := h.of_isConj (IsConj.refl a) hw
  have hY : Y4aStruct a w x := hF.loc.y4a.self.y4a x hxmem hx hwx'
  have hMK : CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w)) ≤ derivedOf (Gxy x w) :=
    Subgroup.map_subtype_le _
  have hM : IsElemTwo 4 (CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w))) := hY.orth.1
  have hM16 : Nat.card ↥(CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w))) = 16 := by
    rw [hM.2]; norm_num
  obtain ⟨S, hpart, hS0, hS1⟩ := hY.orth.2
  obtain ⟨π, hπsurj, hπker, hπab⟩ := y4a_exists_hom hY.shape
  obtain ⟨-, -, hψdata⟩ := y4a_derived_of_hom π hπsurj hπker hπab hM16
  obtain ⟨ψ, hψsurj, hψker⟩ := hψdata
  exact orthCoord_of_orbits hMK hM hpart hS0 hS1 hψsurj hψker

theorem out_Y_of_base (h : F5Base a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) {ψ₁ ψ₂ : G → G}
    (h₁ : IsIsoOn (derivedOf (Gxy w x)) (derivedOf (Gxy w x)) ψ₁)
    (h₂ : IsIsoOn (derivedOf (Gxy w x)) (derivedOf (Gxy w x)) ψ₂)
    (n₁ : ¬ ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), ψ₁ y = g * y * g⁻¹)
    (n₂ : ¬ ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), ψ₂ y = g * y * g⁻¹) :
    ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), ψ₁ (ψ₂ y) = g * y * g⁻¹ := by
  rw [Gxy_comm w x] at h₁ h₂ n₁ n₂ ⊢
  obtain ⟨ρ, θ, hC⟩ := exists_orthCoord_Y h hw hx hwx
  exact hC.out_aut rfl h₁ h₂ n₁ n₂

end CFSG.EvenSporadicStandard.HNRecog.Section4
