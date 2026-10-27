module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusSchur
public import CFSG.GF2Type.Smith1979.CaseI25A2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_Lbar_of_centralizes_w4 (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C) {c : S.O} (hcM : c ∈ S.Mbar)
    (hc : ∀ l ∈ S.Lbar g, c * l = l * c) : c ∈ S.Lbar g := by
  obtain ⟨Q, hQ, -, -, hE, hsing⟩ := hΩ.exists_form
  have ha0 := aV_ne_zero H ht
  have ha := CaseIClosure.Q_aV_eq_zero H ht hsing
  have hct : c * t = t * c := hc t ht
  have hcN : c ∈ normalizer (S.Lbar g : Set S.O) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => (hc h hh).symm)
  have hca := fix_of_mem_normalizer H hcN
  let y : S8.CMt S t := ⟨c, S8.mem_CMt.mpr ⟨hcM, hct⟩⟩
  have hφapp : ∀ w : Vt S g t,
      ((S8.resCV S g H.conj_mem t y w : Vt S g t) : S.Qt) =
        (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w := fun w => rfl
  have hφinv : ∀ w : Vt S g t,
      (((S8.resCV S g H.conj_mem t y)⁻¹ w : Vt S g t) : S.Qt) =
        ((c⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w :=
    coe_inv_apply_of_forall hφapp
  have hφO : S8.resCV S g H.conj_mem t y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    W4As.resCV_mem_orthogonalGroup_omega H hNo C ht ht1 hVQ hΩ hsing y
  have hφa : S8.resCV S g H.conj_mem t y (aV ht) = aV ht := Subtype.ext hca
  have hcomm : ∀ u ∈ pointRadical Q (aV ht),
      S8.resCV S g H.conj_mem t y * u * (S8.resCV S g H.conj_mem t y)⁻¹ = u := by
    intro u hu
    rw [← hE] at hu
    obtain ⟨x, hx, hux⟩ := mem_LmodN.mp hu
    have e : c * x * c⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc x hx
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hφapp, hux, hφinv, hux v]
    change ((c * x * c⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = _
    rw [e]
  have hφL := Case25.mem_pointRadical_of_commute hQ ha0 ha hφO hφa hcomm
  rw [← hE] at hφL
  obtain ⟨l, hl, hφl⟩ := mem_LmodN.mp hφL
  have hxM : l⁻¹ * c ∈ S.Mbar := mul_mem (inv_mem (S.Lbar_le_Mbar g hl)) hcM
  have hlt : Commute l t := Lbar_comm S H.conj_mem hl ht
  have hxt : (l⁻¹ * c) * t = t * (l⁻¹ * c) := by
    calc l⁻¹ * c * t = l⁻¹ * (c * t) := by group
      _ = l⁻¹ * (t * c) := by rw [hct]
      _ = (l⁻¹ * t) * c := by group
      _ = (t * l⁻¹) * c := by rw [hlt.inv_left.eq]
      _ = t * (l⁻¹ * c) := by group
  have hxV : ∀ v ∈ Vt S g t, ((l⁻¹ * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    have h1 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v := hφl ⟨v, hv⟩
    rw [coe_mul_apply, h1, inv_apply_apply_O]
  have hcl : c = l * (l⁻¹ * c) := by group
  rw [hcl]
  rcases W4Minus.eq_one_or_t_of_fix_Vt hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hxM hxt hxV with
    h | h
  · rw [h, mul_one]
    exact hl
  · rw [h]
    exact mul_mem hl ht

theorem mem_Lbar_mul_of_centralizes_w4 (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C) (h : S.M) {c : S.O}
    (hcM : c ∈ S.Mbar) (hc : ∀ l ∈ S.Lbar ((h : G) * g), c * l = l * c) :
    c ∈ S.Lbar ((h : G) * g) := by
  rw [mem_Lbar_mul_iff]
  have hρM : S.ρ h ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨h, rfl⟩
  refine mem_Lbar_of_centralizes_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP
    (mul_mem (mul_mem (inv_mem hρM) hcM) hρM) fun l hl => ?_
  have hl' : S.ρ h * l * (S.ρ h)⁻¹ ∈ S.Lbar ((h : G) * g) := conj_mem_Lbar_mul S h hl
  have e := hc _ hl'
  calc (S.ρ h)⁻¹ * c * S.ρ h * l
      = (S.ρ h)⁻¹ * (c * (S.ρ h * l * (S.ρ h)⁻¹)) * S.ρ h := by group
    _ = (S.ρ h)⁻¹ * ((S.ρ h * l * (S.ρ h)⁻¹) * c) * S.ρ h := by rw [e]
    _ = l * ((S.ρ h)⁻¹ * c * S.ρ h) := by group

end CFSG.GF2Type.Smith1979.W4MinusC
