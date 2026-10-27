module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLWFix
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoP
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section LemP

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y}

theorem false_of_centModE_of_omegaOne (hc : P23Cfg n Y R S t K' W u e g)
    (hOm : OmegaOneCenter (rLayer (Om R) e) e) {c' : Y}
    (hyC : c' * e * c'⁻¹ ∈ Subgroup.centralizer ({e} : Set Y))
    (hy2 : (c' * e * c'⁻¹) * (c' * e * c'⁻¹) = 1) (hne : c' * e * c'⁻¹ ≠ e)
    (hcm : CentModE R e (c' * e * c'⁻¹)) : False := by
  set y := c' * e * c'⁻¹ with hydef
  set E := rLayer (Om R) e
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have he2 : e * e = 1 := hc.data.he2
  have heE : e ∈ E := p23_e_mem_rLayer hc
  have hV2 : IsPGroup 2 (Subgroup.zpowers y) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hy2
  have hzp : ∀ v ∈ Subgroup.zpowers y, v = 1 ∨ v = y := by
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hy2' : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy2
    rw [zpow_eq_zpow_emod k hy2']
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h, zpow_zero]
    · right; rw [h, zpow_one]
  have hcov : E ≤ oddCoreOf E ⊔ (E ⊓ rLayerSub (Om R) (Subgroup.zpowers y)) :=
    F7C.rLayer_le_cover hΩ hV2 (Subgroup.zpowers_le.mpr hyC) (by
      intro v hv a ha
      rcases hzp v hv with rfl | rfl
      · rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact (oddCoreOf E).one_mem
      · exact hcm a ha)
  have hey : e ∈ rLayerSub (Om R) (Subgroup.zpowers y) :=
    F7C.mem_rLayerSub_of_cover hcov heE
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one he2)
  have hsubeq : rLayerSub (Om R) (Subgroup.zpowers y) = conjSub c' E := by
    have hcz : Subgroup.centralizer (Subgroup.zpowers y : Set Y) =
        Subgroup.centralizer ({y} : Set Y) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h1 : rLayerSub (Om R) (Subgroup.zpowers y) = rLayer (Om R) y := by
      unfold rLayerSub rLayer
      simp only [hcz]
    rw [h1, hydef]
    exact rLayer_conj (R := R) c' e
  rw [hsubeq] at hcov hey
  have heEy : e ∈ conjSub c' E := hey
  have hcov' := ZTwo.cover_transfer E (conjSub c' E) (Twin1711.conjSubEquiv E c') hcov
  have hOEy : ∀ a ∈ conjSub c' E, ∀ o ∈ oddCoreOf (conjSub c' E),
      a * o * a⁻¹ ∈ oddCoreOf (conjSub c' E) := fun a ha o ho =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf _ ha) o).mp ho
  have hEC : E ≤ Subgroup.centralizer ({e} : Set Y) := F7C.rLayer_le_centralizer e
  have hcentE : ∀ x ∈ E, e * x * e⁻¹ = x := fun x hx => by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEC hx)]
    group
  have hP8 : ∀ a ∈ conjSub c' E, e * a * e⁻¹ * a⁻¹ ∈ oddCoreOf (conjSub c' E) := by
    intro a ha
    have ha' : a ∈ ((oddCoreOf (conjSub c' E) ⊔ (E ⊓ conjSub c' E) : Subgroup Y) : Set Y) :=
      hcov' ha
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans (Sec7.le_normalizer_oddCoreOf _))] at ha'
    obtain ⟨o, ho, x, hx, rfl⟩ := ha'
    have h1 : e * (o * x) * e⁻¹ * (o * x)⁻¹ = (e * o * e⁻¹) * o⁻¹ := by
      have hx' := hcentE x hx.1
      calc e * (o * x) * e⁻¹ * (o * x)⁻¹ = (e * o * e⁻¹) * (e * x * e⁻¹) * x⁻¹ * o⁻¹ := by
            group
        _ = (e * o * e⁻¹) * o⁻¹ := by rw [hx']; group
    rw [h1]
    exact (oddCoreOf (conjSub c' E)).mul_mem (hOEy e heEy o ho)
      ((oddCoreOf (conjSub c' E)).inv_mem ho)
  have hE₂ : c'⁻¹ * e * c' ∈ E := mem_conjSub_iff.mp heEy
  set e₂ := c'⁻¹ * e * c' with he₂def
  have he₂2 : e₂ * e₂ = 1 := by
    calc e₂ * e₂ = c'⁻¹ * (e * e) * c' := by rw [he₂def]; group
      _ = 1 := by rw [he2]; group
  have hP9 : ∀ a₂ ∈ E, e₂ * a₂ * e₂⁻¹ * a₂⁻¹ ∈ oddCoreOf E := by
    intro a₂ ha₂
    have ha : c' * a₂ * c'⁻¹ ∈ conjSub c' E := conj_mem_conjSub ha₂
    have h1 := hP8 _ ha
    rw [AscE184Sect.oddCoreOf_conjSub, mem_conjSub_iff] at h1
    have : c'⁻¹ * (e * (c' * a₂ * c'⁻¹) * e⁻¹ * (c' * a₂ * c'⁻¹)⁻¹) * c' =
        e₂ * a₂ * e₂⁻¹ * a₂⁻¹ := by
      rw [he₂def]
      group
    rwa [this] at h1
  have hsq : e₂ * e₂ ∈ oddCoreOf E := by
    rw [he₂2]
    exact (oddCoreOf E).one_mem
  rcases hOm e₂ hE₂ hP9 hsq with h1 | h1
  ·
    have h2 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) h1
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one he₂2)
    apply hc.data.he1
    have : c' * e₂ * c'⁻¹ = e := by rw [he₂def]; group
    rw [← this, h2]
    group
  ·
    have hc2 : e * e₂ = e₂ * e := by
      have := hcentE e₂ hE₂
      calc e * e₂ = e * e₂ * e⁻¹ * e := by group
        _ = e₂ * e := by rw [this]
    have h4 : (e⁻¹ * e₂) * (e⁻¹ * e₂) = 1 := by
      rw [inv_eq_of_mul_eq_one_right he2]
      calc (e * e₂) * (e * e₂) = e * (e₂ * e) * e₂ := by group
        _ = e * (e * e₂) * e₂ := by rw [hc2]
        _ = (e * e) * (e₂ * e₂) := by group
        _ = 1 := by rw [he2, he₂2, one_mul]
    have h5 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) h1
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h4)
    have h6 : e = e₂ := inv_mul_eq_one.mp h5
    apply hne
    calc y = c' * e * c'⁻¹ := hydef
      _ = c' * e₂ * c'⁻¹ := by rw [← h6]
      _ = e := by rw [he₂def]; group

theorem not_centModE_orbit_237 (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hE : ECase1 R W e) (hno : ¬ SecNoExit R e)
    (hZs : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y))) (hZ : P23ZData t u e Z) {y : Y}
    (hy : y ∈ p23Orb Z t e) (hye : y ≠ e) : ¬ CentModE R e y := by
  intro hcm
  obtain ⟨m, hm, rfl⟩ := hy
  have hyZ : m * e * m⁻¹ ∈ Z := hZ.orb_le ⟨m, hm, rfl⟩
  exact false_of_centModE_of_omegaOne hc
    (lemLEZ_proved n hc.std.perp.core.below hP Y R S t K' W u e g hc hno hE hZs)
    (hZ.le_cent hZ.he hyZ) (hZ.sq _ hyZ) hye hcm

theorem not_centModE_of_ne_237 (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hE : ECase1 R W e) (hno : ¬ SecNoExit R e)
    (hZs : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y))) (hZ : P23ZData t u e Z)
    {f₁ f₂ : Y} (hf₁ : f₁ ∈ p23Orb Z t e) (hf₂ : f₂ ∈ p23Orb Z t e) (hne : f₁ ≠ f₂) :
    ¬ CentModE R f₁ f₂ := by
  intro hcm
  obtain ⟨m, hm, rfl⟩ := hf₁
  obtain ⟨m₂, hm₂, rfl⟩ := hf₂
  have hm' : m⁻¹ * m₂ ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hm₂
  have hcm' : CentModE R e ((m⁻¹ * m₂) * e * (m⁻¹ * m₂)⁻¹) := by
    have := (centModE_conj (R := R) m⁻¹ (m * e * m⁻¹) (m₂ * e * m₂⁻¹)).mpr hcm
    rwa [show m⁻¹ * (m * e * m⁻¹) * m⁻¹⁻¹ = e by group,
      show m⁻¹ * (m₂ * e * m₂⁻¹) * m⁻¹⁻¹ = (m⁻¹ * m₂) * e * (m⁻¹ * m₂)⁻¹ by group] at this
  refine not_centModE_orbit_237 hP hc hE hno hZs hZ ⟨m⁻¹ * m₂, hm', rfl⟩ ?_ hcm'
  intro h
  apply hne
  calc m * e * m⁻¹ = m * ((m⁻¹ * m₂) * e * (m⁻¹ * m₂)⁻¹) * m⁻¹ := by rw [h]
    _ = m₂ * e * m₂⁻¹ := by group

end LemP

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
