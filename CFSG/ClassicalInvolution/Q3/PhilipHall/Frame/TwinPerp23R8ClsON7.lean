module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOAct

import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoP
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOD8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

section ON7


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y}

theorem acts_inv {Q : Type} [Group Q] {Φ : Set (Subgroup Q)} (D : AEData Q Φ) {σ : MulAut Q} {w : Wr 6}
    (hσ : D.Acts σ w) : D.Acts (σ⁻¹ : MulAut Q) w⁻¹ := by
  intro x
  have h1 := hσ (σ⁻¹ x)
  rw [MulAut.apply_inv_self] at h1
  rw [map_inv, inv_inv]
  calc D.φ (σ⁻¹ x) = (mkQ 6 w)⁻¹ * (mkQ 6 w * D.φ (σ⁻¹ x) * (mkQ 6 w)⁻¹) * mkQ 6 w := by group
    _ = (mkQ 6 w)⁻¹ * D.φ x * mkQ 6 w := by rw [← h1]

theorem p23E8ON7_of_cover (hc : P23Cfg n Y R S t K' W u e g)
    (hAE : SecAE R e 6) (hZ : P23ZData t u e Z) : (aSub R Z e).relIndex Z ≤ 4 := by
  classical
  obtain ⟨D⟩ := exists_cover hc hAE
  obtain ⟨β, hβ, b₀, hlA, hlA', hz, htA, htA', -⟩ := twin_labels hc D
  set θ := actHom hc hZ with hθ
  haveI : Finite θ.range := Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hex : ∀ σ : θ.range, ∃ w : Wr 6, D.toAEData.Acts (σ : MulAut (SecQ R e)) w ∧
      ∀ (b : Bool), ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    rintro ⟨σ, a, rfl⟩
    exact exists_cent_w hc D hlA hlA' hz htA htA' (hZ.le_cent hZ.he a.2)
      (hZ.comm (a : Y) a.2 t hZ.ht) (fun l hl => p23_zdata_comm_twins hc hZ a.2 hl)
  choose w hwA hwC using hex
  let f : θ.range → AEQ 6 := fun σ => mkQ 6 (w σ)
  have hG : ∀ σ : θ.range, σ * σ = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    show θ a * θ a = 1
    rw [← map_mul, show a * a = 1 from Subtype.ext (hZ.sq a a.2), map_one]
  have hGc : ∀ σ : θ.range, (σ : MulAut (SecQ R e)) * σ = 1 := fun σ => congrArg Subtype.val (hG σ)
  have hf : Function.Injective f := by
    intro σ₁ σ₂ h
    have hcomp := (acts_inv D.toAEData (hwA σ₂)).comp D.toAEData (hwA σ₁)
    have h1 : mkQ 6 ((w σ₂)⁻¹ * w σ₁) = 1 := by
      rw [map_mul, map_inv, show mkQ 6 (w σ₁) = mkQ 6 (w σ₂) from h, inv_mul_cancel]
    have hid := eq_of_trivial_mod_ker D.perfect ((σ₂ : MulAut (SecQ R e))⁻¹ * (σ₁ : MulAut (SecQ R e)))
      (fun x => by
        apply D.toAEData.ker_le
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have h2 := hcomp x
        rw [h1] at h2
        have h3 : D.φ (((σ₂ : MulAut (SecQ R e))⁻¹ * (σ₁ : MulAut (SecQ R e))) x) = D.φ x := by
          simpa using h2
        rw [h3, inv_mul_cancel])
    apply Subtype.ext
    have h4 : (σ₂ : MulAut (SecQ R e))⁻¹ * (σ₁ : MulAut (SecQ R e)) = 1 := MulEquiv.ext hid
    exact (inv_mul_eq_one.mp h4).symm
  have hsq : ∀ σ, f σ * f σ = 1 := by
    intro σ
    have hc2 := (hwA σ).comp D.toAEData (hwA σ)
    have h0 : mkQ 6 (w σ * w σ) = 1 := by
      apply mkQ_eq_one_of_centralizes
      intro y hy
      rw [← D.toAEData.range_eq] at hy
      obtain ⟨x, rfl⟩ := hy
      have h1 := hc2 x
      have h2 : ((σ : MulAut (SecQ R e)) ∘ (σ : MulAut (SecQ R e))) x = x :=
        congrArg (fun τ : MulAut (SecQ R e) => τ x) (hGc σ)
      rw [h2] at h1
      exact h1.symm
    show mkQ 6 (w σ) * mkQ 6 (w σ) = 1
    rw [← map_mul]
    exact h0
  have hcard : Nat.card θ.range ≤ 4 := card_le_four hβ hG f hf hsq (fun σ b y hy => hwC σ b y hy)
  have hker : θ.ker ≤ (aSub R Z e).subgroupOf Z := by
    intro a ha
    rw [Subgroup.mem_subgroupOf, mem_aSub_iff (hZ.le_cent hZ.he)]
    exact ⟨a.2, centModE_of_act_eq_one hc hZ ha⟩
  have h1 : ((aSub R Z e).subgroupOf Z).index ∣ θ.ker.index := Subgroup.index_dvd_of_le hker
  have h2 : θ.ker.index = Nat.card θ.range := Subgroup.index_ker θ
  have h3 : θ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h1
  rw [h2] at h4
  exact h4.trans hcard

theorem p23E8ON7_proved : P23E8ON7 n := by
  intro _ _ Y _ _ R S t K' W u e g hc _ _ hA6 Z hZ
  exact p23E8ON7_of_cover hc hA6 hZ

end ON7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
