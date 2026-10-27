module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.QuasithinUnique.Id2519 (fixSubgroup fixSubgroup_eq_map)
open CFSG.QuasithinUnique.Id2519.SporHS (fix_data fixEquiv hsRows_cases)
open CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section HS


theorem hs_outerE_not_l34 : ¬ LieModel outerE .PSL 3 2 2 := by
  obtain ⟨eC, hsz, -⟩ := outerE_classes
  have h3 : 3 < classSizes.size := by decide
  have hc : Nat.card (eC ⟨3, h3⟩).carrier = 105 := (hsz _).trans rfl
  have hE : Nat.card outerE = 20160 := card_outerE
  have : Finite outerE := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have h1 : (192 : ℕ) * 105 = 20160 := by norm_num
  exact not_lieModel_psl_three_two_of_conjClass (X := outerE) (eC ⟨3, h3⟩) (m := 192)
    (fun h => by have := hc.symm.trans h; norm_num at this)
    ((congrArg (fun n => 192 * n) hc).trans (h1.trans hE.symm)) (by norm_num) (by norm_num)

theorem hs_fixedSubgroup_rows {S : Type} [Group S] (e : S ≃* NativeSporadic.HS) {σ : MulAut S}
    (hσ : orderOf σ = 2) :
    ∃ r ∈ hsRows, Nonempty (fixedSubgroup σ ≃*
      ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))))) := by
  set θ : S ≃* hsP := e.trans hsPermEquiv
  set α : MulAut hsP := MulAut.congr θ σ
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hα2 : α * α = 1 := by
    rw [show α * α = MulAut.congr θ (σ * σ) from (map_mul (MulAut.congr θ) σ σ).symm, hσ2,
      map_one]
  have hα1 : α ≠ 1 := by
    intro h
    have : σ = 1 := (MulAut.congr θ).injective (by rw [map_one]; exact h)
    rw [this, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨r, hr, g, -, x, -, -, h3⟩ := fix_data α hα2 hα1
  have hmap : fixSubgroup α = (fixSubgroup σ).map θ.toMonoidHom :=
    fixSubgroup_eq_map θ σ α fun y => by simp [α, MulAut.congr_apply]
  have hfix : fixedSubgroup σ = fixSubgroup σ := by
    ext y
    exact Iff.rfl
  refine ⟨r, hr, ⟨?_⟩⟩
  exact ((MulEquiv.subgroupCongr hfix).trans
    (((fixSubgroup σ).equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hmap.symm))).trans (fixEquiv h3)

theorem hs_false_of_l34 {S : Type} [Group S] (e : S ≃* NativeSporadic.HS) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 2) : False := by
  obtain ⟨r, hr, ⟨φ⟩⟩ := hs_fixedSubgroup_rows e hσ
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  have hcardC := (hrows r hr).2.2.2.2.1
  have hcardD : Nat.card (D ⧸ center D) = 20160 := by
    rw [LinearPilot.card_of_lieModel_PSL_two hDm]
    decide
  have hdvd := card_quotient_center_dvd_card_fixedSubgroup D
  rw [hcardD, Nat.card_congr φ.toEquiv, hcardC] at hdvd
  rcases hsRows_cases hr with h | ⟨-, -, h, -⟩ | ⟨hrep, -⟩ | h
  · rw [h] at hdvd
    norm_num at hdvd
  · rw [h] at hdvd
    norm_num at hdvd
  ·
    have hC : hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) = outerC := by
      rw [hrep]
      rfl
    let ψ : fixedSubgroup σ ≃* outerC := φ.trans (MulEquiv.subgroupCongr hC)
    set B : Subgroup outerC := D.map ψ.toMonoidHom with hBdef
    have hB : IsComponent B := LocalCores.isComponent_map_mulEquiv ψ hD
    have hBm : LieModel (B ⧸ center B) .PSL 3 2 2 := lieModel_map_of_mulEquiv ψ hDm
    have hBq : Nat.card (B ⧸ center B) = 20160 := by
      rw [LinearPilot.card_of_lieModel_PSL_two hBm]
      decide
    have hBperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.1.1
    have hBle : B.map outerC.subtype ≤ outerE := by
      rw [← map_commutator_outerC, ← hBperf]
      exact Subgroup.map_mono (Subgroup.commutator_mono le_top le_top)
    have hBcard : Nat.card B = 20160 := by
      have h1 : Nat.card B ≤ 20160 := by
        rw [← card_outerE, ← Subgroup.card_map_of_injective outerC.subtype_injective]
        exact Subgroup.card_le_of_le hBle
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
      rw [hBq] at h2
      have h3 : 0 < Nat.card (center B) := Nat.card_pos
      nlinarith
    have hBeq : B.map outerC.subtype = outerE := Subgroup.eq_of_le_of_card_ge hBle (by
      rw [Subgroup.card_map_of_injective outerC.subtype_injective, hBcard, card_outerE])
    have hZ : center B = ⊥ := by
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
      rw [hBq, hBcard] at h2
      exact Subgroup.eq_bot_of_card_eq _ (by omega)
    let ε : B ⧸ center B ≃* outerE :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        ((B.equivMapOfInjective outerC.subtype outerC.subtype_injective).trans
          (MulEquiv.subgroupCongr hBeq))
    exact hs_outerE_not_l34 (LieType.CurtisTits.lieModel_of_mulEquiv ε hBm)
  · rw [h] at hdvd
    norm_num at hdvd

end HS

end CFSG.SeitzReduction.SporadicRefine
