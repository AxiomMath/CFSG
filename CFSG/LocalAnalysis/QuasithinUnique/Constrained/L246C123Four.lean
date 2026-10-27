module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Unconditional
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourDef
import all CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Bridge

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

variable {G : Type} [Group G] [Finite G] {T Y L : Subgroup G}

theorem b42_case7_four (h4 : AsB42A7Four) {m : Main T Y L} {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAc : ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    ∃ A₂ : Subgroup (MulAut (Msec m)), A₂ ≤ autSec (autI m.hyp.elem A) (U' m) (Z' m) ∧
      ∀ π : ↥(alternatingGroup (Fin 7)) ≃* ↥(L₂ m),
        AltConjTo 7 ((A₂.subgroupOf (L₂ m)).comap π.toMonoidHom) kleinRegular7 := by
  have hAc' : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T Y : Set G) := fun h =>
    hAc (m.le_centralizer_of_comm_le (hA.1.trans m.hyp.TY) h)
  let D := m.blockData
  have Hs := D.secHyp hA hAc'
  have hFF := D.isFFStarOffender hA hAc'
  have hV2 : ∀ v : V₀ m, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hA2 : ∀ a ∈ autI D.elem A, a ^ 2 = 1 := hFF.2.2.1.2
  have hIsA2 : IsA2 (autSec (autI D.elem L ⊔ autI D.elem A) (U' m) (Z' m))
      (autSec (autI D.elem A) (U' m) (Z' m)) :=
    ⟨autSec_mono le_sup_right _ _, autSec_ne_bot Hs.stabA Hs.not_le_centSec_A,
      isElemAbelian2_autSec hFF.2.2.1 Hs.stabA⟩
  obtain ⟨A₂, hA₂Ā, hA₂, -⟩ :=
    B1.exists_offender_below hIsA2 0 (by simpa using Hs.card_le_autSec hFF)
  refine ⟨A₂, hA₂Ā, fun π => ?_⟩
  have C : Alt57.Ctx (autSec (autI D.elem L ⊔ autI D.elem A) (U' m) (Z' m)) (L₂ m) 7 :=
    ⟨Or.inr rfl, Hs.iso_autSec, (Hs.genFitting_eq hA2 hV2).symm, Hs.sqG hA2⟩
  have hcard : Nat.card (Msec m) = 2 ^ 4 := by
    rw [card_Msec m]
    norm_num
  exact h4 (Msec m) (exp_Msec m) _ (L₂ m) A₂ C Hs.isIrrSec hA₂ hcard π

section OffenderDataFour

theorem offender_klein_four (h4 : AsB42A7Four) {m : Main T Y L}
    (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAc : ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    IsKleinConj (img (πmap hrange e) A) := by
  obtain ⟨A₂, hA₂Ā, hAlt⟩ := b42_case7_four h4 (m := m) hA hAc
  have hAY : A ≤ Y := hA.1.trans m.hyp.TY
  have hK' := isKleinConj_of_altConjTo (hAlt e.symm)
  have hle : (A₂.subgroupOf (L₂ m)).comap e.symm.toMonoidHom ≤ img (πmap hrange e) A := by
    intro x hx
    have h1 : ((e.symm x : ↥(L₂ m)) : MulAut (Msec m)) ∈ A₂ :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hx)
    obtain ⟨a, haA, ha⟩ := (mem_Abar_iff hAY (autI_le_stab hAY)).1 (hA₂Ā h1)
    refine mem_img.2 ⟨a, haA, ?_⟩
    show e ⟨actY m a, hrange a⟩ = x
    have : (⟨actY m a, hrange a⟩ : ↥(L₂ m)) = e.symm x := Subtype.ext ha
    rw [this, MulEquiv.apply_symm_apply]
  have hcard4 : Nat.card ↥(img (πmap hrange e) A) ≤ 4 :=
    card_le_four (img_elem_abelian hA.2.1).1 (img_elem_abelian hA.2.1).2
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hK'.card]; exact hcard4)
  rw [← heq]
  exact hK'

theorem le_card_fixU_four (h4 : AsB42A7Four) {m : Main T Y L}
    (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAc : ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    4 ≤ Nat.card (fixU (ρmap e) (img (πmap hrange e) A)) := by
  have hAY : A ≤ Y := hA.1.trans m.hyp.TY
  have hAc' : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T Y : Set G) := fun h =>
    hAc (m.le_centralizer_of_comm_le hAY h)
  have Hs := m.blockData.secHyp hA hAc'
  have hFF := m.blockData.isFFStarOffender hA hAc'
  have hKk := offender_klein_four h4 hrange e hA hAc
  have h1 : Nat.card (Msec m) ≤ Nat.card ↥(autSec (autI m.hyp.elem A) (U' m) (Z' m)) *
      Nat.card ↥(fixV (autSec (autI m.hyp.elem A) (U' m) (Z' m))) := Hs.card_le_autSec hFF
  have hĀ : Nat.card ↥(autSec (autI m.hyp.elem A) (U' m) (Z' m)) = 4 :=
    (card_Abar hrange e hAY).trans hKk.card
  rw [fixU_eq_fixV hrange e hAY]
  have h16 := card_Msec m
  have h16' : 4 * 4 ≤ 4 * Nat.card ↥(fixV (autSec (autI m.hyp.elem A) (U' m) (Z' m))) := by
    have h2 := h1
    rw [hĀ, h16] at h2
    exact h2
  exact Nat.le_of_mul_le_mul_left h16' (by norm_num)

theorem offender_split_four (h4 : AsB42A7Four) {m : Main T Y L}
    (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAc : ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    ∀ v ∈ VZ T Y, ∃ u ∈ blockU L, ∃ c ∈ VZ T Y, (∀ a ∈ A, a * c = c * a) ∧ v = u * c := by
  have hAY : A ≤ Y := hA.1.trans m.hyp.TY
  have hAc' : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T Y : Set G) := fun h =>
    hAc (m.le_centralizer_of_comm_le hAY h)
  have Hs := m.blockData.secHyp hA hAc'
  have hFF := m.blockData.isFFStarOffender hA hAc'
  have hKk := offender_klein_four h4 hrange e hA hAc
  have hĀ : Nat.card ↥(autSec (autI m.hyp.elem A) (U' m) (Z' m)) = 4 :=
    (card_Abar hrange e hAY).trans hKk.card
  have hge := le_card_fixU_four h4 hrange e hA hAc
  have hX := autI_le_stab (m := m) m.hyp.LY
  have hle : Nat.card (fixU (ρmap e) (img (πmap hrange e) A)) ≤ 4 :=
    card_fixU_le_four (ρmap e) (card_Msec m) (ρmap_injective e) (exp_Msec m)
      (T := img (πmap hrange e) T) (A := img (πmap hrange e) A)
      (card_img_T m.hyp (πmap_surjective hX hrange e)) hKk.card (img_mono hA.1)
  have hfix4 : Nat.card ↥(fixV (autSec (autI m.hyp.elem A) (U' m) (Z' m))) = 4 := by
    rw [← fixU_eq_fixV hrange e hAY]
    exact le_antisymm hle hge
  have hAstar : Nat.card ↥(autI m.hyp.elem A) = 4 := by
    have h1 := card_autSec_mul (A := autI m.hyp.elem A) (W := U' m) (U := Z' m)
      Hs.stabAU Hs.stabAZ
    rw [autI_inf_centSec_eq_bot hAY, Subgroup.card_bot, mul_one, hĀ] at h1
    exact h1.symm
  have h : Nat.card (Msec m) = Nat.card ↥(autI m.hyp.elem A) *
      Nat.card ↥(fixV (autSec (autI m.hyp.elem A) (U' m) (Z' m))) := by
    rw [hAstar, hfix4, card_Msec m]
  obtain ⟨-, htop⟩ := section_equality hFF Hs.ltZU.le Hs.stabAU h
  intro v hv
  have hv0 : IntMod.mk m.hyp.elem ⟨v, hv⟩ ∈ U' m ⊔ fixV (autI m.hyp.elem A) := by
    rw [htop]
    trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.1 hv0
  refine ⟨x.val, hx, y.val, y.val_mem, fun a ha => ?_, ?_⟩
  · have haY : a ∈ Y := hAY ha
    have h1 := hy (convI m.hyp.elem ⟨a, m.hyp.YN haY⟩) (convI_mem_autI m.hyp.elem ha _)
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    exact mul_inv_eq_iff_eq_mul.1 h2
  · have h3 := congrArg IntMod.val hxy
    rw [IntMod.val_mul] at h3
    exact h3.symm

end OffenderDataFour

theorem exists_modData_four (h4 : AsB42A7Four) (m : Main T Y L) :
    ∃ (M : Type) (_ : CommGroup M) (φ : ↥(blockU L) ≃* M) (π : ↥Y →* A7)
      (ρ : A7 →* MulAut M), ModData T Y L φ π ρ := by
  obtain ⟨A₁, hA₁, hA₁c⟩ := exists_offender m
  have hAY : A₁ ≤ Y := hA₁.1.trans m.hyp.TY
  have hAc' : ¬ ⁅L, A₁⁆ ≤ Subgroup.centralizer (VZ T Y : Set G) := fun h =>
    hA₁c (m.le_centralizer_of_comm_le hAY h)
  have Hs := m.blockData.secHyp hA₁ hAc'
  obtain ⟨e₀⟩ := Hs.iso_autSec
  have hcard : Nat.card (L₂ m) = 2520 := by
    rw [Nat.card_congr e₀.toEquiv]
    exact card_A7
  have hX := autI_le_stab (m := m) m.hyp.LY
  have hrange := actY_mem_L₂' hX hcard
  refine ⟨Msec m, inferInstance, φeq m, πmap hrange e₀, ρmap e₀, ?_⟩
  exact
    { card_M := card_Msec m
      exp_M := exp_Msec m
      surj := πmap_surjective hX hrange e₀
      inj := ρmap_injective e₀
      equiv := fun y u u' h => πmap_equiv hrange e₀ y u u' h
      ker := fun y h => πmap_ker hrange e₀ y h
      klein := fun A hA hAc => ⟨offender_klein_four h4 hrange e₀ hA hAc,
        le_card_fixU_four h4 hrange e₀ hA hAc⟩
      split := fun A hA hAc => offender_split_four h4 hrange e₀ hA hAc }

theorem c123_generic_four
    (h4 : AsB42A7Four) (hZ : ExcA7CentralZero) {T Y L : Subgroup G}
    (hH : Hyp T Y L) : Y ≤ cgsIn Y T := by
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T Y : Set G)
  · exact hH.le_cgsIn_of_J_le hJ
  · let m : Main T Y L := ⟨hH, hZ G L hH.exc, hJ⟩
    obtain ⟨M, _, φ, π, ρ, D⟩ := exists_modData_four h4 m
    exact core m D

theorem c123_four (h4 : AsB42A7Four) (hZ : ExcA7CentralZero) :
    ∀ (G : Type) [Group G] [Finite G], L238.C123TwoCgsStatement (G := G) := by
  intro G _ _ T Y L hT hY _ hL hprod hexc
  exact c123_generic_four h4 hZ ⟨hT, hY, hL, hprod, hexc⟩

theorem c123_unconditional_four
    (h4 : AsB42A7Four) :
    ∀ (G : Type) [Group G] [Finite G], L238.C123TwoCgsStatement (G := G) :=
  c123_four h4 excA7CentralZero

end CFSG.QuasithinUnique.L246.C123
