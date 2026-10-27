module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTBasic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2OutLieModel
import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.GH74.GLS.IVK.GHInv
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (fixSub)


section Inner


theorem q3In_g2 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3EmptyIn (fun X _ => LieModel X .G2 0 p f) := by
  intro N _ _ H t L hs htH hH
  have ht2 : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hs.inv
  obtain ⟨F, _, _, S, hcard, -⟩ := exists_shape_G2 hp hp2 hH _ ht2
  have h3 : 3 ≤ Nat.card F := by rw [hcard]; exact PumpupTableExc.three_le_pow hp hp2 hf
  have hk : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hcard
  exact PumpupTableExc.false_of_shape_centralizer hs.comp htH hs.two S h3 h3 hk hk

theorem q3In_d4
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3EmptyIn (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro N _ _ H t L hs htH hH
  have ht2 : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hs.inv
  obtain ⟨F₁, F₂, _, _, _, _, S, hc₁, hc₂, -⟩ := exists_shape_D4 hp hp2 hH _ ht2
  have h3 : 3 ≤ p ^ f := PumpupTableExc.three_le_pow hp hp2 hf
  have h₁ : 3 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 3 ≤ p ^ f := h3
      _ ≤ (p ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h₂ : 3 ≤ Nat.card F₂ := by rw [hc₂]; exact h3
  have hk₁ : ringChar F₁ ≠ 2 :=
    CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 (f := f * 3)
      (by rw [hc₁, ← pow_mul])
  have hk₂ : ringChar F₂ ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hc₂
  exact PumpupTableExc.false_of_shape_centralizer hs.comp htH hs.two S h₁ h₂ hk₁ hk₂

end Inner

theorem q3Out_g2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) :
    Q3EmptyOut (fun X _ => LieModel X .G2 0 p f) := by
  intro N _ _ H t K hs htH hH
  have := hs.normal
  obtain ⟨L0, hL0, -, hcomm, hsimple, e', he', hmodel⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_outer_involution_fixed_simple hp hp2 hp3 hf hH
      (MulAut.conjNormal t : MulAut ↥H) (PumpupOutOrders.conjNormal_sq hs.inv)
      (PumpupOutOrders.conjNormal_not_inner hs.faithful htH)
  have hcK := hs.card_eq_of_fixSub_le L0 hL0 hcomm hsimple
  rw [hs.card_K, CFSG.GH74.card_of_lieModel_G2 hp2 hmodel] at hcK
  exact (lt_ordG2 (three_le_pow hp hp2 he')).ne hcK

theorem q3Out_d4
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3EmptyOut (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro N _ _ H t K hs htH hH
  have := hs.normal
  obtain ⟨e', he', hsimple, -, hmodel⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.td4_outer_involution_fixed hp hp2 hf hH
      (MulAut.conjNormal t : MulAut ↥H) (by rw [sq]; exact PumpupOutOrders.conjNormal_sq hs.inv)
      (PumpupOutOrders.conjNormal_not_inner hs.faithful htH)
  have hs' : IsSimpleGroup ↥(fixSub (MulAut.conjNormal t : MulAut ↥H)) := hsimple
  have hmodel' : LieModel ↥(fixSub (MulAut.conjNormal t : MulAut ↥H)) .trialityD4 0 p e' :=
    hmodel
  have hcK := hs.card_eq_of_fixSub_simple hs'
  rw [hs.card_K, CFSG.GH74.card_of_lieModel_trialityD4 hp2 hmodel'] at hcK
  exact (lt_ordTrialityD4 (three_le_pow hp hp2 he')).ne hcK

end CFSG.GH74.Generic.BProg.B2.T4.PGV
