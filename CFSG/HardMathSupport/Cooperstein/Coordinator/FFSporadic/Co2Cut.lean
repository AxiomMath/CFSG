module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.KCut

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin

namespace KCut

variable {W : Type} [CommGroup W]

theorem le_cent_of_le_Kgrp {L D : Subgroup (MulAut W)} {u : MulAut W} (h : D ≤ Kgrp L u) :
    D ≤ L ⊓ Subgroup.centralizer {u} := h.trans (Kgrp_le_cent L u)

theorem genPair_of_sub {L Du Dv : Subgroup (MulAut W)} {u v : MulAut W}
    (hu : Du ≤ L ⊓ Subgroup.centralizer {u}) (hv : Dv ≤ L ⊓ Subgroup.centralizer {v})
    (h : Du ⊔ Dv = L) : GenPair L u v := by
  exact le_antisymm (sup_le inf_le_left inf_le_left) (h.symm.le.trans (sup_le_sup hu hv))

theorem cut_aux_of_sub [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)}
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV L = ⊥) {e f : MulAut W} (he2 : e * e = 1) (he1 : e ≠ 1) (hef : e * f = f * e)
    {De Df Def : Subgroup (MulAut W)} (hDe : De ≤ Kgrp L e) (hDf : Df ≤ Kgrp L f)
    (hDef : Def ≤ Kgrp L (e * f)) (hgen₁ : De ⊔ Df = L) (hgen₂ : Df ⊔ Def = L)
    (hcard : Nat.card (fixV (Subgroup.zpowers f)) ≤ Nat.card (fixV (Subgroup.zpowers e))) :
    False := by
  have hG : GenPair L e f := genPair_of_sub (le_cent_of_le_Kgrp hDe) (le_cent_of_le_Kgrp hDf) hgen₁
  obtain ⟨w, hew, hfw⟩ := exists_fixed_ne_of_max hW hirr he2 he1 hG hcard
  have hsup : Kgrp L f ⊔ Kgrp L (e * f) = L :=
    le_antisymm (sup_le (Kgrp_le L f) (Kgrp_le L _)) (hgen₂.symm.le.trans (sup_le_sup hDf hDef))
  have hw2 : f w * w⁻¹ = (e * f) w * w⁻¹ := by
    have : (e * f) w = f w := by
      rw [hef, MulAut.mul_apply, hew]
    rw [this]
  have h1 := disp_eq_one_of_sup_eq hfix hsup hw2
  exact hfw (mul_inv_eq_one.1 h1)

theorem false_of_sub_Kgrp [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)}
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV L = ⊥) {a b : MulAut W} (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a * b = b * a) (hne : a ≠ b)
    {Da Db Dab : Subgroup (MulAut W)} (hDa : Da ≤ Kgrp L a) (hDb : Db ≤ Kgrp L b)
    (hDab : Dab ≤ Kgrp L (a * b)) (hgen₁ : Da ⊔ Db = L) (hgen₂ : Da ⊔ Dab = L)
    (hgen₃ : Db ⊔ Dab = L) : False := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hb2)
  have hba : b * a = a * b := hab.symm
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2]; group
  set ca := Nat.card (fixV (Subgroup.zpowers a))
  set cb := Nat.card (fixV (Subgroup.zpowers b))
  set cab := Nat.card (fixV (Subgroup.zpowers (a * b)))
  by_cases h1 : cb ≤ ca ∧ cab ≤ ca
  ·
    exact cut_aux_of_sub hW hirr hfix ha2 ha1 hab hDa hDb hDab hgen₁ hgen₃ h1.1
  · by_cases h2 : ca ≤ cb ∧ cab ≤ cb
    ·
      have hDab' : Dab ≤ Kgrp L (b * a) := by rw [hba]; exact hDab
      exact cut_aux_of_sub hW hirr hfix hb2 hb1 hba hDb hDa hDab' (by rw [sup_comm]; exact hgen₁)
        hgen₂ h2.1
    ·
      have hca : ca ≤ cab := by omega
      have hfa : (a * b) * a = b := by
        calc a * b * a = a * (b * a) := by group
          _ = a * (a * b) := by rw [hba]
          _ = (a * a) * b := by group
          _ = b := by rw [ha2]; group
      have hcomm : (a * b) * a = a * (a * b) := by
        rw [hfa]
        calc b = (a * a) * b := by rw [ha2]; group
          _ = a * (a * b) := by group
      have hDb' : Db ≤ Kgrp L ((a * b) * a) := by rw [hfa]; exact hDb
      exact cut_aux_of_sub hW hirr hfix hab2 hab1 hcomm hDab hDa hDb' (by rw [sup_comm]; exact hgen₂)
        hgen₁ hca

end KCut

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
