module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphFpf
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrPerm

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF diagGL eq_bot_of_four_group isometrySL)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] noncomputable def ClU.slIso1 (R : GL (Fin n) h.fixedField) :
    isometrySL n R →* iso1 h R :=
  MonoidHom.codRestrict (Matrix.SpecialLinearGroup.toGL.comp (isometrySL n R).subtype)
    (iso1 h R) fun X => Subgroup.mem_inf.2 ⟨X.2, by
      rw [MonoidHom.mem_ker]
      refine Units.ext ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact (X : Matrix.SpecialLinearGroup (Fin n) h.fixedField).2⟩

@[expose] noncomputable def ClU.signIS {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0)
    {i j : Fin n} (hij : i ≠ j) : isometrySL n (diagGL hw) :=
  ⟨Gr.signPair hij, Gr.signPair_mem_isometry hw hij⟩

theorem ClU.coe_signIS {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0) {i j : Fin n}
    (hij : i ≠ j) :
    ((ClU.signIS h hw hij : isometrySL n (diagGL hw)) :
      Matrix.SpecialLinearGroup (Fin n) h.fixedField) = Gr.signPair hij := rfl

theorem ClU.slIso1_signIS {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0) {i j : Fin n}
    (hij : i ≠ j) :
    ClU.slIso1 h (diagGL hw) (ClU.signIS h hw hij) =
      signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two) :=
  Subtype.ext (Units.ext rfl)

theorem ClU.graphOrth_eq_one_three (hp3 : p ^ f = 3) (hn3 : 3 ≤ n) (hn4 : n ≤ 4)
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : OrthNF w)
    (hR : ((diagGL hw.1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {Y : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))} (hYodd : Odd (Nat.card Y))
    (hYi : ∀ y ∈ Y, y * (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) =
      (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) * y)
    (hYc : ∀ x, (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h) :
        MulAut (StatedProj (StatedSU n (p ^ f) K))) x = x →
      Odd (orderOf x) → ∀ y ∈ Y, MulAut.conj x * y * (MulAut.conj x)⁻¹ ∈ Y) :
    ∀ y ∈ Y, y = 1 := by
  have := h.finite
  have : Finite Y := inferInstance
  obtain ⟨I, hI3, -, hIw⟩ := hw.2
  obtain ⟨a, ha, a', ha', d, hd, hab, had, hbd⟩ := Finset.two_lt_card.1 (by omega : 2 < I.card)
  obtain ⟨c, hcs, hc3, hca, hcb, hcd, hco⟩ := Gr.exists_three_cycle hab had hbd
  have hwc : ∀ x, w (c x) = w x := by
    intro x
    by_cases hxa : x = a
    · rw [hxa, hca]; exact hIw _ ha' _ ha
    · by_cases hxb : x = a'
      · rw [hxb, hcb]; exact hIw _ hd _ ha'
      · by_cases hxd : x = d
        · rw [hxd, hcd]; exact hIw _ ha _ hd
        · rw [hco x hxa hxb hxd]
  set ψ := (conjProjH (StatedSU n (p ^ f) K)).comp
    ((gHom h hPPi hPiP hs hR).comp (ClU.slIso1 h (diagGL hw.1))) with hψ
  have hnorm3 : ∀ x : isometrySL n (diagGL hw.1), x ^ 3 = 1 → ∀ y ∈ Y,
      ψ x * y * (ψ x)⁻¹ ∈ Y := by
    intro x hx3 y hy
    set g := gHom h hPPi hPiP hs hR (ClU.slIso1 h (diagGL hw.1) x) with hg
    have hfix : (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h) :
        MulAut (StatedProj (StatedSU n (p ^ f) K))) (projH (StatedSU n (p ^ f) K) g) =
          projH (StatedSU n (p ^ f) K) g := by
      rw [uLift_proj h (by omega) A (barEq h), hg, uLift_gHom h hPPi hPiP hs hR hb hbP]
    have hg3 : g ^ 3 = 1 := by rw [hg, ← map_pow, ← map_pow, hx3, map_one, map_one]
    have hodd : Odd (orderOf (projH (StatedSU n (p ^ f) K) g)) :=
      Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg3, map_one]))
    exact hYc _ hfix hodd y hy
  set P₃ : isometrySL n (diagGL hw.1) :=
    ⟨Gr.permSL c hcs, Gr.permSL_mem_isometry hw.1 c hcs hwc⟩ with hP₃
  have hP3 : P₃ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact Gr.permSL_pow_eq_one c hcs hc3)
  have hnorm : ∀ {i j : Fin n} (hij : i ≠ j), ∀ y ∈ Y,
      ψ (P₃ * ClU.signIS h hw.1 hij * P₃⁻¹ * (ClU.signIS h hw.1 hij)⁻¹) * y *
        (ψ (P₃ * ClU.signIS h hw.1 hij * P₃⁻¹ * (ClU.signIS h hw.1 hij)⁻¹))⁻¹ ∈ Y := by
    intro i j hij y hy
    set S := ClU.signIS h hw.1 hij with hS
    set y' := S * P₃⁻¹ * S⁻¹ with hy'
    have hy3 : y' ^ 3 = 1 := by
      rw [hy', conj_pow, inv_pow, hP3, inv_one, mul_one, mul_inv_cancel]
    have e : P₃ * S * P₃⁻¹ * S⁻¹ = P₃ * y' := by rw [hy']; group
    rw [e, map_mul]
    have h2 := hnorm3 P₃ hP3 _ (hnorm3 y' hy3 y hy)
    have e2 : ψ P₃ * ψ y' * y * (ψ P₃ * ψ y')⁻¹ =
        ψ P₃ * (ψ y' * y * (ψ y')⁻¹) * (ψ P₃)⁻¹ := by group
    rw [e2]
    exact h2
  have hcomm₁ : P₃ * ClU.signIS h hw.1 hab * P₃⁻¹ * (ClU.signIS h hw.1 hab)⁻¹ =
      ClU.signIS h hw.1 had := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ClU.coe_signIS, hP₃]
    rw [Gr.conj_signSL_pair, Gr.signPair_inv, Gr.signPair_eq (c.injective.ne hab) hbd hca hcb,
      Gr.signPair_comm hbd, Gr.signPair_comm hab, Gr.signPair_mul hbd.symm hab.symm had.symm]
    exact (Gr.signPair_comm had).symm
  have hcomm₂ : P₃ * ClU.signIS h hw.1 had * P₃⁻¹ * (ClU.signIS h hw.1 had)⁻¹ =
      ClU.signIS h hw.1 hbd := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ClU.coe_signIS, hP₃]
    rw [Gr.conj_signSL_pair, Gr.signPair_inv, Gr.signPair_eq (c.injective.ne had) hab.symm hca hcd]
    exact Gr.signPair_mul hab.symm had hbd
  have hsq : ∀ {i j : Fin n} (hij : i ≠ j),
      ψ (ClU.signIS h hw.1 hij) * ψ (ClU.signIS h hw.1 hij) = 1 := by
    intro i j hij
    rw [← map_mul, show ClU.signIS h hw.1 hij * ClU.signIS h hw.1 hij = 1 from
      Subtype.ext (Gr.signPair_mul_self hij), map_one]
  have h12 : ψ (ClU.signIS h hw.1 had) * ψ (ClU.signIS h hw.1 hbd) =
      ψ (ClU.signIS h hw.1 hab) := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, ClU.coe_signIS, ClU.coe_signIS, ClU.coe_signIS, Gr.signPair_comm hbd,
      Gr.signPair_mul had hbd.symm hab]
  have hfpf : ∀ {i j : Fin n} (hij : i ≠ j), ∀ x ∈ Y,
      ψ (ClU.signIS h hw.1 hij) * x = x * ψ (ClU.signIS h hw.1 hij) → x = 1 := by
    intro i j hij x hx hc
    have e : ψ (ClU.signIS h hw.1 hij) = conjProjH (StatedSU n (p ^ f) K)
        (gHom h hPPi hPiP hs hR
          (signIso h hw.1 {i, j} (by rw [Finset.card_pair hij]; exact even_two))) := by
      change conjProjH (StatedSU n (p ^ f) K) (gHom h hPPi hPiP hs hR
        (ClU.slIso1 h (diagGL hw.1) (ClU.signIS h hw.1 hij))) = _
      rw [ClU.slIso1_signIS]
    rw [e] at hc
    exact ClU.graph_three_fpf h hp3 hn3 hn4 hPPi hPiP hb hbP hs hw.1 hR hij
      (ClSp.odd_orderOf_of_mem hYodd hx) (hYi x hx) hc
  have hYb : Y = ⊥ := eq_bot_of_four_group (hsq had) (hsq hbd)
    (fun x hx => by
      have := hnorm hab x hx
      rwa [hcomm₁] at this)
    (fun x hx => by
      have := hnorm had x hx
      rwa [hcomm₂] at this)
    (hfpf had) (hfpf hbd)
    (fun x hx hc => by
      rw [h12] at hc
      exact hfpf hab x hx hc)
  intro y hy
  rw [hYb] at hy
  exact mem_bot.1 hy

end CFSG.ComponentClassification.Foote5.OddLieCore
