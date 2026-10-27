module

public import CFSG.Fischer.Classification.PartIII.U4.Classify
public import CFSG.Fischer.Classification.PartIII.R3.Admissible

public section

namespace CFSG.Fischer.Classification.LocalU4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.Beta
  CFSG.Fischer.Classification.LocalR3 F3

theorem exists_mulEquiv_PG_four_R3_I5 : ∃ Ξ : PG 4 ≃* R3 I5Form,
    (∀ i, Ξ (pt i) = (oElt i : R3 I5Form)) ∧ Ξ '' DG 4 = D3 I5Form := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_U2_four_R3_I5_eq
  refine ⟨(u2Equiv 4).symm.trans ψ, fun i => ?_, ?_⟩
  · have h : (u2Equiv 4).symm (pt i) = (uElt i : U2 4) := by
      rw [coe_uElt, tqU_eq]
      rfl
    rw [MulEquiv.trans_apply, h, hψ, betaEquiv_uElt]
  · rw [MulEquiv.coe_trans, Set.image_comp, ← image_DU, image_symm_image,
      image_eq_of_forall_eq betaEquiv hψ]

theorem I5Form_oPt (i : Fin 45) : I5Form (oPt i) (oPt i) = 1 := by
  rw [I5Form_eq_dot5]
  exact dot5_oPt i

theorem sPt_I5Form_eq (z : Fin 5 → ZMod 3) :
    sPt I5Form z = (fun i => (oElt i : R3 I5Form)) '' {i | dot5 1 (oPt i) z = 0} := by
  ext q
  constructor
  · rintro ⟨w, hw, hwz, rfl⟩
    obtain ⟨i, hi⟩ := oElt_bijective.2 ⟨reflBar I5Form w, reflBar_mem_D3 hw⟩
    have hq : (oElt i : R3 I5Form) = reflBar I5Form w := congrArg Subtype.val hi
    refine ⟨i, ?_, hq⟩
    have h : reflBar I5Form (oPt i) ∈ sPt I5Form z := by
      rw [← coe_oElt, hq]
      exact ⟨w, hw, hwz, rfl⟩
    rw [reflBar_mem_sPt_iff isF3Form_I5Form (by norm_num) (I5Form_oPt i), I5Form_eq_dot5] at h
    exact h
  · rintro ⟨i, hi, rfl⟩
    exact ⟨oPt i, I5Form_oPt i, by rw [I5Form_eq_dot5]; exact hi, (coe_oElt i).symm⟩

@[expose] def zStar : Fin 5 → ZMod 3 := ![0, 1, 1, 1, 0]

theorem zStar_ne_zero : zStar ≠ 0 := fun h => by
  have := congrFun h 1
  simp [zStar] at this

theorem I5Form_zStar : I5Form zStar zStar = 0 := by
  rw [I5Form_eq_dot5]
  decide +kernel

theorem chk_zStar : ∀ i : Fin 45, dot5 1 (oPt i) zStar = 0 ↔ InI18 i := by
  decide +kernel

theorem image_M18_eq_sPt {Ξ : PG 4 ≃* R3 I5Form} (hΞ : ∀ i, Ξ (pt i) = (oElt i : R3 I5Form)) :
    Ξ '' M18 = sPt I5Form zStar := by
  rw [M18, Set.image_image, sPt_I5Form_eq]
  refine (Set.image_congr fun i _ => hΞ i).trans ?_
  congr 1
  ext i
  exact (chk_zStar i).symm

theorem chk_card_sPt : ∀ a b c d e : ZMod 3, ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) →
    dot5 1 ![a, b, c, d, e] ![a, b, c, d, e] = 0 →
      (Finset.univ.filter fun i => dot5 1 (oPt i) ![a, b, c, d, e] = 0).card = 18 := by
  decide +kernel

theorem ncard_sPt_I5Form {z : Fin 5 → ZMod 3} (hz0 : z ≠ 0) (hzz : I5Form z z = 0) :
    (sPt I5Form z).ncard = 18 := by
  have hinj : Function.Injective fun i => (oElt i : R3 I5Form) :=
    Subtype.val_injective.comp oElt_bijective.1
  rw [sPt_I5Form_eq, Set.ncard_image_of_injective _ hinj]
  rw [vec5_eq z] at hz0 hzz ⊢
  rw [I5Form_eq_dot5] at hzz
  have h0 : ¬(z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 ∧ z 4 = 0) := by
    rintro ⟨h0, h1, h2, h3, h4⟩
    apply hz0
    rw [h0, h1, h2, h3, h4]
    funext i
    fin_cases i <;> rfl
  rw [← chk_card_sPt _ _ _ _ _ h0 hzz, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

end CFSG.Fischer.Classification.LocalU4
