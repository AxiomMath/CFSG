module

public import CFSG.Fischer.Classification.PartIII.Beta.Data
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
public import CFSG.Fischer.Classification.PartIII.Beta.Transport

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open F3

namespace Beta

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem bijective_reflBar_of_reps (hf : IsF3Form f) (hm : 4 ≤ m) {N : ℕ}
    (p : Fin N → Fin m → ZMod 3) (idx : (Fin m → ZMod 3) → Fin N) (hp : ∀ i, f (p i) (p i) = 1)
    (hidx : ∀ i, idx (p i) = i ∧ idx (-p i) = i)
    (hsurj : ∀ w, f w w = 1 → p (idx w) = w ∨ p (idx w) = -w) :
    Function.Bijective fun i => (⟨reflBar f (p i), reflBar_mem_D3 (hp i)⟩ : D3 f) := by
  refine ⟨fun i j hij => ?_, fun q => ?_⟩
  · have h := congrArg Subtype.val hij
    rcases (reflBar_eq_reflBar_iff hf hm (hp i) (hp j)).1 h with h1 | h1
    · rw [← (hidx j).1, h1, (hidx i).1]
    · rw [← (hidx j).1, h1, (hidx i).2]
  · obtain ⟨w, hw, hq⟩ := mem_D3_iff.1 q.2
    refine ⟨idx w, Subtype.ext ?_⟩
    show reflBar f (p (idx w)) = q
    rw [← hq]
    rcases hsurj w hw with h1 | h1 <;> rw [h1]
    exact reflBar_neg w

theorem vec5_eq (w : Fin 5 → ZMod 3) : w = ![w 0, w 1, w 2, w 3, w 4] := by
  ext i
  fin_cases i <;> rfl

theorem diagF3_five_apply (δ : ZMod 3) (x y : Fin 5 → ZMod 3) :
    diagF3 5 δ x y = dot5 δ x y := by
  rw [diagF3_apply, Fin.sum_univ_five, dot5]
  simp only [diagF3Entry]
  norm_num

theorem I5Form_eq_dot5 (x y : Fin 5 → ZMod 3) : I5Form x y = dot5 1 x y := by
  rw [← diagF3_five_one, diagF3_five_apply]

theorem act_refl_I5Form {w : Fin 5 → ZMod 3} (hw : I5Form w w = 1) (v : Fin 5 → ZMod 3) :
    act (refl I5Form w) v = rO w v := by
  rw [act_refl hw, I5Form_eq_dot5, rO]

@[expose] noncomputable def oElt (i : Fin 45) : D3 I5Form :=
  ⟨reflBar I5Form (oPt i), reflBar_mem_D3 (by rw [I5Form_eq_dot5]; exact dot5_oPt i)⟩

theorem coe_oElt (i : Fin 45) : (oElt i : R3 I5Form) = reflBar I5Form (oPt i) :=
  rfl

theorem oElt_bijective : Function.Bijective oElt :=
  bijective_reflBar_of_reps isF3Form_I5Form (by norm_num) oPt oIdx
    (fun i => by rw [I5Form_eq_dot5]; exact dot5_oPt i) oIdx_oPt fun w hw => by
      rw [I5Form_eq_dot5, vec5_eq w] at hw
      rw [vec5_eq w]
      exact oPt_oIdx _ _ _ _ _ hw

@[expose] noncomputable def qElt (i : Fin 36) : D3 (diagF3 5 2) :=
  ⟨reflBar (diagF3 5 2) (qPt i), reflBar_mem_D3 (by rw [diagF3_five_apply]; exact dot5_qPt i)⟩

theorem qElt_bijective : Function.Bijective qElt :=
  bijective_reflBar_of_reps (isF3Form_diagF3 (by decide)) (by norm_num) qPt qIdx
    (fun i => by rw [diagF3_five_apply]; exact dot5_qPt i) qIdx_qPt fun w hw => by
      rw [diagF3_five_apply, vec5_eq w] at hw
      rw [vec5_eq w]
      exact qPt_qIdx _ _ _ _ _ hw

end Beta

open Beta

theorem ncard_D3_diagF3_five_one : (D3 (diagF3 5 1)).ncard = 45 := by
  rw [diagF3_five_one, ← Nat.card_coe_set_eq, ← Nat.card_eq_of_bijective _ oElt_bijective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_D3_diagF3_five_two : (D3 (diagF3 5 2)).ncard = 36 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_eq_of_bijective _ qElt_bijective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_D3_of_isometry {m : ℕ} {f f' : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) (he : ∀ x y, f x y = f' (e x) (e y)) :
    (D3 f).ncard = (D3 f').ncard := by
  rw [← image_D3_R3Congr he, Set.ncard_image_of_injective _ (R3Congr e he).injective]

theorem R3_five_cases {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf : IsF3Form f) :
    ((D3 f).ncard = 45 ∧ ∃ ψ : R3 f ≃* R3 I5Form, ψ '' D3 f = D3 I5Form) ∨
      ((D3 f).ncard = 36 ∧ ∃ ψ : R3 f ≃* R3 (diagF3 5 2), ψ '' D3 f = D3 (diagF3 5 2)) := by
  obtain ⟨δ, e, hδ, he⟩ := exists_linearEquiv_diagF3 (by norm_num) hf
  rcases hδ with rfl | rfl
  · left
    rw [diagF3_five_one] at he
    exact ⟨(ncard_D3_of_isometry e he).trans (diagF3_five_one ▸ ncard_D3_diagF3_five_one),
      exists_mulEquiv_R3_of_isometry e he⟩
  · right
    exact ⟨(ncard_D3_of_isometry e he).trans ncard_D3_diagF3_five_two,
      exists_mulEquiv_R3_of_isometry e he⟩

end CFSG.Fischer.Classification
