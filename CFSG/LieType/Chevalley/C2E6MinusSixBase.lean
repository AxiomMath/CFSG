module

public import CFSG.LieType.Chevalley.C2E6MinusSixTail
public import CFSG.LieType.Chevalley.C2E6MinusSixRigidity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.Polynomial.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def vertexStabilizer (S : Set (Submodule (ZMod 2) X)) :
    Subgroup (Equiv.Perm QVertex) where
  carrier := {σ | σ ∈ typeAut ∧ ∀ x : QVertex, x.1 ∈ S → σ x = x}
  mul_mem' {σ τ} hσ hτ := ⟨typeAut.mul_mem hσ.1 hτ.1, fun x hx => by
    rw [Equiv.Perm.mul_apply, hτ.2 x hx, hσ.2 x hx]⟩
  one_mem' := ⟨typeAut.one_mem, fun _ _ => rfl⟩
  inv_mem' {σ} hσ := ⟨typeAut.inv_mem hσ.1, fun x hx => by
    conv_lhs => rw [← hσ.2 x hx]
    exact Equiv.symm_apply_apply σ x⟩

theorem mem_vertexStabilizer {S : Set (Submodule (ZMod 2) X)} {σ : Equiv.Perm QVertex} :
    σ ∈ vertexStabilizer S ↔ σ ∈ typeAut ∧ ∀ x : QVertex, x.1 ∈ S → σ x = x :=
  Iff.rfl

@[expose] def baseFlagSpaces : Set (Submodule (ZMod 2) X) :=
  {(ZMod 2) ∙ e₁, Submodule.span (ZMod 2) {e₁, e₂}, (ZMod 2) ∙ f₁,
    Submodule.span (ZMod 2) {f₁, f₂}}

theorem ptVec_zero : ptVec 0 = e₁ := by decide

theorem ptVec_one : ptVec 1 = e₂ := by decide

theorem ptVec_two : ptVec 2 = f₁ := by decide

theorem ptVec_three : ptVec 3 = f₂ := by decide

theorem coe_ptVertex_zero : (ptVertex 0).1 = (ZMod 2) ∙ e₁ := by
  simp only [ptVertex, ptSub, ptVec_zero]

theorem coe_ptVertex_two : (ptVertex 2).1 = (ZMod 2) ∙ f₁ := by
  simp only [ptVertex, ptSub, ptVec_two]

theorem coe_lnVertex_zero : (lnVertex 0).1 = Submodule.span (ZMod 2) {e₁, e₂} := by
  simp only [lnVertex, lnSub]
  rw [show lnA 0 = 0 from rfl, show lnB 0 = 1 from rfl, ptVec_zero, ptVec_one]

theorem coe_lnVertex_one : (lnVertex 1).1 = Submodule.span (ZMod 2) {f₁, f₂} := by
  simp only [lnVertex, lnSub]
  rw [show lnA 1 = 2 from rfl, show lnB 1 = 3 from rfl, ptVec_two, ptVec_three]

theorem fix_flagBase {σ : Equiv.Perm QVertex} (hσ : σ ∈ vertexStabilizer baseFlagSpaces) :
    ∀ f ∈ flagBase, σ (vertexOf f) = vertexOf f := by
  intro f hf
  simp only [flagBase, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact hσ.2 _ (by rw [vertexOf, coe_ptVertex_zero]; exact Or.inl rfl)
  · exact hσ.2 _ (by rw [vertexOf, coe_ptVertex_two]; exact Or.inr (Or.inr (Or.inl rfl)))
  · exact hσ.2 _ (by rw [vertexOf, coe_lnVertex_zero]; exact Or.inr (Or.inl rfl))
  · exact hσ.2 _ (by rw [vertexOf, coe_lnVertex_one]; exact Or.inr (Or.inr (Or.inr rfl)))

theorem tailLin_eq_self {A : Matrix (Fin 2) (Fin 2) (ZMod 2)} {v : X} (h4 : v 4 = 0)
    (h5 : v 5 = 0) : tailLin A v = v := by
  funext i
  fin_cases i <;> simp [tailLin_apply, h4, h5]

theorem map_span_of_fix (g : QuadraticMap.IsometryEquiv Q Q) {s : Set X} (hs : ∀ v ∈ s, g v = v) :
    (Submodule.span (ZMod 2) s).map (g.toLinearEquiv : X →ₗ[ZMod 2] X) =
      Submodule.span (ZMod 2) s := by
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hs w hw).symm ▸ hw
  · intro hv
    exact ⟨v, hv, hs v hv⟩

theorem tailIso_fix_base (A : GL (Fin 2) (ZMod 2)) :
    ∀ v ∈ ({e₁, e₂, f₁, f₂} : Set X), tailIso A v = v := by
  intro v hv
  rw [tailIso_apply]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> exact tailLin_eq_self (by decide) (by decide)

theorem inducedPerm_tailIso_mem (A : GL (Fin 2) (ZMod 2)) :
    inducedPerm (tailIso A) ∈ vertexStabilizer baseFlagSpaces := by
  refine ⟨inducedPerm_mem_typeAut _, fun x hx => Subtype.ext ?_⟩
  rw [coe_inducedPerm]
  have hfix := tailIso_fix_base A
  rcases hx with h | h | h | h <;> rw [h] <;> refine map_span_of_fix _ fun v hv => hfix v ?_
  all_goals
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
    rcases hv with rfl | rfl <;> simp

theorem ptOn_zero_three : PtOn 0 3 := by decide

theorem lnVertex_injective : Function.Injective lnVertex := fun j j' h =>
  Sum.inr_injective (@vertexOf_injective (.inr j) (.inr j') h)

theorem image_lnVertex_through {σ : Equiv.Perm QVertex} (hσ : σ ∈ typeAut)
    (h0 : σ (ptVertex 0) = ptVertex 0) (hl0 : σ (lnVertex 0) = lnVertex 0)
    (hl2 : σ (lnVertex 2) = lnVertex 2) {j : Fin 45} (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    ∃ a : Fin 45, (a = 3 ∨ a = 4 ∨ a = 5) ∧ σ (lnVertex j) = lnVertex a := by
  obtain ⟨c, hc⟩ := vertexOf_surjective (σ (lnVertex j))
  have htype : CType c = 2 := by
    rw [← type_vertexOf, hc]
    exact (hσ.1 _).trans (type_vertexOf (.inr j))
  rcases c with i | a
  · exact absurd htype (by simp [CType])
  have hinc : CInc (.inr a) (.inl 0) := by
    rw [← incident_vertexOf_iff]
    change (vertexOf (.inr a)).Incident (ptVertex 0)
    rw [hc, ← h0, hσ.2, ← vertexOf, ← vertexOf, incident_vertexOf_iff]
    show PtOn 0 j
    rcases hj with rfl | rfl | rfl <;> decide
  have ha : σ (lnVertex j) = lnVertex a := hc.symm
  rcases (ptOn_zero_iff a).mp hinc with rfl | rfl | h
  · rw [← hl0] at ha
    have := lnVertex_injective (σ.injective ha)
    rcases hj with rfl | rfl | rfl <;> exact absurd this (by decide)
  · rw [← hl2] at ha
    have := lnVertex_injective (σ.injective ha)
    rcases hj with rfl | rfl | rfl <;> exact absurd this (by decide)
  · exact ⟨a, h, ha⟩

theorem eq_inducedPerm_of_agree {σ : Equiv.Perm QVertex}
    (hσ : σ ∈ vertexStabilizer baseFlagSpaces) (A : GL (Fin 2) (ZMod 2))
    (h3 : inducedPerm (tailIso A) (lnVertex 3) = σ (lnVertex 3))
    (h4 : inducedPerm (tailIso A) (lnVertex 4) = σ (lnVertex 4)) :
    σ = inducedPerm (tailIso A) := by
  set g := inducedPerm (tailIso A)
  have hg := inducedPerm_tailIso_mem A
  have hτ : g⁻¹ * σ ∈ typeAut := typeAut.mul_mem (typeAut.inv_mem hg.1) hσ.1
  have hfix : ∀ f ∈ rigidBase, (g⁻¹ * σ) (vertexOf f) = vertexOf f := by
    intro f hf
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    simp only [rigidBase, List.mem_cons, List.not_mem_nil, or_false] at hf
    have hσF := fix_flagBase hσ
    have hgF := fix_flagBase hg
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hσF _ (by decide), hgF _ (by decide)]
    · rw [hσF _ (by decide), hgF _ (by decide)]
    · rw [hσF _ (by decide), hgF _ (by decide)]
    · rw [hσF _ (by decide), hgF _ (by decide)]
    · exact h3.symm
    · exact h4.symm
  have := eq_one_of_fix_base hτ hfix
  rw [inv_mul_eq_one] at this
  exact this.symm

@[expose] def glSwap : GL (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide, by decide⟩

@[expose] def glRot : GL (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 1], !![1, 1; 1, 0], by decide, by decide⟩

@[expose] def glRot' : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 1, 0], !![0, 1; 1, 1], by decide, by decide⟩

@[expose] def glLow : GL (Fin 2) (ZMod 2) := ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩

@[expose] def glUp : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩

theorem tail_glSwap_11 : tailIso glSwap (ptVec 11) = ptVec 17 := by decide
theorem tail_glSwap_17 : tailIso glSwap (ptVec 17) = ptVec 11 := by decide
theorem tail_glRot_11 : tailIso glRot (ptVec 11) = ptVec 17 := by decide
theorem tail_glRot_17 : tailIso glRot (ptVec 17) = ptVec 23 := by decide
theorem tail_glRot'_11 : tailIso glRot' (ptVec 11) = ptVec 23 := by decide
theorem tail_glRot'_17 : tailIso glRot' (ptVec 17) = ptVec 11 := by decide
theorem tail_glLow_11 : tailIso glLow (ptVec 11) = ptVec 23 := by decide
theorem tail_glLow_17 : tailIso glLow (ptVec 17) = ptVec 17 := by decide
theorem tail_glUp_11 : tailIso glUp (ptVec 11) = ptVec 11 := by decide
theorem tail_glUp_17 : tailIso glUp (ptVec 17) = ptVec 23 := by decide

theorem tail_ptVec_zero (A : GL (Fin 2) (ZMod 2)) : tailIso A (ptVec 0) = ptVec 0 := by
  rw [ptVec_zero]
  exact tailIso_fix_base A e₁ (by simp)

theorem tail_lnVertex_three (A : GL (Fin 2) (ZMod 2)) {p : Fin 27} {a : Fin 45}
    (hp : tailIso A (ptVec 11) = ptVec p) (hpa : PtOn p a) (ha : PtOn 0 a) (hp0 : 0 ≠ p) :
    inducedPerm (tailIso A) (lnVertex 3) = lnVertex a :=
  inducedPerm_lnVertex _ (tail_ptVec_zero A) hp ha hpa hp0

theorem tail_lnVertex_four (A : GL (Fin 2) (ZMod 2)) {p : Fin 27} {a : Fin 45}
    (hp : tailIso A (ptVec 17) = ptVec p) (hpa : PtOn p a) (ha : PtOn 0 a) (hp0 : 0 ≠ p) :
    inducedPerm (tailIso A) (lnVertex 4) = lnVertex a :=
  inducedPerm_lnVertex _ (tail_ptVec_zero A) hp ha hpa hp0

theorem tail_glOne_11 : tailIso 1 (ptVec 11) = ptVec 11 := by decide
theorem tail_glOne_17 : tailIso 1 (ptVec 17) = ptVec 17 := by decide

theorem tail_case {σ : Equiv.Perm QVertex} (hσ : σ ∈ vertexStabilizer baseFlagSpaces)
    (A : GL (Fin 2) (ZMod 2)) {p q : Fin 27} {a b : Fin 45}
    (hp : tailIso A (ptVec 11) = ptVec p) (hq : tailIso A (ptVec 17) = ptVec q)
    (hpa : PtOn p a) (hqb : PtOn q b) (ha : PtOn 0 a) (hb : PtOn 0 b) (hp0 : 0 ≠ p)
    (hq0 : 0 ≠ q) (ha' : σ (lnVertex 3) = lnVertex a) (hb' : σ (lnVertex 4) = lnVertex b) :
    σ = inducedPerm (tailIso A) :=
  eq_inducedPerm_of_agree hσ A ((tail_lnVertex_three A hp hpa ha hp0).trans ha'.symm)
    ((tail_lnVertex_four A hq hqb hb hq0).trans hb'.symm)

theorem exists_tail_of_mem {σ : Equiv.Perm QVertex}
    (hσ : σ ∈ vertexStabilizer baseFlagSpaces) :
    ∃ A : GL (Fin 2) (ZMod 2), σ = inducedPerm (tailIso A) := by
  have hF := fix_flagBase hσ
  have h0 : σ (ptVertex 0) = ptVertex 0 := hF (.inl 0) (by decide)
  have hl0 : σ (lnVertex 0) = lnVertex 0 := hF (.inr 0) (by decide)
  have hl2 := fix_lnVertex_two hσ.1 hF
  obtain ⟨a, ha, ha'⟩ := image_lnVertex_through hσ.1 h0 hl0 hl2 (j := 3) (by decide)
  obtain ⟨b, hb, hb'⟩ := image_lnVertex_through hσ.1 h0 hl0 hl2 (j := 4) (by decide)
  have hab : a ≠ b := by
    rintro rfl
    have := lnVertex_injective (σ.injective (ha'.trans hb'.symm))
    exact absurd this (by decide)
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · exact ⟨1, tail_case hσ 1 tail_glOne_11 tail_glOne_17 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ha' hb'⟩
  · exact ⟨glUp, tail_case hσ glUp tail_glUp_11 tail_glUp_17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ha' hb'⟩
  · exact ⟨glSwap, tail_case hσ glSwap tail_glSwap_11 tail_glSwap_17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ha' hb'⟩
  · exact absurd rfl hab
  · exact ⟨glRot, tail_case hσ glRot tail_glRot_11 tail_glRot_17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ha' hb'⟩
  · exact ⟨glRot', tail_case hσ glRot' tail_glRot'_11 tail_glRot'_17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ha' hb'⟩
  · exact ⟨glLow, tail_case hσ glLow tail_glLow_11 tail_glLow_17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ha' hb'⟩
  · exact absurd rfl hab

theorem mem_baseStabilizer_iff {σ : Equiv.Perm QVertex} :
    σ ∈ vertexStabilizer baseFlagSpaces ↔ ∃ A : GL (Fin 2) (ZMod 2), σ = inducedPerm (tailIso A) :=
  ⟨exists_tail_of_mem, by rintro ⟨A, rfl⟩; exact inducedPerm_tailIso_mem A⟩

theorem eq_of_span_singleton_eq {u v : X} (hu : u ≠ 0)
    (h : (ZMod 2) ∙ u = (ZMod 2) ∙ v) : u = v := by
  have : u ∈ (ZMod 2) ∙ v := h ▸ Submodule.mem_span_singleton_self u
  rcases mem_span_singleton_zmod_two.mp this with h0 | h1
  · exact absurd h0 hu
  · exact h1

theorem tail_eq_of_inducedPerm_eq {A B : GL (Fin 2) (ZMod 2)}
    (h : inducedPerm (tailIso A) = inducedPerm (tailIso B)) (i : Fin 27) :
    tailLin A (ptVec i) = tailLin B (ptVec i) := by
  have hx := congrArg Subtype.val (congrFun (congrArg DFunLike.coe h) (ptVertex i))
  simp only [coe_inducedPerm, ptVertex, ptSub, Submodule.map_span, Set.image_singleton] at hx
  refine eq_of_span_singleton_eq ?_ hx
  intro h0
  have := congrArg (tailLin (↑A⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod 2))) h0
  rw [← tailLin_mul, Units.inv_mul, tailLin_one, map_zero] at this
  exact ptVec_ne_zero i this

theorem inducedPerm_tailIso_injective :
    Function.Injective fun A : GL (Fin 2) (ZMod 2) => inducedPerm (tailIso A) := by
  intro A B h
  have h11 := tail_eq_of_inducedPerm_eq h 11
  have h17 := tail_eq_of_inducedPerm_eq h 17
  have e11 : ∀ C : GL (Fin 2) (ZMod 2), tailLin C (ptVec 11) =
      ![0, 1, 0, 1, (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0,
        (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0] := fun C => by
    funext k
    fin_cases k <;> simp [tailLin_apply, ptVec]
  have e17 : ∀ C : GL (Fin 2) (ZMod 2), tailLin C (ptVec 17) =
      ![0, 1, 0, 1, (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1,
        (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1] := fun C => by
    funext k
    fin_cases k <;> simp [tailLin_apply, ptVec]
  rw [e11, e11] at h11
  rw [e17, e17] at h17
  apply Units.ext
  ext r s
  fin_cases r <;> fin_cases s
  · exact congrFun h11 4
  · exact congrFun h17 4
  · exact congrFun h11 5
  · exact congrFun h17 5

theorem card_GL_two_zmod_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  rfl

theorem card_baseStabilizer : Nat.card (vertexStabilizer baseFlagSpaces) = 6 := by
  rw [← card_GL_two_zmod_two]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun A : GL (Fin 2) (ZMod 2) => (⟨inducedPerm (tailIso A), inducedPerm_tailIso_mem A⟩ :
      vertexStabilizer baseFlagSpaces)) ⟨fun A B h => ?_, fun σ => ?_⟩)).symm
  · exact inducedPerm_tailIso_injective (congrArg Subtype.val h)
  · obtain ⟨A, hA⟩ := exists_tail_of_mem σ.2
    exact ⟨A, Subtype.ext hA.symm⟩

end CFSG.LieType.Chevalley.C2E6Overlap
