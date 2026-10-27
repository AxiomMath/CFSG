module

public import CFSG.Quasithin.Background.G2UAdjoint
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import Certificates.Certificate12042

public section

namespace CFSG.LieType.Multipliers.G23

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.Sporadic.He.Native CFSG.CosetTable
  CFSG.Sporadic.Bridge.TwoGen

theorem model_facts :
    toMat 3 14 aArr * toMat 3 14 aArr = 1 ∧ toMat 3 14 bArr * toMat 3 14 bInvArr = 1 ∧
      (∀ r ∈ rels, toMat 3 14 (wordArr r) = 1) ∧
      (∀ j, toMat 3 14 (wordArr (genWord j)) = rootMat j) ∧
      ∀ i, toMat 3 14 (wordArr (commWords (pairs i))) = toMat 3 14 (letterArr (i, true)) :=
  Certificates.certificate12042.1

theorem card_le :
    Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 4245696 :=
  Certificates.certificate12042.2

theorem toMat_arrOf (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : toMat 3 14 (arrOf M) = M := by
  ext i j
  rw [toMat_apply, arrOf, getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]
  exact ZMod.natCast_zmod_val _

theorem rootMat_cube : ∀ j, rootMat j * (rootMat j * rootMat j) = 1 := by
  decide +kernel

@[expose] def xIdx (i : Fin Tag.G2.rank) : Fin 4 := if i = ix 0 then 0 else 1

@[expose] def yIdx (i : Fin Tag.G2.rank) : Fin 4 := if i = ix 0 then 2 else 3

theorem XMat_eq_rootMat_pow : ∀ (i : Fin Tag.G2.rank) (t : ZMod 3),
    XMat (ZMod 3) i t = rootMat (xIdx i) ^ t.val ∧
      YMat (ZMod 3) i t = rootMat (yIdx i) ^ t.val := by
  decide +kernel

@[expose] def rootUnit (j : Fin 4) : GL (Fin 14) (ZMod 3) :=
  ⟨rootMat j, rootMat j * rootMat j, rootMat_cube j, by rw [Matrix.mul_assoc, rootMat_cube j]⟩

variable {K : Type} [Field K] (σ : K ≃+* ZMod 3)

noncomputable def rootOp : Fin 4 → Module.End K (RootModule .G2 K)
  | 0 => xOp .G2 K (ix 0) (σ.symm 1)
  | 1 => xOp .G2 K (ix 1) (σ.symm 1)
  | 2 => yOp .G2 K (ix 0) (σ.symm 1)
  | 3 => yOp .G2 K (ix 1) (σ.symm 1)

theorem endEquiv_rootOp (j : Fin 4) : endEquiv σ (rootOp σ j) = rootMat j := by
  fin_cases j <;>
    simp [rootOp, rootMat, endEquiv_xOp, endEquiv_yOp]

theorem coe_glEquiv_symm_rootUnit (j : Fin 4) :
    (((glEquiv σ).symm (rootUnit j) : ModGL .G2 K) : Module.End K (RootModule .G2 K)) =
      rootOp σ j := by
  apply (endEquiv σ).injective
  rw [← coe_glEquiv, MulEquiv.apply_symm_apply, endEquiv_rootOp]
  rfl

theorem glEquiv_symm_rootUnit_mem (j : Fin 4) :
    (glEquiv σ).symm (rootUnit j) ∈ adjointGroup .G2 K := by
  apply Subgroup.subset_closure
  have h := coe_glEquiv_symm_rootUnit σ j
  fin_cases j
  · exact ⟨ix 0, σ.symm 1, Or.inl h⟩
  · exact ⟨ix 1, σ.symm 1, Or.inl h⟩
  · exact ⟨ix 0, σ.symm 1, Or.inr h⟩
  · exact ⟨ix 1, σ.symm 1, Or.inr h⟩

noncomputable def rootElt (j : Fin 4) : adjointGroup .G2 K :=
  ⟨(glEquiv σ).symm (rootUnit j), glEquiv_symm_rootUnit_mem σ j⟩

noncomputable def matHom : adjointGroup .G2 K →* GL (Fin 14) (ZMod 3) :=
  (glHom σ).comp (adjointGroup .G2 K).subtype

theorem matHom_injective : Function.Injective (matHom σ) :=
  (glHom_injective σ).comp Subtype.val_injective

theorem matHom_rootElt (j : Fin 4) : matHom σ (rootElt σ j) = rootUnit j := by
  simp [matHom, rootElt, glHom_apply]

theorem val_matHom_prod (js : List (Fin 4)) :
    ((matHom σ (js.map (rootElt σ)).prod : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 (rootProd js) := by
  induction js with
  | nil => rw [List.map_nil, List.prod_nil, map_one, Units.val_one, rootProd, List.foldr_nil,
      toMat_idM]
  | cons j js ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Units.val_mul, ih, matHom_rootElt]
    change _ = toMat 3 14 (mulM 3 14 (rootArr j) (rootProd js))
    rw [toMat_mulM, rootArr, toMat_arrOf]
    rfl

noncomputable def aElt : adjointGroup .G2 K := (aWord.map (rootElt σ)).prod

noncomputable def bElt : adjointGroup .G2 K := (bWord.map (rootElt σ)).prod

noncomputable def gens (i : Fin 2) : adjointGroup .G2 K := img2 (aElt σ) (bElt σ) i.val

theorem val_matHom_letter (l : Fin 2 × Bool) :
    ((matHom σ (cond l.2 (gens σ l.1) (gens σ l.1)⁻¹) : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 (letterArr l) := by
  obtain ⟨h1, h2, -⟩ := model_facts
  have ha : ((matHom σ (aElt σ) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 aArr := val_matHom_prod σ aWord
  have hb : ((matHom σ (bElt σ) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 bArr := val_matHom_prod σ bWord
  have ha' : (matHom σ (aElt σ))⁻¹ = matHom σ (aElt σ) :=
    inv_eq_of_mul_eq_one_right (Units.ext (by rw [Units.val_mul, ha, h1, Units.val_one]))
  have hb' : (matHom σ (bElt σ))⁻¹ = matHom σ (bElt σ) * matHom σ (bElt σ) :=
    inv_eq_of_mul_eq_one_right (Units.ext (by
      rw [Units.val_mul, Units.val_mul, hb, ← toMat_mulM, ← bInvArr, h2, Units.val_one]))
  obtain ⟨i, s⟩ := l
  fin_cases i <;> cases s
  · change ((matHom σ (aElt σ)⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = _
    rw [map_inv, ha', ha]
    rfl
  · exact ha
  · change ((matHom σ (bElt σ)⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = _
    rw [map_inv, hb', Units.val_mul, hb, ← toMat_mulM]
    rfl
  · exact hb

theorem val_matHom_lift (w : List (Fin 2 × Bool)) :
    ((matHom σ (FreeGroup.lift (gens σ) (FreeGroup.mk w)) : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 (wordArr w) := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => rw [List.map_nil, List.prod_nil, map_one, Units.val_one, wordArr, List.foldr_nil,
      toMat_idM]
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Units.val_mul, ih, val_matHom_letter]
    change _ = toMat 3 14 (mulM 3 14 (letterArr l) (wordArr w))
    rw [toMat_mulM]

theorem lift_gens_eq_of_toMat {w : List (Fin 2 × Bool)}
    {g : adjointGroup .G2 K}
    (h : toMat 3 14 (wordArr w) =
      ((matHom σ g : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3))) :
    FreeGroup.lift (gens σ) (FreeGroup.mk w) = g :=
  matHom_injective σ (Units.ext (by rw [val_matHom_lift, h]))

theorem lift_gens_rels :
    ∀ r ∈ wordSet rels, FreeGroup.lift (gens σ) r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact lift_gens_eq_of_toMat σ (by rw [model_facts.2.2.1 w hw, map_one, Units.val_one])

theorem lift_gens_commWords (i : Fin 2) :
    FreeGroup.lift (gens σ) (FreeGroup.mk (commWords (pairs i))) = gens σ i :=
  lift_gens_eq_of_toMat σ (by rw [model_facts.2.2.2.2 i, ← val_matHom_letter σ (i, true)]; rfl)

theorem lift_gens_genWord (j : Fin 4) :
    FreeGroup.lift (gens σ) (FreeGroup.mk (genWord j)) = rootElt σ j :=
  lift_gens_eq_of_toMat σ (by rw [model_facts.2.2.2.1 j, matHom_rootElt]; rfl)

theorem closure_range_gens :
    Subgroup.closure (Set.range (gens σ)) = ⊤ := by
  have hroot : ∀ (j : Fin 4) (n : ℕ), rootElt σ j ^ n ∈ Subgroup.closure (Set.range (gens σ)) :=
    fun j n => by
      refine pow_mem ?_ n
      rw [← lift_gens_genWord, ← FreeGroup.range_lift_eq_closure]
      exact ⟨_, rfl⟩
  set H := Subgroup.closure (Set.range (gens σ))
  have hpow : ∀ (j : Fin 4) (n : ℕ) (g : ModGL .G2 K),
      ((glHom σ g : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = rootMat j ^ n →
        g ∈ H.map (adjointGroup .G2 K).subtype := fun j n g h => by
    refine ⟨rootElt σ j ^ n, hroot j n, glHom_injective σ (Units.ext ?_)⟩
    rw [h, Subgroup.coe_subtype, Subgroup.coe_pow, map_pow]
    change ((glHom σ ((glEquiv σ).symm (rootUnit j)) ^ n : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) = _
    rw [glHom_apply, MulEquiv.apply_symm_apply, Units.val_pow_eq_pow_val]
    rfl
  have hle : ∀ g ∈ adjointGroup .G2 K, g ∈ H.map (adjointGroup .G2 K).subtype := by
    intro g hg
    refine (Subgroup.closure_le (K := H.map (adjointGroup .G2 K).subtype)).mpr ?_ hg
    rintro g ⟨i, c, h | h⟩
    · refine hpow (xIdx i) (σ c).val g ?_
      rw [glHom_apply, coe_glEquiv, h, endEquiv_xOp, (XMat_eq_rootMat_pow i (σ c)).1]
    · refine hpow (yIdx i) (σ c).val g ?_
      rw [glHom_apply, coe_glEquiv, h, endEquiv_yOp, (XMat_eq_rootMat_pow i (σ c)).2]
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, hy, hyx⟩ := hle _ x.2
  rwa [show y = x from Subtype.ext hyx] at hy

section Presentation


theorem card_adjointGroup_G2_eq (hK : Nat.card K = 3) :
    Nat.card (adjointGroup .G2 K) = 4245696 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
  decide

theorem isPresentation (hK : Nat.card K = 3) :
    IsPresentation (gens σ) (wordSet rels) := by
  obtain ⟨hfin, hle⟩ := card_le
  exact IsPresentation.of_card_le (lift_gens_rels σ) (closure_range_gens σ)
    (hle.trans (by rw [card_adjointGroup_G2_eq hK]))

end Presentation

end CFSG.LieType.Multipliers.G23
