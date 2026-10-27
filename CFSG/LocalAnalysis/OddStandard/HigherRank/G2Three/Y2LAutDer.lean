module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LAutLin
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2GL

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup Matrix CFSG.LocalAnalysis.SteinbergBV.ThreeInvolutions

variable {X : Type} [Group X] {M : Subgroup X}

theorem y2l_card_mulAut (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2))) :
    Nat.card (MulAut M) = 168 := by
  refine CFSG.OddStandard.ChengHeld.card_mulAut_elemAb8 ?_ fun v => eM.injective ?_
  · rw [Nat.card_congr eM.toEquiv, Nat.card_pi]
    simp
  · rw [map_mul, map_one]
    funext i
    have h : ∀ z : Multiplicative (ZMod 2), z * z = 1 := by decide
    rw [Pi.mul_apply, Pi.one_apply]
    exact h _

variable [M.Normal]

theorem y2l_ker_conjNormal (hC : centralizer (M : Set X) = M) :
    (MulAut.conjNormal : X →* MulAut M).ker = M := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 : x * m * x⁻¹ = m := by
      have := congrArg Subtype.val (DFunLike.congr_fun hx ⟨m, hm⟩)
      rwa [MulAut.conjNormal_apply] at this
    calc m * x = x * m * x⁻¹ * x := by rw [h1]
      _ = x * m := by group
  · intro hx
    have hx' : x ∈ centralizer (M : Set X) := by
      rw [hC]
      exact hx
    rw [Subgroup.mem_centralizer_iff] at hx'
    ext m
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← hx' m m.2]
    group

theorem y2l_range_conjNormal [Finite X] (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2)))
    (hC : centralizer (M : Set X) = M) (hidx : M.index = 168) :
    (MulAut.conjNormal : X →* MulAut M).range = ⊤ := by
  haveI : Finite (MulAut M) := Nat.finite_of_card_ne_zero (by rw [y2l_card_mulAut eM]; norm_num)
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, y2l_ker_conjNormal hC, hidx, y2l_card_mulAut eM]

theorem y2l_closure_gen (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2)))
    (hC : centralizer (M : Set X) = M) {x : Fin 2 → X}
    (hx : ∀ l, MulAut.conjNormal (x l) = y2l_psiAut eM (![T01, pGL] l)) :
    Subgroup.closure (Set.range x ∪ (M : Set X)) = ⊤ := by
  have hker : (MulAut.conjNormal : X →* MulAut M).ker ≤
      Subgroup.closure (Set.range x ∪ (M : Set X)) := by
    rw [y2l_ker_conjNormal hC]
    exact fun m hm => Subgroup.subset_closure (Or.inr hm)
  have hmap : Subgroup.map (MulAut.conjNormal : X →* MulAut M)
      (Subgroup.closure (Set.range x ∪ (M : Set X))) = ⊤ := by
    rw [eq_top_iff, ← y2l_closure_psiAut eM (y2l_card_mulAut eM), Subgroup.closure_le]
    intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl
    · exact ⟨x 0, Subgroup.subset_closure (Or.inl ⟨0, rfl⟩), hx 0⟩
    · exact ⟨x 1, Subgroup.subset_closure (Or.inl ⟨1, rfl⟩), hx 1⟩
  rw [← Subgroup.comap_map_eq_self hker, hmap, Subgroup.comap_top]

theorem y2l_mem_delta (hC : centralizer (M : Set X) = M) {β : MulAut X}
    (hβ : ∀ m ∈ M, β m = m) (x : X) : β x * x⁻¹ ∈ M := by
  rw [← hC, Subgroup.mem_centralizer_iff]
  intro m hm
  have h1 : x⁻¹ * m * x ∈ M := by
    have := ‹M.Normal›.conj_mem m hm x⁻¹
    rwa [inv_inv] at this
  have h2 := hβ _ h1
  rw [map_mul, map_mul, map_inv, hβ m hm] at h2
  calc m * (β x * x⁻¹) = β x * ((β x)⁻¹ * m * β x) * x⁻¹ := by group
    _ = β x * (x⁻¹ * m * x) * x⁻¹ := by rw [h2]
    _ = β x * x⁻¹ * m := by group

@[expose] def y2l_cocM (x : Fin 2 → X) (d : Fin 2 → M) : List (Fin 2) → M
  | [] => 1
  | l :: w => d l * MulAut.conjNormal (x l) (y2l_cocM x d w)

theorem y2l_prod_perturb (x : Fin 2 → X) (d : Fin 2 → M) (w : List (Fin 2)) :
    (w.map fun l => (d l : X) * x l).prod = (y2l_cocM x d w : X) * (w.map x).prod := by
  induction w with
  | nil => simp [y2l_cocM]
  | cons l w ih =>
    simp only [List.map_cons, List.prod_cons, ih, y2l_cocM, Subgroup.coe_mul,
      MulAut.conjNormal_apply]
    group

theorem y2l_toW_cocM (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2))) (x : Fin 2 → X)
    (d : Fin 2 → M) (g : Fin 2 → GL (Fin 3) (ZMod 2))
    (hx : ∀ l, MulAut.conjNormal (x l) = y2l_psiAut eM (g l)) (w : List (Fin 2)) :
    (y2l_toW eM (y2l_cocM x d w)).toAdd =
      y2l_coc (fun l => (g l : Matrix (Fin 3) (Fin 3) (ZMod 2)))
        (fun l => (y2l_toW eM (d l)).toAdd) w := by
  induction w with
  | nil => simp [y2l_cocM, y2l_coc]
  | cons l w ih => simp only [y2l_cocM, y2l_coc, map_mul, toAdd_mul, hx, y2l_toW_psiAut, ih]

theorem y2l_cocM_eq_one {β : MulAut X} (hβ : ∀ m ∈ M, β m = m) (x : Fin 2 → X) (d : Fin 2 → M)
    (hd : ∀ l, (d l : X) = β (x l) * (x l)⁻¹) (w : List (Fin 2)) (hw : (w.map x).prod ∈ M) :
    y2l_cocM x d w = 1 := by
  have h1 : β (w.map x).prod = (w.map fun l => (d l : X) * x l).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    simp [hd]
  rw [y2l_prod_perturb, hβ _ hw] at h1
  exact Subtype.ext (mul_right_cancel (h1.symm.trans (one_mul _).symm))

theorem y2l_card_fix_le [Finite X] (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2)))
    (hC : centralizer (M : Set X) = M) {x : Fin 2 → X}
    (hx : ∀ l, MulAut.conjNormal (x l) = y2l_psiAut eM (![T01, pGL] l)) :
    Nat.card (fixingSubgroup (MulAut X) (M : Set X)) ≤ 16 := by
  have hfix : ∀ β ∈ fixingSubgroup (MulAut X) (M : Set X), ∀ m ∈ M, β m = m :=
    fun β hβ m hm => (mem_fixingSubgroup_iff (MulAut X)).mp hβ m hm
  have hmem : ∀ w : List (Fin 2), (w.map ![T01, pGL]).prod = 1 → (w.map x).prod ∈ M := by
    intro w hw
    rw [← y2l_ker_conjNormal hC, MonoidHom.mem_ker, map_list_prod, List.map_map]
    have : (⇑(MulAut.conjNormal : X →* MulAut M) ∘ x) = ⇑(y2l_psiAut eM) ∘ ![T01, pGL] :=
      funext hx
    rw [this, ← List.map_map, ← map_list_prod, hw, map_one]
  have hsq : ([0, 0].map x).prod ∈ M := hmem _ (by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero]
    exact y2l_T01_sq)
  have hcube : ([1, 1, 1].map x).prod ∈ M := hmem _ (by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_one, Matrix.head_cons]
    rw [← mul_assoc]
    exact y2l_pGL_cube)
  let δ : fixingSubgroup (MulAut X) (M : Set X) → Fin 2 → M := fun β l =>
    ⟨β.1 (x l) * (x l)⁻¹, y2l_mem_delta hC (hfix β.1 β.2) (x l)⟩
  have hδ : ∀ β l, ((δ β l : M) : X) = β.1 (x l) * (x l)⁻¹ := fun _ _ => rfl
  have hcoc : ∀ β, ∀ w : List (Fin 2), (w.map x).prod ∈ M →
      y2l_coc ![t01, pMat] ![(y2l_toW eM (δ β 0)).toAdd, (y2l_toW eM (δ β 1)).toAdd] w = 0 := by
    intro β w hw
    have hA : ![t01, pMat] =
        fun l => ((![T01, pGL] l : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      funext l
      fin_cases l <;> rfl
    have hd : ![(y2l_toW eM (δ β 0)).toAdd, (y2l_toW eM (δ β 1)).toAdd] =
        fun l => (y2l_toW eM (δ β l)).toAdd := by
      funext l
      fin_cases l <;> rfl
    rw [hA, hd, ← y2l_toW_cocM eM x (δ β) ![T01, pGL] hx w,
      y2l_cocM_eq_one (hfix β.1 β.2) x (δ β) (hδ β) w hw, map_one, toAdd_one]
  let f : fixingSubgroup (MulAut X) (M : Set X) → y2l_cocSet := fun β =>
    ⟨((y2l_toW eM (δ β 0)).toAdd, (y2l_toW eM (δ β 1)).toAdd),
      y2l_mem_cocSet.mpr ⟨hcoc β _ hsq, hcoc β _ hcube⟩⟩
  have hf : Function.Injective f := by
    intro β₁ β₂ h
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
    have he : ∀ l, β₁.1 (x l) = β₂.1 (x l) := by
      intro l
      have hl : δ β₁ l = δ β₂ l := by
        apply (y2l_toW eM).injective
        apply Multiplicative.toAdd.injective
        fin_cases l
        · exact h.1
        · exact h.2
      have h' := congrArg Subtype.val hl
      rw [hδ, hδ] at h'
      exact mul_right_cancel h'
    have hEq : β₁.1.toMonoidHom = β₂.1.toMonoidHom :=
      MonoidHom.eq_of_eqOn_dense (y2l_closure_gen eM hC hx) (by
        rintro z (⟨l, rfl⟩ | hz)
        · exact he l
        · exact (hfix β₁.1 β₁.2 z hz).trans (hfix β₂.1 β₂.2 z hz).symm)
    exact Subtype.ext (MulEquiv.ext fun y => DFunLike.congr_fun hEq y)
  calc Nat.card (fixingSubgroup (MulAut X) (M : Set X)) ≤ Nat.card y2l_cocSet :=
        Nat.card_le_card_of_injective f hf
    _ = 16 := by rw [Nat.card_eq_finsetCard, y2l_card_cocSet]

end CFSG.OddStandard.HigherRank.G2Three.Sec2
