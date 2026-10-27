module

public import CFSG.LargeExtraspecial.A2ModCfgSL
public import CFSG.LargeExtraspecial.A2ModGrid

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions

variable {k : ℕ}

theorem single_ne_single {i j : Fin k} (hij : i ≠ j) :
    (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) ≠ Pi.single j 1 := by
  intro h
  have := congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact one_ne_zero this

theorem linearIndependent_single_pair {i j : Fin k} (hij : i ≠ j) :
    LinearIndependent (ZMod 2) ![(Pi.single i (1 : ZMod 2) : Fin k → ZMod 2), Pi.single j 1] :=
  Grid.linearIndependent_pair_iff.mpr ⟨Pi.single_ne_zero_iff.mpr one_ne_zero,
    Pi.single_ne_zero_iff.mpr one_ne_zero, single_ne_single hij⟩

theorem exists_pair_coordSpace {S : Set (Fin k)} {i j : Fin k} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) : ∃ x ∈ coordSpace S, ∃ y ∈ coordSpace S, LinearIndependent (ZMod 2) ![x, y] :=
  ⟨_, single_mem_coordSpace hi, _, single_mem_coordSpace hj, linearIndependent_single_pair hij⟩

theorem span_single_le_coordSpace {S : Set (Fin k)} {i : Fin k} (hi : i ∈ S) :
    (ZMod 2) ∙ (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) ≤ coordSpace S :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr (single_mem_coordSpace hi)

theorem fin_ne_of_val_ne {i j : Fin k} (h : i.val ≠ j.val) : i ≠ j := fun e => h (e ▸ rfl)

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem A2Action.inf_commSpace_ne_bot (hA : A2Action D Q ρ) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (hde : d * e ∈ D) : commSpace (ρ d) ⊓ commSpace (ρ e) ≠ ⊥ := by
  obtain ⟨-, h1, -⟩ := hA.third_line hd he hde
  exact Submodule.one_le_finrank_iff.mp h1.ge

omit [FiniteDimensional (ZMod 2) V] in
theorem IsPointMaps.inf_span_ne_bot_of_node {Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X}
    {P Pd : (Fin k → ZMod 2) →ₗ[ZMod 2] V} (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) {a : X}
    {i j : Fin k} (hij : i ≠ j) {S₁ S₂ : Set (Fin k)} (hi₁ : i ∉ S₁) (hj₁ : j ∉ S₁)
    (hi₂ : i ∉ S₂) (hj₂ : j ∉ S₂) (hS : Disjoint S₁ S₂)
    (h₁ : ∀ l ∈ S₁, Commute a (Ψ (elemTv l i))) (h₂ : ∀ l ∈ S₂, Commute a (Ψ (elemTv j l)))
    (hmeet : commSpace (ρ a) ⊓ commSpace (ρ (Ψ (elemTv i j))) ≠ ⊥) {w ψ : Fin k → ZMod 2}
    (hw : w ∈ coordSpace S₁) (hψ : ψ ∈ coordSpace S₂) :
    commSpace (ρ a) ⊓
      Submodule.span (ZMod 2) {P (Pi.single i 1 + w), Pd (Pi.single j 1 + ψ)} ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hmeet
  rw [Submodule.mem_inf] at hx
  set u := tv w (Pi.single i 1) * tv (Pi.single j 1) ψ with hu_def
  have hu : Commute a (Ψ u) := by
    rw [hu_def, map_mul]
    exact (commute_tv_left_of_mem_coordSpace Ψ hi₁ h₁ hw).mul_right
      (commute_tv_right_of_mem_coordSpace Ψ hj₂ h₂ hψ)
  have hconj := conj_elemTv_eq hi₁ hj₁ hi₂ hj₂ hS hw hψ
  have h1 : ρ (Ψ u) x ∈ commSpace (ρ a) := by
    have := apply_mem_commSpace_conj ρ (Ψ u) hx.1
    rwa [← hu.eq, mul_inv_cancel_right] at this
  have h2 : ρ (Ψ u) x ∈ commSpace (ρ (Ψ (tv (Pi.single i 1 + w) (Pi.single j 1 + ψ)))) := by
    have := apply_mem_commSpace_conj ρ (Ψ u) hx.2
    rwa [← map_inv, ← map_mul, ← map_mul, hconj] at this
  have hinc : (Pi.single j (1 : ZMod 2) + ψ) ⬝ᵥ (Pi.single i 1 + w) = 0 := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, single_dotProduct_single_of_ne hij,
      single_dotProduct_eq_zero_of_mem_coordSpace hw hj₁,
      dotProduct_single_eq_zero_of_mem_coordSpace hψ hi₂,
      dotProduct_eq_zero_of_mem_coordSpace hS hψ hw, add_zero, add_zero]
  have hline := hP.commSpace_tv _ _ (single_add_ne_zero_of_mem_coordSpace hw hi₁)
    (single_add_ne_zero_of_mem_coordSpace hψ hj₂) hinc
  rw [MonoidHom.comp_apply] at hline
  rw [hline] at h2
  exact (Submodule.ne_bot_iff _).mpr ⟨ρ (Ψ u) x, Submodule.mem_inf.mpr ⟨h1, h2⟩,
    fun h => hx0 ((LinearEquiv.map_eq_zero_iff _).mp h)⟩

structure IsLeviNode (D : Set X) (Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X) (a b : X) :
    Prop where
  map_mem : ∀ g ∈ transvectionSet k (ZMod 2), Ψ g ∈ D
  mem_left : a ∈ D
  mem_right : b ∈ D
  commute_left : ∀ i j : Fin k, j.val + 1 = i.val → Commute a (Ψ (elemTv i j))
  commute_right : ∀ i j : Fin k, i.val + 1 = j.val → Commute b (Ψ (elemTv i j))
  mul_mem_left : ∀ i j : Fin k, i.val + 2 = k → j.val + 3 = k → a * Ψ (elemTv i j) ∈ D
  mul_mem_right : ∀ i j : Fin k, i.val + 3 = k → j.val + 2 = k → b * Ψ (elemTv i j) ∈ D

namespace IsLeviNode

variable {Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X} {a b : X}
  {P Pd : (Fin k → ZMod 2) →ₗ[ZMod 2] V}

theorem meet_left (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b)
    (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) {i₂ i₃ : Fin k} (hi₂ : i₂.val + 2 = k)
    (hi₃ : i₃.val + 3 = k) {w ψ : Fin k → ZMod 2} (hw : w ∈ coordSpace {l | i₂ < l})
    (hψ : ψ ∈ coordSpace {l | l < i₃}) :
    commSpace (ρ a) ⊓
      Submodule.span (ZMod 2) {P (Pi.single i₂ 1 + w), Pd (Pi.single i₃ 1 + ψ)} ≠ ⊥ := by
  have h23 : i₂ ≠ i₃ := fin_ne_of_val_ne (by omega)
  have hlow := commute_elemTv_of_lt Ψ h.commute_left
  have hE := h.map_mem _ (elemTv_mem_transvectionSet h23)
  refine hP.inf_span_ne_bot_of_node h23 (S₁ := {l | i₂ < l}) (S₂ := {l | l < i₃})
    (by simp) (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega)
    (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega) (by simp)
    (Set.disjoint_left.mpr fun l h1 h2 => by
      simp only [Set.mem_ofPred_eq, Fin.lt_def] at h1 h2; omega)
    (fun l hl => hlow l i₂ hl) (fun l hl => hlow i₃ l hl)
    (hA.inf_commSpace_ne_bot h.mem_left hE (h.mul_mem_left i₂ i₃ hi₂ hi₃)) hw hψ

theorem meet_right (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b)
    (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) {i₂ i₃ : Fin k} (hi₂ : i₂.val + 2 = k)
    (hi₃ : i₃.val + 3 = k) {w ψ : Fin k → ZMod 2} (hw : w ∈ coordSpace {l | l < i₃})
    (hψ : ψ ∈ coordSpace {l | i₂ < l}) :
    commSpace (ρ b) ⊓
      Submodule.span (ZMod 2) {P (Pi.single i₃ 1 + w), Pd (Pi.single i₂ 1 + ψ)} ≠ ⊥ := by
  have h32 : i₃ ≠ i₂ := fin_ne_of_val_ne (by omega)
  have hup := commute_elemTv_of_lt' Ψ h.commute_right
  have hE := h.map_mem _ (elemTv_mem_transvectionSet h32)
  refine hP.inf_span_ne_bot_of_node h32 (S₁ := {l | l < i₃}) (S₂ := {l | i₂ < l})
    (by simp) (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega)
    (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega) (by simp)
    (Set.disjoint_left.mpr fun l h1 h2 => by
      simp only [Set.mem_ofPred_eq, Fin.lt_def] at h1 h2; omega)
    (fun l hl => hup l i₃ hl) (fun l hl => hup i₂ l hl)
    (hA.inf_commSpace_ne_bot h.mem_right hE (h.mul_mem_right i₃ i₂ hi₃ hi₂)) hw hψ

theorem commSpace_left_le (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b) (hk : 5 ≤ k)
    (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) : commSpace (ρ a) ≤ LinearMap.range P := by
  obtain ⟨i₁, hi₁⟩ : ∃ i : Fin k, i.val + 1 = k := ⟨⟨k - 1, by omega⟩, by simp; omega⟩
  obtain ⟨i₂, hi₂⟩ : ∃ i : Fin k, i.val + 2 = k := ⟨⟨k - 2, by omega⟩, by simp; omega⟩
  obtain ⟨i₃, hi₃⟩ : ∃ i : Fin k, i.val + 3 = k := ⟨⟨k - 3, by omega⟩, by simp; omega⟩
  have h₁ : i₁ ∈ {l : Fin k | i₂ < l} := by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega
  have heq := eq_span_of_forall_meet_grid_left hP.injective hP.injective_dual
    hP.range_inf_range (hA.isTypeA h.mem_left).2.2.2.1
    (linearIndependent_single_pair (fin_ne_of_val_ne (i := i₂) (j := i₁) (by omega)))
    (exists_pair_coordSpace (S := {l : Fin k | l < i₃}) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega) (fin_ne_of_val_ne (by simp)))
    (Pi.single i₃ 1) fun w hw ψ hψ =>
      h.meet_left hA hP hi₂ hi₃ (span_single_le_coordSpace h₁ hw) hψ
  rw [heq, Submodule.span_le]
  rintro x (rfl | rfl) <;> exact LinearMap.mem_range_self P _

theorem commSpace_right_le (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b) (hk : 5 ≤ k)
    (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) : commSpace (ρ b) ≤ LinearMap.range Pd := by
  obtain ⟨i₁, hi₁⟩ : ∃ i : Fin k, i.val + 1 = k := ⟨⟨k - 1, by omega⟩, by simp; omega⟩
  obtain ⟨i₂, hi₂⟩ : ∃ i : Fin k, i.val + 2 = k := ⟨⟨k - 2, by omega⟩, by simp; omega⟩
  obtain ⟨i₃, hi₃⟩ : ∃ i : Fin k, i.val + 3 = k := ⟨⟨k - 3, by omega⟩, by simp; omega⟩
  have h₁ : i₁ ∈ {l : Fin k | i₂ < l} := by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega
  have heq := eq_span_of_forall_meet_grid_right hP.injective hP.injective_dual
    hP.range_inf_range (hA.isTypeA h.mem_right).2.2.2.1
    (linearIndependent_single_pair (fin_ne_of_val_ne (i := i₂) (j := i₁) (by omega)))
    (exists_pair_coordSpace (S := {l : Fin k | l < i₃}) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega) (fin_ne_of_val_ne (by simp)))
    (Pi.single i₃ 1) fun w hw ψ hψ =>
      h.meet_right hA hP hi₂ hi₃ hw (span_single_le_coordSpace h₁ hψ)
  rw [heq, Submodule.span_le]
  rintro x (rfl | rfl) <;> exact LinearMap.mem_range_self Pd _

theorem commSpace_left_le_sup (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b) (hk : k = 4)
    (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) :
    commSpace (ρ a) ≤ LinearMap.range P ⊔ LinearMap.range Pd := by
  subst hk
  exact le_sup_range_of_forall_meet_grid hP.injective hP.injective_dual hP.range_inf_range
    (hA.isTypeA h.mem_left).2.2.2.1 (linearIndependent_single_pair (i := 2) (j := 3) (by decide))
    (linearIndependent_single_pair (i := 1) (j := 0) (by decide)) fun w hw ψ hψ =>
      h.meet_left hA hP (i₂ := 2) (i₃ := 1) rfl rfl
        (span_single_le_coordSpace (S := {l : Fin 4 | 2 < l}) (by decide) hw)
        (span_single_le_coordSpace (S := {l : Fin 4 | l < 1}) (by decide) hψ)

theorem commSpace_right_le_sup (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b) (hk : k = 4)
    (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) :
    commSpace (ρ b) ≤ LinearMap.range P ⊔ LinearMap.range Pd := by
  subst hk
  exact le_sup_range_of_forall_meet_grid hP.injective hP.injective_dual hP.range_inf_range
    (hA.isTypeA h.mem_right).2.2.2.1 (linearIndependent_single_pair (i := 1) (j := 0) (by decide))
    (linearIndependent_single_pair (i := 2) (j := 3) (by decide)) fun w hw ψ hψ =>
      h.meet_right hA hP (i₂ := 2) (i₃ := 1) rfl rfl
        (span_single_le_coordSpace (S := {l : Fin 4 | l < 1}) (by decide) hw)
        (span_single_le_coordSpace (S := {l : Fin 4 | 2 < l}) (by decide) hψ)

theorem exists_isPointMaps_commSpaceOf_eq (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b)
    (hk : 5 ≤ k) :
    ∃ P Pd : (Fin k → ZMod 2) →ₗ[ZMod 2] V, IsPointMaps (ρ.comp Ψ) Q P Pd ∧
      commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b) =
        LinearMap.range P ⊔ LinearMap.range Pd := by
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) h.map_mem
  obtain ⟨P, Pd, hP⟩ := exists_isPointMaps hA' hk
  refine ⟨P, Pd, hP, ?_⟩
  rw [commSpaceOf_sup_zpowers, commSpaceOf_sup_zpowers, commSpaceOf_range, hP.commSpaceOf_top]
  exact le_antisymm (sup_le (sup_le le_rfl ((h.commSpace_left_le hA hk hP).trans le_sup_left))
    ((h.commSpace_right_le hA hk hP).trans le_sup_right)) (le_sup_left.trans le_sup_left)

theorem finrank_commSpaceOf_eq (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b) (hk : 5 ≤ k) :
    finrank (ZMod 2) (commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b)) =
      2 * k := by
  obtain ⟨P, Pd, hP, heq⟩ := h.exists_isPointMaps_commSpaceOf_eq hA hk
  rw [heq, finrank_range_sup_range_eq hP.injective hP.injective_dual hP.range_inf_range]

theorem commSpaceOf_eq_of_isPointMaps (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b)
    (hk : k = 4) (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) :
    commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b) =
      LinearMap.range P ⊔ LinearMap.range Pd := by
  rw [commSpaceOf_sup_zpowers, commSpaceOf_sup_zpowers, commSpaceOf_range, hP.commSpaceOf_top]
  exact le_antisymm (sup_le (sup_le le_rfl (h.commSpace_left_le_sup hA hk hP))
    (h.commSpace_right_le_sup hA hk hP)) (le_sup_left.trans le_sup_left)

theorem finrank_commSpaceOf_le_add (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b)
    (hk : 4 ≤ k) :
    finrank (ZMod 2) (commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤
      finrank (ZMod 2) (commSpaceOf ρ Ψ.range) + 2 := by
  obtain ⟨i₂, hi₂⟩ : ∃ i : Fin k, i.val + 2 = k := ⟨⟨k - 2, by omega⟩, by simp; omega⟩
  obtain ⟨i₃, hi₃⟩ : ∃ i : Fin k, i.val + 3 = k := ⟨⟨k - 3, by omega⟩, by simp; omega⟩
  have h23 : i₂ ≠ i₃ := fin_ne_of_val_ne (by omega)
  have h1 := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear (H := Ψ.range) h.mem_left
    (h.map_mem _ (elemTv_mem_transvectionSet h23)) ⟨_, rfl⟩ (h.mul_mem_left i₂ i₃ hi₂ hi₃)
  have h2 := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear
    (H := Ψ.range ⊔ Subgroup.zpowers a) h.mem_right
    (h.map_mem _ (elemTv_mem_transvectionSet h23.symm)) (Subgroup.mem_sup_left ⟨_, rfl⟩)
    (h.mul_mem_right i₃ i₂ hi₃ hi₂)
  omega

theorem finrank_commSpaceOf_le (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b) (hk : k = 4) :
    finrank (ZMod 2) (commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤
      9 := by
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) h.map_mem
  rcases exists_isPointMaps_or_finrank_le hA' (by omega) with ⟨P, Pd, hP⟩ | hle
  · rw [h.commSpaceOf_eq_of_isPointMaps hA hk hP,
      finrank_range_sup_range_eq hP.injective hP.injective_dual hP.range_inf_range]
    omega
  · have h1 := h.finrank_commSpaceOf_le_add hA (by omega)
    rw [commSpaceOf_range] at h1
    omega

end IsLeviNode

theorem false_of_node (hA : A2Action D Q ρ) {Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X}
    (hΨ : ∀ g ∈ transvectionSet k (ZMod 2), Ψ g ∈ D) {e : X} (he : e ∈ D)
    (hcomm : ∀ i j : Fin k, j.val + 1 = i.val → Commute e (Ψ (elemTv i j))) {i j : Fin k}
    (hji : j.val + 1 = i.val) (hj : 2 ≤ j.val) (hi : i.val + 3 ≤ k)
    (hcoll : e * Ψ (elemTv i j) ∈ D) : False := by
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) hΨ
  obtain ⟨P, Pd, hP⟩ := exists_isPointMaps hA' (by omega)
  have hij : i ≠ j := fin_ne_of_val_ne (by omega)
  have hlow := commute_elemTv_of_lt Ψ hcomm
  refine false_of_forall_meet_grid hP.injective hP.injective_dual hP.range_inf_range
    (hA.isTypeA he).2.2.2.1 (W₁ := coordSpace {l | i < l}) (W₂ := coordSpace {l | l < j})
    (exists_pair_coordSpace (i := ⟨i.val + 1, by omega⟩) (j := ⟨i.val + 2, by omega⟩)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega) (fin_ne_of_val_ne (by simp)))
    (exists_pair_coordSpace (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega)
      (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega) (fin_ne_of_val_ne (by simp)))
    (Pi.single i 1) (Pi.single j 1) fun w hw ψ hψ => ?_
  exact hP.inf_span_ne_bot_of_node hij (S₁ := {l | i < l}) (S₂ := {l | l < j}) (by simp)
    (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega)
    (by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega) (by simp)
    (Set.disjoint_left.mpr fun l h1 h2 => by
      simp only [Set.mem_ofPred_eq, Fin.lt_def] at h1 h2; omega)
    (fun l hl => hlow l i hl) (fun l hl => hlow j l hl)
    (hA.inf_commSpace_ne_bot he (hΨ _ (elemTv_mem_transvectionSet hij)) hcoll) hw hψ

end CFSG.LargeExtraspecial.A2Mod
