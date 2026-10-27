module

public import CFSG.HardMathSupport.Dickson.BMRows.M13L33Base

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.M13L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33

@[expose] def genL (k : ℕ) : Equiv.Perm (Fin 13) :=
  if k = 0 then pa else if k = 1 then pb else pb⁻¹

@[expose] def wordPerm (w : List ℕ) : Equiv.Perm (Fin 13) := (w.map genL).prod

@[expose] def centWords : List (List ℕ) :=
  [[], [0], [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1], [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2],
    [2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1], [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2],
    [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1], [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2],
    [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1], [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2],
    [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1],
    [1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1],
    [2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2],
    [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2],
    [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1],
    [0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1],
    [0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2],
    [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2],
    [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2],
    [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1],
    [2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1],
    [2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2],
    [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1],
    [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2],
    [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2],
    [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2],
    [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1],
    [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1],
    [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2],
    [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2],
    [0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2],
    [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2],
    [1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1],
    [1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    [1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2]]

@[expose] def centPerms : List (Equiv.Perm (Fin 13)) := centWords.map wordPerm

@[expose] def tabA : List (Fin 13) := [12, 1, 2, 11, 7, 5, 10, 4, 8, 9, 6, 3, 0]

@[expose] def tabB : List (Fin 13) := [11, 12, 10, 3, 0, 6, 8, 2, 5, 1, 7, 4, 9]

@[expose] def tabC : List (Fin 13) := [4, 9, 7, 3, 11, 8, 5, 10, 6, 12, 2, 0, 1]

@[expose] def genTab (k : ℕ) (i : Fin 13) : Fin 13 :=
  (if k = 0 then tabA else if k = 1 then tabB else tabC).getD i.val 0

@[expose] def evalTab (w : List ℕ) (i : Fin 13) : Fin 13 := w.foldr genTab i

@[expose] def wordTab (w : List ℕ) : List (Fin 13) := (List.finRange 13).map (evalTab w)

theorem pa_apply : ∀ i : Fin 13, pa i = tabA.getD i.val 0 := by decide +kernel

theorem pb_apply : ∀ i : Fin 13, pb i = tabB.getD i.val 0 := by decide +kernel

theorem pbi_apply : ∀ i : Fin 13, pb⁻¹ i = tabC.getD i.val 0 := by decide +kernel

theorem genL_apply (k : ℕ) (i : Fin 13) : genL k i = genTab k i := by
  unfold genL genTab
  split_ifs
  · exact pa_apply i
  · exact pb_apply i
  · exact pbi_apply i

theorem wordPerm_apply (w : List ℕ) (i : Fin 13) : wordPerm w i = evalTab w i := by
  induction w generalizing i with
  | nil => rfl
  | cons k w ih =>
    have h1 : wordPerm (k :: w) = genL k * wordPerm w := by simp [wordPerm]
    rw [h1, Equiv.Perm.mul_apply, ih, genL_apply]
    rfl

theorem pa_sq : pa * pa = 1 := by decide +kernel

theorem pa_ne_one : pa ≠ 1 := by decide +kernel

theorem centPerms_length : centPerms.length = 48 := by decide +kernel

theorem centTabs_nodup : (centWords.map wordTab).Nodup := by decide +kernel

theorem centTabs_comm :
    ∀ w ∈ centWords, ∀ i : Fin 13,
      evalTab w (tabA.getD i.val 0) = tabA.getD (evalTab w i).val 0 := by decide +kernel

@[expose] def permTab (σ : Equiv.Perm (Fin 13)) : List (Fin 13) :=
  (List.finRange 13).map fun i => σ i

theorem centPerms_nodup : centPerms.Nodup := by
  have h : (centPerms.map permTab).Nodup := by
    have : centPerms.map permTab = centWords.map wordTab := by
      simp only [centPerms, List.map_map]
      refine List.map_congr_left fun w _ => ?_
      simp only [Function.comp, wordTab, permTab]
      exact List.map_congr_left fun i _ => wordPerm_apply w i
    rw [this]
    exact centTabs_nodup
  exact List.Nodup.of_map _ h

theorem centPerms_comm : ∀ g ∈ centPerms, g * pa = pa * g := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  ext i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, wordPerm_apply, pa_apply, wordPerm_apply,
    pa_apply, centTabs_comm w hw i]

theorem wordPerm_mem (w : List ℕ) : wordPerm w ∈ QP13.originalSubgroup := by
  rw [QP13_closure]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  unfold genL
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem pa_mem : pa ∈ QP13.originalSubgroup := by
  rw [QP13_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem pb_mem : pb ∈ QP13.originalSubgroup := by
  rw [QP13_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem pa_pb_noncomm :
    (⟨pa, pa_mem⟩ : ↥QP13.originalSubgroup) * ⟨pb, pb_mem⟩ ≠ ⟨pb, pb_mem⟩ * ⟨pa, pa_mem⟩ := by
  decide +kernel

@[expose] def GoodL33 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))

@[expose] def TrivRk (_T : Type) [Group _T] : Prop := True

theorem GoodL33.of_equiv {T T' : Type} [Group T] [Group T'] (f : T ≃* T') (h : GoodL33 T) :
    GoodL33 T' := by
  obtain ⟨g⟩ := h
  exact ⟨f.symm.trans g⟩

section Iso


theorem nonempty_equiv_p13 {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
    Nonempty (K ≃* QP13.originalSubgroup) := by
  obtain ⟨e2⟩ := equiv_psl_P13
  exact ⟨(e.trans slEquivPsl).trans e2⟩

theorem card_of_equiv_sl {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) : Nat.card K = 5616 := by
  obtain ⟨ε⟩ := nonempty_equiv_p13 e
  rw [Nat.card_congr ε.toEquiv, card_group QP13 QP13_ok, QP13_valid.2]

theorem isSimple_of_equiv_sl {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) : IsSimpleGroup K := by
  have hlin := CFSG.LinearGroups.linear_projective_simple (K := ZMod 3) (n := 3)
    (by norm_num) (Or.inl (by norm_num))
  exact (MulEquiv.isSimpleGroup_congr (e.trans slEquivPsl)).mpr hlin.2.1

theorem noncomm_of_equiv_sl {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) : ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨ε⟩ := nonempty_equiv_p13 e
  refine ⟨ε.symm ⟨pa, pa_mem⟩, ε.symm ⟨pb, pb_mem⟩, fun h => pa_pb_noncomm ?_⟩
  have h' := congrArg ε h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  exact h'

theorem card_mulAut_of_equiv_sl {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) : Nat.card (MulAut K) = 11232 := by
  obtain ⟨ε⟩ := nonempty_equiv_p13 e
  obtain ⟨e3⟩ := equiv_P13_P
  exact card_mulAut (ε.trans e3)

theorem exists_involution_cent_ge {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
    ∃ u : K, u * u = 1 ∧ u ≠ 1 ∧ 48 ≤ Nat.card ↥(Subgroup.centralizer ({u} : Set K)) := by
  obtain ⟨e2⟩ := equiv_psl_P13
  let ε : K ≃* QP13.originalSubgroup := (e.trans slEquivPsl).trans e2
  haveI : Finite K := Finite.of_equiv _ ε.symm.toEquiv
  let ua : QP13.originalSubgroup := ⟨pa, pa_mem⟩
  have hmem : ∀ i : Fin centPerms.length, centPerms.get i ∈ QP13.originalSubgroup := by
    intro i
    obtain ⟨w, -, hw⟩ := List.mem_map.1 (List.get_mem centPerms i)
    rw [← hw]
    exact wordPerm_mem w
  have hcomm : ∀ i : Fin centPerms.length,
      ε.symm ⟨centPerms.get i, hmem i⟩ ∈ Subgroup.centralizer ({ε.symm ua} : Set K) := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (centPerms_comm _ (List.get_mem centPerms i))
  refine ⟨ε.symm ua, ?_, ?_, ?_⟩
  · rw [← map_mul]
    have : ua * ua = 1 := Subtype.ext pa_sq
    rw [this, map_one]
  · intro h
    have : ua = 1 := by simpa using congrArg ε h
    exact pa_ne_one (congrArg Subtype.val this)
  · have hlen : Nat.card (Fin centPerms.length) = 48 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, centPerms_length]
    rw [← hlen]
    refine Nat.card_le_card_of_injective
      (fun i : Fin centPerms.length =>
        (⟨ε.symm ⟨centPerms.get i, hmem i⟩, hcomm i⟩ :
          ↥(Subgroup.centralizer ({ε.symm ua} : Set K)))) ?_
    intro i j hij
    have h1 := ε.symm.injective (Subtype.ext_iff.1 hij)
    have h2 : centPerms.get i = centPerms.get j := congrArg Subtype.val h1
    exact centPerms_nodup.get_inj_iff.1 h2

end Iso

end CFSG.HardMathSupport.Dickson.BMRows.M13L33
