module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.AGLEmbedding.LieOut CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.SquareLinear CFSG.LieType.Steinberg

section Coord

variable {N : ℕ} {F : Type} [Field F] (S : Finset (Fin N))

theorem coordHom_transvection {x y : ↥S} (hxy : x ≠ y) (c : F) :
    coordHom (F := F) S (Matrix.SpecialLinearGroup.transvection hxy c) =
      Matrix.SpecialLinearGroup.transvection
        (show (x : Fin N) ≠ y from fun h => hxy (Subtype.ext h)) c := by
  apply Subtype.ext
  change coordMat S (Matrix.transvection x y c) = Matrix.transvection (x : Fin N) (y : Fin N) c
  ext a b
  obtain ⟨p, rfl⟩ := (coordEquiv S).surjective a
  obtain ⟨q, rfl⟩ := (coordEquiv S).surjective b
  rw [coordMat_apply]
  have hxS : (x : Fin N) ∈ S := x.2
  have hyS : (y : Fin N) ∈ S := y.2
  rcases p with x' | x' <;> rcases q with y' | y'
  · rw [Matrix.fromBlocks_apply₁₁, coordEquiv_inl, coordEquiv_inl]
    have h1 : ((x' : Fin N) = y') ↔ x' = y' := Subtype.ext_iff.symm
    have h2 : ((x : Fin N) = x') ↔ x = x' := Subtype.ext_iff.symm
    have h3 : ((y : Fin N) = y') ↔ y = y' := Subtype.ext_iff.symm
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      h1, h2, h3]
  · rw [Matrix.fromBlocks_apply₁₂, coordEquiv_inl, coordEquiv_inr]
    have hy' : (y' : Fin N) ∉ S := y'.2
    have h1 : (x' : Fin N) ≠ y' := fun h => hy' (h ▸ x'.2)
    have h2 : ¬ ((x : Fin N) = x' ∧ (y : Fin N) = y') := fun ⟨_, h⟩ => hy' (h ▸ hyS)
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      if_neg h1, if_neg h2, Matrix.zero_apply, add_zero]
  · rw [Matrix.fromBlocks_apply₂₁, coordEquiv_inr, coordEquiv_inl]
    have hx' : (x' : Fin N) ∉ S := x'.2
    have h1 : (x' : Fin N) ≠ y' := fun h => hx' (h ▸ y'.2)
    have h2 : ¬ ((x : Fin N) = x' ∧ (y : Fin N) = y') := fun ⟨h, _⟩ => hx' (h ▸ hxS)
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      if_neg h1, if_neg h2, Matrix.zero_apply, add_zero]
  · rw [Matrix.fromBlocks_apply₂₂, coordEquiv_inr, coordEquiv_inr]
    have hx' : (x' : Fin N) ∉ S := x'.2
    have h2 : ¬ ((x : Fin N) = x' ∧ (y : Fin N) = y') := fun ⟨h, _⟩ => hx' (h ▸ hxS)
    have h1 : ((x' : Fin N) = y') ↔ x' = y' := Subtype.ext_iff.symm
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, h1,
      h2, if_false, add_zero]

end Coord

section Blocks

open Classical

variable {m : ℕ} {F : Type} [Field F] (I : Set (Fin m))

@[expose] noncomputable def blkSet (p : Fin (m + 1)) : Finset (Fin (m + 1)) :=
  Finset.univ.filter fun q => SameBlk I p q

variable {I}

theorem mem_blkSet {p q : Fin (m + 1)} : q ∈ blkSet I p ↔ SameBlk I p q := by
  simp [blkSet]

theorem self_mem_blkSet (p : Fin (m + 1)) : p ∈ blkSet I p := mem_blkSet.mpr (SameBlk.refl I p)

theorem blkSet_eq_of_same {p q : Fin (m + 1)} (h : SameBlk I p q) : blkSet I p = blkSet I q := by
  ext r
  rw [mem_blkSet, mem_blkSet]
  exact ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩

theorem disjoint_blkSet {p q : Fin (m + 1)} (h : blkSet I p ≠ blkSet I q) :
    Disjoint (blkSet I p) (blkSet I q) := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  rw [mem_blkSet] at hr hr'
  exact h (blkSet_eq_of_same (hr.trans hr'.symm))

theorem transvection_mem_leviM {x y : Fin (m + 1)} (hxy : x ≠ y) (hs : SameBlk I x y) (c : F) :
    Matrix.SpecialLinearGroup.transvection hxy c ∈ leviM (rootDatum m F) I := by
  have hct := isCTGroupDatum m F
  rcases lt_or_gt_of_ne (fun h => hxy (Fin.ext h) : x.val ≠ y.val) with hlt | hgt
  · have hroot : rootVec x y ∈ (rootDatum m F).roots := by
      change rootVec x y ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A m) ∅
      rw [roots_eq]
      exact ⟨x, y, hxy, toStd_rootVec hlt⟩
    have hsupp : ∀ k ∉ I, rootVec x y k = 0 := by
      intro k hk
      simp only [rootVec]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      have := (hs k hk).mp h1
      omega
    have h2 : (rootDatum m F).rootGroup (rootVec x y) = rootSubgroup m F hxy :=
      rootGroup_eq m F hxy (toStd_rootVec hlt)
    have h3 := rootGroup_le_leviM hct hroot hsupp
    exact (le_of_eq_of_le h2.symm h3) (transvection_mem_rootSubgroup hxy c)
  · have hlt : y.val < x.val := hgt
    have hxy' : y ≠ x := hxy.symm
    have hstd : toStd m (-rootVec y x) = Pi.single x 1 - Pi.single y 1 := by
      rw [toStd_neg, toStd_rootVec hlt, neg_sub]
    have hroot : -rootVec y x ∈ (rootDatum m F).roots := by
      change -rootVec y x ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A m) ∅
      rw [roots_eq]
      exact ⟨x, y, hxy, hstd⟩
    have hsupp : ∀ k ∉ I, (-rootVec y x) k = 0 := by
      intro k hk
      simp only [rootVec, Pi.neg_apply]
      rw [if_neg]
      · simp
      rintro ⟨h1, h2⟩
      have := (hs k hk).mpr (by omega)
      omega
    have h2 : (rootDatum m F).rootGroup (-rootVec y x) = rootSubgroup m F hxy :=
      rootGroup_eq m F hxy hstd
    have h3 := rootGroup_le_leviM hct hroot hsupp
    exact (le_of_eq_of_le h2.symm h3) (transvection_mem_rootSubgroup hxy c)

theorem range_coordHom_le_leviM (p : Fin (m + 1)) :
    (coordHom (F := F) (blkSet I p)).range ≤ leviM (rootDatum m F) I := by
  rintro _ ⟨A, rfl⟩
  have hA : A ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct ↥(blkSet I p) F →
        Matrix.SpecialLinearGroup ↥(blkSet I p) F)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top _
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨u, v, huv, c⟩ := t
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, coordHom_transvection]
    have hsame : SameBlk I (u : Fin (m + 1)) v :=
      (mem_blkSet.mp u.2).symm.trans (mem_blkSet.mp v.2)
    exact transvection_mem_leviM _ hsame c
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

end Blocks

section Disjoint

variable {N : ℕ} {F : Type} [Field F]

theorem coordHom_apply_of_not_mem (S : Finset (Fin N)) (A : Matrix.SpecialLinearGroup ↥S F)
    {a b : Fin N} (hab : a ∉ S ∨ b ∉ S) :
    (coordHom (F := F) S A).1 a b = (1 : Matrix (Fin N) (Fin N) F) a b := by
  obtain ⟨p, rfl⟩ := (coordEquiv S).surjective a
  obtain ⟨q, rfl⟩ := (coordEquiv S).surjective b
  change coordMat S (A : Matrix ↥S ↥S F) (coordEquiv S p) (coordEquiv S q) = _
  rw [coordMat_apply]
  rcases p with x | x <;> rcases q with y | y
  · exfalso
    rcases hab with h | h
    · exact h x.2
    · exact h y.2
  · have hne : (x : Fin N) ≠ (y : Fin N) := fun h => y.2 (h ▸ x.2)
    rw [Matrix.fromBlocks_apply₁₂, coordEquiv_inl, coordEquiv_inr, Matrix.one_apply_ne hne]
    rfl
  · have hne : (x : Fin N) ≠ (y : Fin N) := fun h => x.2 (h ▸ y.2)
    rw [Matrix.fromBlocks_apply₂₁, coordEquiv_inr, coordEquiv_inl, Matrix.one_apply_ne hne]
    rfl
  · rw [Matrix.fromBlocks_apply₂₂, coordEquiv_inr, coordEquiv_inr]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [Matrix.one_apply_ne hxy, Matrix.one_apply_ne (fun h => hxy (Subtype.ext h))]

theorem coordHom_commute_of_disjoint {S S' : Finset (Fin N)} (hS : Disjoint S S')
    (A : Matrix.SpecialLinearGroup ↥S F) (A' : Matrix.SpecialLinearGroup ↥S' F) :
    coordHom (F := F) S A * coordHom (F := F) S' A' = coordHom (F := F) S' A' * coordHom (F := F) S A := by
  apply Subtype.ext
  set g : Matrix (Fin N) (Fin N) F := (coordHom (F := F) S A).1 with hg
  set h : Matrix (Fin N) (Fin N) F := (coordHom (F := F) S' A').1 with hh
  have hXY : (g - 1) * (h - 1) = 0 := by
    ext a b
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : (g - 1) a l = 0
    · simp [h1]
    · by_cases h2 : (h - 1) l b = 0
      · simp [h2]
      · exfalso
        have hl1 : l ∈ S := by
          by_contra hl
          exact h1 (by
            rw [Matrix.sub_apply, hg, coordHom_apply_of_not_mem S A (Or.inr hl), sub_self])
        have hl2 : l ∈ S' := by
          by_contra hl
          exact h2 (by
            rw [Matrix.sub_apply, hh, coordHom_apply_of_not_mem S' A' (Or.inl hl), sub_self])
        exact Finset.disjoint_left.mp hS hl1 hl2
  have hYX : (h - 1) * (g - 1) = 0 := by
    ext a b
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : (h - 1) a l = 0
    · simp [h1]
    · by_cases h2 : (g - 1) l b = 0
      · simp [h2]
      · exfalso
        have hl1 : l ∈ S' := by
          by_contra hl
          exact h1 (by
            rw [Matrix.sub_apply, hh, coordHom_apply_of_not_mem S' A' (Or.inr hl), sub_self])
        have hl2 : l ∈ S := by
          by_contra hl
          exact h2 (by
            rw [Matrix.sub_apply, hg, coordHom_apply_of_not_mem S A (Or.inl hl), sub_self])
        exact Finset.disjoint_left.mp hS hl2 hl1
  change g * h = h * g
  have e1 : g * h - h * g = (g - 1) * (h - 1) - (h - 1) * (g - 1) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    abel
  have := e1
  rw [hXY, hYX, sub_zero] at this
  exact sub_eq_zero.mp this

end Disjoint

section Torus

variable {m : ℕ} {F : Type} [Field F]

theorem exists_root_of_ne {x y : Fin (m + 1)} (hxy : x ≠ y) :
    ∃ γ ∈ (rootDatum m F).roots, (rootDatum m F).rootGroup γ = rootSubgroup m F hxy := by
  rcases lt_or_gt_of_ne (fun h => hxy (Fin.ext h) : x.val ≠ y.val) with hlt | hgt
  · refine ⟨rootVec x y, ?_, rootGroup_eq m F hxy (toStd_rootVec hlt)⟩
    change rootVec x y ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A m) ∅
    rw [roots_eq]
    exact ⟨x, y, hxy, toStd_rootVec hlt⟩
  · have hlt : y.val < x.val := hgt
    have hstd : toStd m (-rootVec y x) = Pi.single x 1 - Pi.single y 1 := by
      rw [toStd_neg, toStd_rootVec hlt, neg_sub]
    refine ⟨-rootVec y x, ?_, rootGroup_eq m F hxy hstd⟩
    change -rootVec y x ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A m) ∅
    rw [roots_eq]
    exact ⟨x, y, hxy, hstd⟩

theorem mem_normalizer_of_conj_le' {G : Type*} [Group G] {S : Subgroup G} {x : G}
    (h1 : ∀ h ∈ S, x * h * x⁻¹ ∈ S) (h2 : ∀ h ∈ S, x⁻¹ * h * x ∈ S) :
    x ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hx => ?_⟩
  simpa [mul_assoc] using h2 _ hx

theorem torus_le_normalizer_range (S : Finset (Fin (m + 1))) :
    (⨆ k, torus m F k) ≤ Subgroup.normalizer ((coordHom (F := F) S).range : Set _) := by
  have hct := isCTGroupDatum m F
  have key : ∀ t ∈ (⨆ k, torus m F k), ∀ g ∈ (coordHom (F := F) S).range,
      t * g * t⁻¹ ∈ (coordHom (F := F) S).range := by
    intro t ht
    rintro _ ⟨A, rfl⟩
    have hA : A ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct ↥S F → Matrix.SpecialLinearGroup ↥S F)) := by
      rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
      exact Subgroup.mem_top _
    induction hA using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨tv, rfl⟩ := hx
      obtain ⟨u, v, huv, c⟩ := tv
      rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, coordHom_transvection]
      have hne : (u : Fin (m + 1)) ≠ v := fun h => huv (Subtype.ext h)
      obtain ⟨γ, hγ, hγg⟩ := exists_root_of_ne (F := F) hne
      have hmem : Matrix.SpecialLinearGroup.transvection hne c ∈
          (rootDatum m F).rootGroup γ := by
        rw [hγg]; exact transvection_mem_rootSubgroup hne c
      have hconj := (Subgroup.mem_normalizer_iff.mp
        (iSup_le_normalizer_rootGroup hct hγ ht) _).mp hmem
      rw [hγg] at hconj
      obtain ⟨c', hc'⟩ := (mem_rootSubgroup hne _).mp hconj
      exact ⟨Matrix.SpecialLinearGroup.transvection huv c', by
        rw [coordHom_transvection]; exact hc'⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have : t * coordHom (F := F) S (x * y) * t⁻¹ =
          (t * coordHom (F := F) S x * t⁻¹) * (t * coordHom (F := F) S y * t⁻¹) := by
        rw [map_mul]; group
      rw [this]
      exact mul_mem hx hy
    | inv x _ hx =>
      have : t * coordHom (F := F) S x⁻¹ * t⁻¹ = (t * coordHom (F := F) S x * t⁻¹)⁻¹ := by
        rw [map_inv]; group
      rw [this]
      exact inv_mem hx
  intro t ht
  exact mem_normalizer_of_conj_le' (key t ht)
    (fun h hh => by simpa using key t⁻¹ (inv_mem ht) h hh)

end Torus

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
