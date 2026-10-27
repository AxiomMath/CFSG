module

public import CFSG.CharacterTheory.Semidihedral.Presentation

public section

namespace CFSG.Semidihedral

open CFSG.Open

instance model_finite (n : ℕ) (hn : 3 ≤ n) : Finite (Model n hn) :=
  Finite.of_equiv (Cyclic (modulus n) × Cyclic 2) SemidirectProduct.equivProd.symm

theorem presentation_finite (n : ℕ) (hn : 3 ≤ n) : Finite (SemidihedralGroup n) :=
  Finite.of_equiv (Model n hn) (presentationEquivModel n hn).symm.toEquiv

@[expose] def coordinateEquiv (n : ℕ) (hn : 3 ≤ n) :
    SemidihedralGroup n ≃ ZMod (modulus n) × ZMod 2 :=
  (presentationEquivModel n hn).toEquiv.trans
    (SemidirectProduct.equivProd.trans (Multiplicative.toAdd.prodCongr Multiplicative.toAdd))

@[expose] def element (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) (e : ZMod 2) :
    SemidihedralGroup n := (coordinateEquiv n hn).symm (i, e)

@[simp] theorem coordinateEquiv_element (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    coordinateEquiv n hn (element n hn i e) = (i, e) :=
  (coordinateEquiv n hn).apply_symm_apply _

theorem element_eq (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) (e : ZMod 2) :
    element n hn i e = r n ^ i.val * s n ^ e.val := rfl

@[simp] theorem coordinateEquiv_r (n : ℕ) (hn : 3 ≤ n) :
    coordinateEquiv n hn (r n) = (1, 0) := by
  change ((presentationEquivModel n hn (r n)).left.toAdd,
    (presentationEquivModel n hn (r n)).right.toAdd) = (1, 0)
  rw [presentationEquivModel_r]
  rfl

@[simp] theorem coordinateEquiv_s (n : ℕ) (hn : 3 ≤ n) :
    coordinateEquiv n hn (s n) = (0, 1) := by
  change ((presentationEquivModel n hn (s n)).left.toAdd,
    (presentationEquivModel n hn (s n)).right.toAdd) = (0, 1)
  rw [presentationEquivModel_s]
  rfl

@[expose] def boundedCoordinateEquiv (n : ℕ) (hn : 3 ≤ n) :
    SemidihedralGroup n ≃ Fin (modulus n) × Fin 2 :=
  (coordinateEquiv n hn).trans
    ((ZMod.finEquiv (modulus n)).symm.toEquiv.prodCongr (ZMod.finEquiv 2).symm.toEquiv)

theorem val_finEquiv (d : ℕ) [NeZero d] (i : Fin d) :
    ((ZMod.finEquiv d) i).val = i.val := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => rfl

theorem boundedCoordinateEquiv_symm_apply (n : ℕ) (hn : 3 ≤ n)
    (c : Fin (modulus n) × Fin 2) :
    (boundedCoordinateEquiv n hn).symm c = r n ^ c.1.val * s n ^ c.2.val := by
  change element n hn ((ZMod.finEquiv (modulus n)) c.1) ((ZMod.finEquiv 2) c.2) = _
  rw [element_eq, val_finEquiv, val_finEquiv]

theorem unique_normal_form (n : ℕ) (hn : 3 ≤ n) (g : SemidihedralGroup n) :
    ∃! c : Fin (modulus n) × Fin 2, g = r n ^ c.1.val * s n ^ c.2.val := by
  refine ⟨boundedCoordinateEquiv n hn g, ?_, ?_⟩
  · change g = r n ^ (boundedCoordinateEquiv n hn g).1.val *
      s n ^ (boundedCoordinateEquiv n hn g).2.val
    rw [← boundedCoordinateEquiv_symm_apply n hn, Equiv.symm_apply_apply]
  · intro c hc
    rw [← boundedCoordinateEquiv_symm_apply n hn] at hc
    exact ((boundedCoordinateEquiv n hn).symm.injective
      (hc.symm.trans ((boundedCoordinateEquiv n hn).symm_apply_apply g).symm))

theorem card (n : ℕ) (hn : 3 ≤ n) : Nat.card (SemidihedralGroup n) = 2 ^ n := by
  rw [Nat.card_congr (boundedCoordinateEquiv n hn), Nat.card_prod,
    Nat.card_fin, Nat.card_fin, modulus]
  have he : n = (n - 1) + 1 := by omega
  conv_rhs => rw [he, pow_succ]

theorem isTwoGroup (n : ℕ) (hn : 3 ≤ n) : IsPGroup 2 (SemidihedralGroup n) :=
  IsPGroup.of_card (card n hn)

theorem orderOf_r (n : ℕ) (hn : 3 ≤ n) : orderOf (r n) = modulus n := by
  rw [← orderOf_injective (toModel n hn) (presentationEquivModel n hn).injective,
    toModel_r, modelR, orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem orderOf_s (n : ℕ) (hn : 3 ≤ n) : orderOf (s n) = 2 := by
  rw [← orderOf_injective (toModel n hn) (presentationEquivModel n hn).injective,
    toModel_s, modelS, orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem rotationHom_range (n : ℕ) : (rotationHom n).range = Subgroup.zpowers (r n) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact Subgroup.pow_mem (Subgroup.zpowers (r n)) (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    refine ⟨Multiplicative.ofAdd 1, ?_⟩
    by_cases hn : 2 ≤ n
    · exact rotationHom_one n hn
    · have hm : modulus n = 1 := by
        have he : n - 1 = 0 := by omega
        simp [modulus, he]
      have hr : r n = 1 := by simpa only [hm, pow_one] using r_modulus n
      simp [rotationHom, cyclicPowHom, hr]

@[expose] def parityHom (n : ℕ) (hn : 3 ≤ n) : SemidihedralGroup n →* Cyclic 2 :=
  SemidirectProduct.rightHom.comp (toModel n hn)

theorem parityHom_surjective (n : ℕ) (hn : 3 ≤ n) : Function.Surjective (parityHom n hn) :=
  SemidirectProduct.rightHom_surjective.comp (presentationEquivModel n hn).surjective

theorem parityHom_ker (n : ℕ) (hn : 3 ≤ n) :
    (parityHom n hn).ker = Subgroup.zpowers (r n) := by
  rw [← rotationHom_range]
  apply le_antisymm
  · intro g hg
    have he : (toModel n hn g).right = 1 := hg
    refine ⟨(toModel n hn g).left, ?_⟩
    apply (presentationEquivModel n hn).injective
    change toModel n hn (rotationHom n (toModel n hn g).left) = toModel n hn g
    rw [toModel_rotationHom]
    apply SemidirectProduct.ext
    · rfl
    · exact he.symm
  · rintro _ ⟨x, rfl⟩
    change (toModel n hn (rotationHom n x)).right = 1
    rw [toModel_rotationHom]
    rfl

theorem rotation_normal (n : ℕ) (hn : 3 ≤ n) : (Subgroup.zpowers (r n)).Normal := by
  rw [← parityHom_ker n hn]
  infer_instance

theorem rotation_index (n : ℕ) (hn : 3 ≤ n) : (Subgroup.zpowers (r n)).index = 2 := by
  rw [← parityHom_ker n hn, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (parityHom_surjective n hn)]
  rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (Cyclic 2)) ≃* Cyclic 2).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem normal_form (n : ℕ) (hn : 4 ≤ n) :
    (∀ g : SemidihedralGroup n,
      ∃! c : Fin (2 ^ (n - 1)) × Fin 2, g = r n ^ c.1.val * s n ^ c.2.val) ∧
    Nat.card (SemidihedralGroup n) = 2 ^ n ∧
    orderOf (r n) = 2 ^ (n - 1) ∧ orderOf (s n) = 2 ∧
    IsCyclic (Subgroup.zpowers (r n)) ∧ (Subgroup.zpowers (r n)).Normal ∧
    (Subgroup.zpowers (r n)).index = 2 := by
  exact ⟨unique_normal_form n (by omega), card n (by omega), orderOf_r n (by omega),
    orderOf_s n (by omega), inferInstance, rotation_normal n (by omega), rotation_index n (by omega)⟩

end CFSG.Semidihedral
