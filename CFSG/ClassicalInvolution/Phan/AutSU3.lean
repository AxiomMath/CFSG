module

public import CFSG.ClassicalInvolution.Phan.AutSU2

public section

namespace CFSG.ClassicalInvolution.Phan

section Extend

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg (embSUid embPair coe_embSUid diagGL coe_diagGL coe_diagGL_inv normOne
  torusTwo)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem embPair_map (φ : K ≃+* K) (c : Fin 3) (X : Matrix (Fin 2) (Fin 2) K) :
    embPair c (X.map φ) = (embPair c X).map φ := by
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [embPair]

theorem fieldAutSU_embSUid (φ : K ≃+* K) (c : Fin 3) (A : Su K p f 2) :
    fieldAutSU p f φ 3 (embSUid (unitaryInvolution K p f) c A) =
      embSUid (unitaryInvolution K p f) c (fieldAutSU p f φ 2 A) := by
  refine Subtype.ext (Units.ext ?_)
  show ((embSUid (unitaryInvolution K p f) c A : Su K p f 3) : GL (Fin 3) K).val.map φ = _
  rw [coe_embSUid]
  show (embPair c ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map φ = _
  rw [← embPair_map]
  rfl

theorem diagConj_embSUid_two (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    diagConj p f hK ![a, b, 1] (embSUid (unitaryInvolution K p f) 2 A) =
      embSUid (unitaryInvolution K p f) 2 (diagConj p f hK ![a, b] A) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_diagConj]
  show _ = ((embSUid (unitaryInvolution K p f) 2 (diagConj p f hK ![a, b] A) : Su K p f 3) :
    GL (Fin 3) K).val
  rw [coe_embSUid, coe_diagConj]
  simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv, coe_embSUid]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem diagConj_embSUid_zero (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    diagConj p f hK ![a, b, 1] (embSUid (unitaryInvolution K p f) 0 A) =
      embSUid (unitaryInvolution K p f) 0 (diagConj p f hK ![b, 1] A) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_diagConj]
  show _ = ((embSUid (unitaryInvolution K p f) 0 (diagConj p f hK ![b, 1] A) : Su K p f 3) :
    GL (Fin 3) K).val
  rw [coe_embSUid, coe_diagConj]
  simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv, coe_embSUid]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.diagonal_mul, Matrix.mul_diagonal]

@[expose] noncomputable def pairExt (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (φ : K ≃+* K) : MulAut (Su K p f 3) :=
  diagConj p f hK ![a, b, 1] * fieldAutSU p f φ 3

theorem pairExt_embSUid_two (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (φ : K ≃+* K) (A : Su K p f 2) :
    pairExt hK a b φ (embSUid (unitaryInvolution K p f) 2 A) =
      embSUid (unitaryInvolution K p f) 2
        ((diagConj p f hK ![a, b] * fieldAutSU p f φ 2) A) := by
  show diagConj p f hK ![a, b, 1] (fieldAutSU p f φ 3 (embSUid (unitaryInvolution K p f) 2 A)) = _
  rw [fieldAutSU_embSUid, diagConj_embSUid_two]
  rfl

theorem pairExt_embSUid_zero (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (φ : K ≃+* K) (A : Su K p f 2) :
    pairExt hK a b φ (embSUid (unitaryInvolution K p f) 0 A) =
      embSUid (unitaryInvolution K p f) 0
        ((diagConj p f hK ![b, 1] * fieldAutSU p f φ 2) A) := by
  show diagConj p f hK ![a, b, 1] (fieldAutSU p f φ 3 (embSUid (unitaryInvolution K p f) 0 A)) = _
  rw [fieldAutSU_embSUid, diagConj_embSUid_zero]
  rfl

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem map_range_eq_of_comp {G H : Type*} [Group G] [Group H] (β : MulAut G) (α : MulAut H)
    (e : H →* G) (h : ∀ x, β (e x) = e (α x)) : e.range.map β.toMonoidHom = e.range := by
  ext g
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨α x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e (α.symm x), ⟨α.symm x, rfl⟩, by simp [h]⟩

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem symm_comp_eq_of_comp_eq {G H : Type*} [Group G] [Group H] (β : MulAut G) (α : MulAut H)
    (e : H →* G) (h : β.toMonoidHom.comp e = e.comp α.toMonoidHom) :
    β.symm.toMonoidHom.comp e = e.comp α.symm.toMonoidHom := by
  ext x
  have := DFunLike.congr_fun h (α.symm x)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this ⊢
  rw [← this, MulEquiv.symm_apply_apply]

theorem exists_mulAut_extend (hK : Nat.card K = (p ^ f) ^ 2) (α : MulAut (Su K p f 2))
    (hα : (torusTwo (unitaryInvolution K p f)).range.map α.toMonoidHom ≤
      (torusTwo (unitaryInvolution K p f)).range) :
    ∃ β : MulAut (Su K p f 3),
      (∀ A, β (embSUid (unitaryInvolution K p f) 2 A) =
        embSUid (unitaryInvolution K p f) 2 (α A)) ∧
      (B12 K p f).map β.toMonoidHom = B12 K p f ∧ (B23 K p f).map β.toMonoidHom = B23 K p f := by
  obtain ⟨a, b, φ, rfl⟩ := exists_diagConj_fieldAut hK α hα
  exact ⟨pairExt hK a b φ, pairExt_embSUid_two hK a b φ,
    map_range_eq_of_comp _ _ _ (pairExt_embSUid_two hK a b φ),
    map_range_eq_of_comp _ _ _ (pairExt_embSUid_zero hK a b φ)⟩

theorem exists_mulAut_extend_comp (hK : Nat.card K = (p ^ f) ^ 2) (α : MulAut (Su K p f 2))
    (hα : (torusTwo (unitaryInvolution K p f)).range.map α.toMonoidHom ≤
      (torusTwo (unitaryInvolution K p f)).range) :
    ∃ β : MulAut (Su K p f 3),
      β.toMonoidHom.comp (embSUid (unitaryInvolution K p f) 2) =
        (embSUid (unitaryInvolution K p f) 2).comp α.toMonoidHom ∧
      (B12 K p f).map β.toMonoidHom = B12 K p f ∧ (B23 K p f).map β.toMonoidHom = B23 K p f := by
  obtain ⟨β, h1, h2, h3⟩ := exists_mulAut_extend hK α hα
  exact ⟨β, MonoidHom.ext h1, h2, h3⟩

theorem exists_mulAut_extend_of_map_eq (hK : Nat.card K = (p ^ f) ^ 2) (α : MulAut (Su K p f 2))
    (hα : (torusTwo (unitaryInvolution K p f)).range.map α.toMonoidHom =
      (torusTwo (unitaryInvolution K p f)).range) :
    ∃ β : MulAut (Su K p f 3),
      (∀ A, β (embSUid (unitaryInvolution K p f) 2 A) =
        embSUid (unitaryInvolution K p f) 2 (α A)) ∧
      (B23 K p f).map β.toMonoidHom ≤ B23 K p f := by
  obtain ⟨β, h1, -, h3⟩ := exists_mulAut_extend hK α hα.le
  exact ⟨β, h1, h3.le⟩

end Extend

end CFSG.ClassicalInvolution.Phan
