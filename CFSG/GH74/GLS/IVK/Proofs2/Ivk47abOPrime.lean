module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open CFSG.GH74.GLS Subgroup
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

@[expose] def wMat (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def uMat (F : Type) [Field F] : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem wMat_mul_self : wMat F * wMat F = -1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_one_mul_neg_one : (-1 : SL(2, F)) * (-1) = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wMat_pow_four : wMat F ^ 4 = 1 := by
  calc wMat F ^ 4 = (wMat F * wMat F) * (wMat F * wMat F) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [wMat_mul_self, neg_one_mul_neg_one]

theorem wMat_not_mem_center : wMat F ∉ Subgroup.center SL(2, F) := by
  intro h
  have h1 := Subgroup.mem_center_iff.1 h (uMat F)
  have h2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
  simp [wMat, uMat, Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem sq_eq_one_of_mem_center {u : SL(2, F)} (hu : u ∈ Subgroup.center SL(2, F)) : u ^ 2 = 1 := by
  obtain ⟨r, hr, hru⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hu
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hru, ← map_mul, ← pow_two, hr, map_one]
  rfl

theorem oPrimeResidual_sl2 [Finite F] (hF : 4 ≤ Nat.card F) : oPrimeResidual 2 SL(2, F) = ⊤ := by
  have : IsSimpleGroup PSL(2, F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  have hnorm : (oPrimeResidual 2 SL(2, F)).Normal :=
    Stage1.Thm6.Prod.oPrimeResidual_normal 2 SL(2, F)
  let Q : SL(2, F) →* PSL(2, F) := QuotientGroup.mk' (Subgroup.center SL(2, F))
  have hQ : Function.Surjective Q := QuotientGroup.mk'_surjective _
  have hcenter : Subgroup.center SL(2, F) ≤ oPrimeResidual 2 SL(2, F) := by
    intro u hu
    exact Subgroup.subset_closure ⟨1, by rw [pow_one]; exact sq_eq_one_of_mem_center hu⟩
  rcases (hnorm.map Q hQ).eq_bot_or_eq_top with h | h
  · exfalso
    have hWN : wMat F ∈ oPrimeResidual 2 SL(2, F) :=
      Subgroup.subset_closure ⟨2, by rw [show 2 ^ 2 = 4 from rfl]; exact wMat_pow_four⟩
    have hQW : Q (wMat F) = 1 := by
      have : Q (wMat F) ∈ (oPrimeResidual 2 SL(2, F)).map Q := Subgroup.mem_map_of_mem Q hWN
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    exact wMat_not_mem_center ((QuotientGroup.eq_one_iff _).1 hQW)
  · rw [eq_top_iff]
    intro x _
    have hx : Q x ∈ (oPrimeResidual 2 SL(2, F)).map Q := by rw [h]; trivial
    obtain ⟨n, hn, hnx⟩ := hx
    have hmem : n⁻¹ * x ∈ Subgroup.center SL(2, F) := by
      have : n⁻¹ * x ∈ Q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
      rwa [QuotientGroup.ker_mk'] at this
    have hx' : x = n * (n⁻¹ * x) := by group
    rw [hx']
    exact mul_mem hn (hcenter hmem)

end SL2

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem oPrimeResidual_map_equiv (p : ℕ) (e : A ≃* B) :
    (oPrimeResidual p A).map e.toMonoidHom = oPrimeResidual p B := by
  unfold oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    apply e.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply, hk]

theorem oPrimeResidual_mulEquiv (p : ℕ) (e : A ≃* B) :
    Nonempty (↥(oPrimeResidual p A) ≃* ↥(oPrimeResidual p B)) :=
  ⟨(Subgroup.equivMapOfInjective (oPrimeResidual p A) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (oPrimeResidual_map_equiv p e))⟩

theorem oPrimeResidualOf_eq_closure' {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) :
    oPrimeResidualOf p X = Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ p ^ k = 1} := by
  rw [oPrimeResidualOf, oPrimeResidual, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hk])⟩, rfl⟩

theorem map_oPrimeResidualOf {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (p : ℕ)
    (X : Subgroup G) :
    (oPrimeResidualOf p X).map φ.toMonoidHom = oPrimeResidualOf p (X.map φ.toMonoidHom) := by
  rw [oPrimeResidualOf_eq_closure', oPrimeResidualOf_eq_closure', MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    apply φ.injective
    rw [map_pow, map_one]
    exact hk

end Transport

section ShapeOPrime

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem le_oPrimeResidual_of_equiv (I : Subgroup Y) {X : Type} [Group X] (e : ↥I ≃* X)
    (h : oPrimeResidual 2 X = ⊤) : I ≤ oPrimeResidual 2 Y := by
  have h1 : oPrimeResidual 2 ↥I = ⊤ := by
    have := oPrimeResidual_map_equiv 2 e
    rw [h] at this
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [this, Subgroup.map_top_of_surjective _ e.surjective]
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥I) ∈ oPrimeResidual 2 ↥I := by rw [h1]; trivial
  have hle : (oPrimeResidual 2 ↥I).map I.subtype ≤ oPrimeResidual 2 Y := by
    unfold oPrimeResidual
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  exact hle ⟨⟨y, hy⟩, hy', rfl⟩

theorem Shape.oPrimeResidual_eq_top [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂)
    (h₁ : 4 ≤ Nat.card F₁) (h₂ : 4 ≤ Nat.card F₂) : oPrimeResidual 2 Y = ⊤ := by
  have hI₁ : S.I₁ ≤ oPrimeResidual 2 Y := le_oPrimeResidual_of_equiv S.I₁ S.e₁ (oPrimeResidual_sl2 h₁)
  have hI₂ : S.I₂ ≤ oPrimeResidual 2 Y := le_oPrimeResidual_of_equiv S.I₂ S.e₂ (oPrimeResidual_sl2 h₂)
  have ht : S.t ∈ oPrimeResidual 2 Y :=
    Subgroup.subset_closure ⟨1, by rw [pow_one, pow_two]; exact S.t_sq⟩
  rw [eq_top_iff, ← S.gen]
  exact sup_le (sup_le hI₁ hI₂) ((Subgroup.zpowers_le).2 ht)

end ShapeOPrime

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
