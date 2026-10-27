module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveFixedPoints
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LinearGroups

open Matrix
open scoped MatrixGroups

theorem isSolvable_dihedralGroup (z : ℕ) [NeZero z] : Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = z := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
    exact (Nat.eq_of_mul_eq_mul_right hz h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

section Extension

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

@[expose] noncomputable def pglExtend (k E : Type*) [Field k] [Field E] [Algebra k E] :
    PGL(Fin 2, k) →* PGL(Fin 2, E) :=
  QuotientGroup.map _ _ (GeneralLinearGroup.map (algebraMap k E)) (by
    rw [GeneralLinearGroup.center_eq_range_scalar, GeneralLinearGroup.center_eq_range_scalar]
    rintro _ ⟨u, rfl⟩
    refine ⟨Units.map (algebraMap k E : k →* E) u, Units.ext ?_⟩
    ext i j
    rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs <;> simp)

theorem pglExtend_mk (g : GL (Fin 2) k) :
    pglExtend k E (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap k E) g) :=
  rfl

theorem pglExtend_injective : Function.Injective (pglExtend k E) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [pglExtend_mk, mk_eq_one_iff_exists_scalar] at hx
  obtain ⟨u, hu⟩ := hx
  have hent : ∀ i j, algebraMap k E ((g : Matrix (Fin 2) (Fin 2) k) i j) =
      if i = j then (u : E) else 0 := by
    intro i j
    have := congrArg (fun A : GL (Fin 2) E => (A : Matrix (Fin 2) (Fin 2) E) i j) hu
    simpa [GeneralLinearGroup.map, Matrix.scalar_apply, Matrix.diagonal_apply] using this
  have h01 : (g : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 :=
    (algebraMap k E).injective (by rw [hent]; simp)
  have h10 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 :=
    (algebraMap k E).injective (by rw [hent]; simp)
  have h11 : (g : Matrix (Fin 2) (Fin 2) k) 1 1 = (g : Matrix (Fin 2) (Fin 2) k) 0 0 :=
    (algebraMap k E).injective (by rw [hent, hent]; simp)
  have h00 : (g : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := by
    intro h0
    have := g.isUnit.ne_zero
    apply this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h01, h10, h11]
  refine mk_eq_one_iff_exists_scalar.mpr ⟨Units.mk0 _ h00, Units.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, h01, h10, h11]

theorem pglExtend_mem_range_toPGL (hsq : ∀ x : k, IsSquare (algebraMap k E x))
    (x : PGL(Fin 2, k)) :
    pglExtend k E x ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := E)).range := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  obtain ⟨l, hl⟩ := hsq (g : Matrix (Fin 2) (Fin 2) k).det
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero, map_eq_zero] at hl
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero hl
  set s : Eˣ := Units.mk0 l hl0
  let g' : GL (Fin 2) E :=
    GeneralLinearGroup.map (algebraMap k E) g * GeneralLinearGroup.scalar (Fin 2) s⁻¹
  have hdet : (g' : Matrix (Fin 2) (Fin 2) E).det = 1 := by
    have hmap : ((GeneralLinearGroup.map (algebraMap k E) g : GL (Fin 2) E) :
        Matrix (Fin 2) (Fin 2) E).det = l * l := by
      rw [← hl, RingHom.map_det]
      rfl
    simp only [g', Units.val_mul, det_mul, hmap, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Units.val_inv_eq_inv_val, Units.val_mk0, s]
    field_simp
  let A : Matrix.SpecialLinearGroup (Fin 2) E := ⟨g', hdet⟩
  refine ⟨(A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E), ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pglExtend_mk, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨s, Units.ext ?_⟩
  change (g' : Matrix (Fin 2) (Fin 2) E) *
      ((GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = _
  rw [← Units.val_mul]
  congr 1
  simp only [g']
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem isSquare_algebraMap_of_card_eq_sq [Fintype k] [Fintype E]
    (hE : Fintype.card E = Fintype.card k ^ 2) (x : k) : IsSquare (algebraMap k E x) := by
  classical
  by_cases hx : x = 0
  · rw [hx, map_zero]
    exact ⟨0, (mul_zero 0).symm⟩
  by_cases h2 : ringChar E = 2
  · exact FiniteField.isSquare_of_char_two h2 _
  · rw [FiniteField.isSquare_iff h2 ((map_ne_zero _).mpr hx)]
    have hk2 : ringChar k ≠ 2 := by rwa [Algebra.ringChar_eq k E]
    have hodd := FiniteField.odd_card_of_char_ne_two hk2
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card k = 2 * m + 1 := ⟨Fintype.card k / 2, by omega⟩
    have hexp : Fintype.card E / 2 = (Fintype.card k - 1) * (m + 1) := by
      rw [hE, hm]
      have : (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
      omega
    rw [hexp, pow_mul, ← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one, one_pow]

end Extension

theorem tame_projective_linear_two_nonsolvable_order_sixty
    {k : Type*} [Field k] [Finite k]
    {p : ℕ} (hp : p.Prime) [CharP k p] (J : Subgroup PGL(Fin 2, k)) (hJ : ¬ p ∣ Nat.card J)
    (hns : ¬ Group.IsSolvable J) : Nat.card J = 60 ∧ 4 ∣ Nat.card J ∧ ¬ 8 ∣ Nat.card J := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite k
  let E := FiniteField.Extension k p 2
  have := Fintype.ofFinite E
  have hEcard : Nat.card E = Nat.card k ^ 2 := FiniteField.natCard_extension k p 2
  obtain ⟨f, -, hkcard⟩ := FiniteField.card k p
  have hEp : Nat.card E = p ^ (2 * (f : ℕ)) := by
    rw [hEcard, Nat.card_eq_fintype_card, hkcard, ← pow_mul, mul_comm]
  have hsq : ∀ x : k, IsSquare (algebraMap k E x) :=
    isSquare_algebraMap_of_card_eq_sq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard])
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := E)
  set J₁ := J.map (pglExtend k E)
  have hJ₁ : J₁ ≤ ι.range := by
    rintro _ ⟨x, -, rfl⟩
    exact pglExtend_mem_range_toPGL hsq x
  set H : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) E) := J₁.comap ι
  have hmap : H.map ι = J₁ := Subgroup.map_comap_eq_self hJ₁
  let eH : H ≃* J :=
    ((H.equivMapOfInjective ι ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (MulEquiv.subgroupCongr hmap)).trans
      (J.equivMapOfInjective (pglExtend k E) pglExtend_injective).symm
  have hcard : Nat.card H = Nat.card J := Nat.card_congr eH.toEquiv
  have hsolv : Group.IsSolvable H → Group.IsSolvable J := fun h =>
    Group.isSolvable_of_surjective (f := eH.toMonoidHom) eH.surjective
  have hHp : ¬ p ∣ Nat.card H := hcard ▸ hJ
  have h60 : Nat.card J = 60 := by
    rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hEp H hHp with
      ⟨z, -, -, hcyc⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exfalso
      apply hns
      apply hsolv
      let : CommGroup H := IsCyclic.commGroup
      infer_instance
    · exfalso
      apply hns
      apply hsolv
      have : NeZero z := ⟨fun hz0 => by
        rw [hz0, mul_zero] at hz
        exact Nat.card_pos.ne' hz⟩
      have := isSolvable_dihedralGroup z
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · exfalso
      apply hns
      apply hsolv
      have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · exfalso
      apply hns
      apply hsolv
      have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · rw [← hcard, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
  refine ⟨h60, ?_, ?_⟩ <;> rw [h60] <;> decide

end CFSG.LinearGroups
