module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TRankCore
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix

variable {F : Type} [Field F]

theorem scalar_inj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) (R := F)) := by
  intro c d h
  have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  exact Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using this)

theorem card_scalars_le_three [Finite F] {A : Subgroup (GL (Fin 3) F)}
    (hp : ∀ x ∈ A, x ^ 3 = 1) : Nat.card ↥(A ⊓ Subgroup.center (GL (Fin 3) F)) ≤ 3 := by
  classical
  have := Fintype.ofFinite F
  set P : Subgroup Fˣ := A.comap (Matrix.GeneralLinearGroup.scalar (Fin 3) (R := F)) with hP
  have hZc : A ⊓ Subgroup.center (GL (Fin 3) F) =
      P.map (Matrix.GeneralLinearGroup.scalar (Fin 3) (R := F)) := by
    ext g
    simp only [Subgroup.mem_inf, Matrix.GeneralLinearGroup.center_eq_range_scalar,
      MonoidHom.mem_range, Subgroup.mem_map, hP, Subgroup.mem_comap]
    constructor
    · rintro ⟨hg, c, rfl⟩
      exact ⟨c, hg, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c, rfl⟩
  rw [hZc, Subgroup.card_map_of_injective scalar_inj]
  have hcube : ∀ c ∈ P, c ^ 3 = 1 := by
    intro c hc
    have h := hp _ hc
    rw [← map_pow] at h
    exact scalar_inj (by rw [h, map_one])
  have h1 := IsCyclic.card_pow_eq_one_le (α := Fˣ) (n := 3) (by norm_num)
  have h2 : Nat.card P ≤ Fintype.card ↥(Finset.univ.filter (fun a : Fˣ => a ^ 3 = 1)) := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.card_le_of_injective
      (fun c : ↥P => (⟨c.1, by simpa using hcube c.1 c.2⟩ :
        ↥(Finset.univ.filter (fun a : Fˣ => a ^ 3 = 1)))) ?_
    intro a b h
    exact Subtype.ext (congrArg (fun z : ↥(Finset.univ.filter (fun a : Fˣ => a ^ 3 = 1)) => (z : Fˣ)) h)
  rw [Fintype.card_coe] at h2
  exact h2.trans h1

theorem false_of_nine_cosets (h3 : (3 : F) ≠ 0) {A : Subgroup (GL (Fin 3) F)}
    (hdet : ∀ g ∈ A, (g : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hp : ∀ x ∈ A, x ^ 3 = 1)
    (r : Fin 9 → GL (Fin 3) F) (hrA : ∀ i, r i ∈ A)
    (hns : ∀ i j, i ≠ j → r i * (r j)⁻¹ ∉ Subgroup.center (GL (Fin 3) F)) : False := by
  classical
  let v : Fin 9 → Matrix (Fin 3) (Fin 3) F := fun i => ((r i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have htr : ∀ i j, i ≠ j → Matrix.trace (v i * (((r j)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = 0 := by
    intro i j hij
    have hy : r i * (r j)⁻¹ ∈ A := A.mul_mem (hrA i) (A.inv_mem (hrA j))
    have hy3 : (r i * (r j)⁻¹) ^ 3 = 1 := hp _ hy
    have hval : v i * (((r j)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((r i * (r j)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := (Units.val_mul _ _).symm
    rw [hval]
    refine trace_eq_zero_of_nonscalar h3 ?_ (hdet _ hy) ?_
    · have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hy3
      simpa [pow_succ, Units.val_mul] using this
    · intro c hc
      apply hns i j hij
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      have hc0 : c ≠ 0 := by
        intro h0
        have h1 : ((r i * (r j)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 0 := by
          rw [hc, h0, zero_smul]
        have h2 := Units.mul_inv (r i * (r j)⁻¹)
        rw [h1, zero_mul] at h2
        exact zero_ne_one h2
      refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, hc]
      simp [Matrix.smul_one_eq_diagonal]
  have hind : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (fun X => Matrix.trace (X * (((r j)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) hg
    simp only [Finset.sum_mul, smul_mul_assoc, zero_mul, Matrix.trace_zero, Matrix.trace_sum,
      Matrix.trace_smul] at h1
    rw [Finset.sum_eq_single j] at h1
    · have hj : Matrix.trace (v j * (((r j)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = 3 := by
        simp [v, ← Units.val_mul]
      rw [hj, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_right h3
    · intro i _ hij
      rw [htr i j hij, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  exact false_of_nine_commuting hind (fun i j => by
    simp only [v, ← Units.val_mul]
    exact congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F))
      (hcomm _ (hrA i) _ (hrA j)))

theorem card_le_nine [Finite F] (h3 : (3 : F) ≠ 0) {A : Subgroup (GL (Fin 3) F)}
    (hdet : ∀ g ∈ A, (g : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hp : ∀ x ∈ A, x ^ 3 = 1) :
    Nat.card A ≤ 9 := by
  classical
  by_contra hlt
  push Not at hlt
  have hPG : IsPGroup 3 A := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hp g g.2)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hPG.exists_card_eq
  have hk3 : 27 ≤ Nat.card A := by
    have : 3 ≤ k := by
      by_contra h
      push Not at h
      have h9 : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h9
      omega
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) this
      _ = Nat.card A := hk.symm
  set Z : Subgroup A := (A ⊓ Subgroup.center (GL (Fin 3) F)).subgroupOf A with hZ
  have hZc : Nat.card Z ≤ 3 := by
    have h1 := card_scalars_le_three (A := A) hp
    have h2 : Nat.card Z = Nat.card ↥(A ⊓ Subgroup.center (GL (Fin 3) F)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    omega
  have hidx : 9 ≤ Z.index := by
    have := Subgroup.card_mul_index Z
    by_contra h
    push Not at h
    have h4 : Nat.card Z * Z.index ≤ 3 * 8 := Nat.mul_le_mul hZc (by omega)
    omega
  have hQcard : 9 ≤ Nat.card (A ⧸ Z) := hidx
  haveI : Finite (A ⧸ Z) := inferInstance
  haveI := Fintype.ofFinite (A ⧸ Z)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 9) (β := A ⧸ Z) (by simpa [Nat.card_eq_fintype_card] using hQcard)
  have hcA : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  refine false_of_nine_cosets h3 hdet hcomm hp (fun i => ((e i).out : A)) (fun i => ((e i).out).2) ?_
  intro i j hij hcen
  have hmem : ((e i).out)⁻¹ * (e j).out ∈ Z := by
    refine Subgroup.mem_subgroupOf.2 ⟨(((e i).out)⁻¹ * (e j).out).2, ?_⟩
    have h1 : (((e i).out)⁻¹ * (e j).out : A) = ((e i).out * ((e j).out)⁻¹)⁻¹ := by
      rw [_root_.mul_inv_rev, inv_inv]
      exact hcA _ _
    rw [h1, Subgroup.coe_inv]
    exact (Subgroup.center (GL (Fin 3) F)).inv_mem hcen
  have : (QuotientGroup.mk (e i).out : A ⧸ Z) = QuotientGroup.mk (e j).out := QuotientGroup.eq.2 hmem
  rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  exact hij (e.injective this)

end CFSG.HardMathSupport.Solomon.Coordinator
