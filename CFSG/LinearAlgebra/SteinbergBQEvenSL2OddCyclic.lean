module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Matrix
open scoped MatrixGroups

theorem mul_self_fin_two {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem eq_one_of_scalar_charTwo {k : Type*} [Field k] [CharP k 2] {g : SL(2, k)}
    (h01 : (g : Matrix (Fin 2) (Fin 2) k) 0 1 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    (h00 : (g : Matrix (Fin 2) (Fin 2) k) 0 0 = (g : Matrix (Fin 2) (Fin 2) k) 1 1) : g = 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_two, h01, h10, ← h00, mul_zero, sub_zero] at hdet
  have ha : (g : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    have h2k : (2 : k) = 0 := CharTwo.two_eq_zero
    have h2 : ((g : Matrix (Fin 2) (Fin 2) k) 0 0 + 1) * ((g : Matrix (Fin 2) (Fin 2) k) 0 0 + 1)
        = 0 := by
      linear_combination hdet + ((g : Matrix (Fin 2) (Fin 2) k) 0 0 + 1) * h2k
    have h3 := mul_self_eq_zero.1 h2
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h3
    exact h3
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using h01
  · simpa using h10
  · simpa [← h00] using ha

end CFSG.LinearAlgebra.SteinbergBQ

namespace CFSG.LinearAlgebra

open Matrix SteinbergBQ
open scoped MatrixGroups

theorem even_SL2_odd_prime_subgroups_cyclic {k : Type*} [Field k] [Finite k] [CharP k 2]
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (P : Subgroup (SL(2, k))) (hP : IsPGroup p P) :
    IsCyclic P := by
  classical
  have : Fintype k := Fintype.ofFinite k
  by_cases hP1 : P = ⊥
  · subst hP1
    infer_instance
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hP1
  have : Finite P := inferInstance
  have := IsPGroup.center_nontrivial hP
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  set x : SL(2, k) := ((z : P) : SL(2, k)) with hxdef
  have hx1 : x ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hxc : ∀ g ∈ P, g * x = x * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩)
  set L := AlgebraicClosure k
  let M : SL(2, k) → Matrix (Fin 2) (Fin 2) L := fun g =>
    (algebraMap k L).mapMatrix (g : Matrix (Fin 2) (Fin 2) k)
  have hM : ∀ g i j, M g i j = algebraMap k L ((g : Matrix (Fin 2) (Fin 2) k) i j) :=
    fun g i j => rfl
  have hMmul : ∀ g h : SL(2, k), M (g * h) = M g * M h := fun g h => by
    simp only [M, Matrix.SpecialLinearGroup.coe_mul, map_mul]
  have hinjL : Function.Injective (algebraMap k L) := (algebraMap k L).injective
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M x))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hxv : M x *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  set f := Matrix.toLin' (M x - μ • (1 : Matrix (Fin 2) (Fin 2) L)) with hfdef
  have hf0 : f ≠ 0 := by
    intro h0
    have hM0 : M x - μ • (1 : Matrix (Fin 2) (Fin 2) L) = 0 := by
      have := congrArg (Matrix.toLin' (R := L) (n := Fin 2)).symm h0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    have he : ∀ i j, M x i j = (μ • (1 : Matrix (Fin 2) (Fin 2) L)) i j := fun i j => by
      have := congrFun (congrFun hM0 i) j
      rwa [Matrix.sub_apply, Matrix.zero_apply, sub_eq_zero] at this
    apply hx1
    refine eq_one_of_scalar_charTwo (hinjL ?_) (hinjL ?_) (hinjL ?_)
    · rw [← hM, he]
      simp
    · rw [← hM, he]
      simp
    · rw [← hM, ← hM, he, he]
      simp
  have hker : LinearMap.ker f = Submodule.span L {v} := by
    have hvker : v ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, hfdef, Matrix.toLin'_apply, Matrix.sub_mulVec, hxv,
        Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    refine (Submodule.eq_of_le_of_finrank_le
      ((Submodule.span_singleton_le_iff_mem _ _).2 hvker) ?_).symm
    rw [finrank_span_singleton hv0]
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at h1
    have h2 : 0 < Module.finrank L (LinearMap.range f) := by
      obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hf0 (LinearMap.ext hcon)
      exact Module.finrank_pos_iff_exists_ne_zero.2
        ⟨⟨f w, LinearMap.mem_range_self f w⟩, fun h => hw (congrArg Subtype.val h)⟩
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  have hvi : v i ≠ 0 := hi
  obtain ⟨c, hc⟩ : ∃ c : SL(2, k) → L, ∀ g, c g = (M g *ᵥ v) i / v i := ⟨_, fun _ => rfl⟩
  have hline : ∀ g ∈ P, M g *ᵥ v = c g • v := by
    intro g hg
    have hmem : M g *ᵥ v ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, hfdef, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
        ← hMmul, ← hxc g hg, hMmul, ← Matrix.mulVec_mulVec, hxv, Matrix.mulVec_smul,
        Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    rw [hker] at hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have hai : c g = a := by
      rw [hc, ← ha, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hvi, mul_one]
    rw [hai, ha]
  have hc1 : c 1 = 1 := by
    rw [hc]
    simp only [M, Matrix.SpecialLinearGroup.coe_one, map_one, Matrix.one_mulVec]
    exact div_self hvi
  have hcmul : ∀ g ∈ P, ∀ h ∈ P, c (g * h) = c g * c h := by
    intro g hg h hh
    have e : M (g * h) *ᵥ v = (c g * c h) • v := by
      rw [hMmul, ← Matrix.mulVec_mulVec, hline h hh, Matrix.mulVec_smul, hline g hg, smul_smul,
        mul_comm]
    rw [hc (g * h), e, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hvi, mul_one]
  let χ : P →* L :=
    { toFun := fun g => c g
      map_one' := hc1
      map_mul' := fun g h => hcmul g g.2 h h.2 }
  have hker1 : ∀ g : P, χ g = 1 → g = 1 := by
    intro g hg
    have hgv : M g *ᵥ v = v := by
      rw [hline g g.2, show c g = 1 from hg, one_smul]
    have hdetL : (M g).det = 1 := by
      rw [← RingHom.map_det, ((g : SL(2, k))).2, map_one]
    have htrL : (M g).trace =
        algebraMap k L (((g : SL(2, k)) : Matrix (Fin 2) (Fin 2) k).trace) := by
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, hM, hM, map_add]
    have hCHL := mul_self_fin_two (M g)
    rw [hdetL, one_smul] at hCHL
    have h1 : (M g * M g) *ᵥ v = ((M g).trace • M g - 1) *ᵥ v := by rw [hCHL]
    rw [← Matrix.mulVec_mulVec, hgv, hgv, Matrix.sub_mulVec, Matrix.smul_mulVec, hgv,
      Matrix.one_mulVec] at h1
    have h2 := congrFun h1 i
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
    have htr0 : (M g).trace = 0 := by
      have h2L : (2 : L) = 0 := CharTwo.two_eq_zero
      have h3 : (M g).trace * v i = 0 := by linear_combination -h2 + (v i) * h2L
      exact (mul_eq_zero.1 h3).resolve_right hvi
    have htr' : ((g : SL(2, k)) : Matrix (Fin 2) (Fin 2) k).trace = 0 :=
      hinjL (by rw [← htrL, htr0, map_zero])
    have hCH := mul_self_fin_two ((g : SL(2, k)) : Matrix (Fin 2) (Fin 2) k)
    have hneg : (-1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
      ext a b
      rw [Matrix.neg_apply]
      exact CharTwo.neg_eq _
    rw [((g : SL(2, k))).2, htr', zero_smul, one_smul, zero_sub, hneg] at hCH
    have hg2 : g ^ 2 = 1 := by
      rw [pow_two]
      exact Subtype.ext (Subtype.ext hCH)
    obtain ⟨n, hn⟩ := hP g
    have h3 := orderOf_dvd_of_pow_eq_one hg2
    have h4 := orderOf_dvd_of_pow_eq_one hn
    have hcop : Nat.Coprime (p ^ n) 2 :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h4 h3)
  have hχinj : Function.Injective χ := by
    intro g h hgh
    have h1 : χ (g * h⁻¹) = 1 := by
      rw [map_mul, hgh, ← map_mul, mul_inv_cancel, map_one]
    exact mul_inv_eq_one.1 (hker1 _ h1)
  exact isCyclic_of_injective_ringHom χ hχinj

end CFSG.LinearAlgebra
