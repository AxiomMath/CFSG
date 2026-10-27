module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.LinearFamily
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def symm3 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 1; 0, 1, 1]

@[expose] def symm4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 1, 0; 0, 0, 0, 1]

theorem symm3_spec : symm3ᵀ = symm3 ∧ symm3 ^ 7 = 1 ∧ symm3.det = 1 ∧ symm3 0 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem symm4_spec : symm4ᵀ = symm4 ∧ symm4 ^ 7 = 1 ∧ symm4.det = 1 ∧ symm4 0 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide


section

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_proj_of_symm {n : ℕ} (hn : 3 ≤ n) (S : Matrix (Fin n) (Fin n) (ZMod 2))
    (hS : Sᵀ = S) (hS7 : S ^ 7 = 1) (hdet : S.det = 1)
    (h01 : S ⟨0, by omega⟩ ⟨1, by omega⟩ = 1) :
    ∃ y : projectiveSL n K, orderOf y = 7 ∧
      ∀ ρ : K ≃+* K, (fieldAut n K ρ * dualAut n K) y = y⁻¹ := by
  classical
  have hcast : (ZMod.castHom (dvd_refl 2) K : ZMod 2 →+* K) = ZMod.castHom (dvd_refl 2) K := rfl
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let SK : Matrix (Fin n) (Fin n) K := S.map ι
  have hSKdet : SK.det = 1 := by
    have := RingHom.map_det ι S
    rw [hdet, map_one] at this
    simpa [SK, RingHom.mapMatrix_apply] using this.symm
  let g : Matrix.SpecialLinearGroup (Fin n) K := ⟨SK, hSKdet⟩
  have hSK7 : SK ^ 7 = 1 := by
    have := congrArg (ι.mapMatrix) hS7
    simpa [SK, RingHom.mapMatrix_apply, map_pow] using this
  have hgT : (g : Matrix (Fin n) (Fin n) K)ᵀ = g := by
    show SKᵀ = SK
    simp only [SK, ← Matrix.transpose_map, hS]
  have hg7 : g ^ 7 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]; exact hSK7)
  have hgns : ∀ c : K, (g : Matrix (Fin n) (Fin n) K) ≠ Matrix.scalar (Fin n) c := by
    intro c h
    have := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply] at this
    have h1 : SK ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
      simp only [SK, Matrix.map_apply, h01, map_one]
    change SK ⟨0, by omega⟩ ⟨1, by omega⟩ = _ at this
    rw [h1] at this
    simp at this
  refine ⟨proj n K g, ?_, ?_⟩
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hg7, map_one]
    · intro h
      rw [proj_eq_one_iff, mem_scalars] at h
      obtain ⟨c, -, hc⟩ := h
      exact hgns c hc
  · intro ρ
    have hgrev : (g⁻¹).transpose = g⁻¹ := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_transpose, hgT]
    have hmap : Matrix.SpecialLinearGroup.map ρ.toRingHom g = g := by
      apply Subtype.ext
      ext i j
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      show ρ (SK i j) = SK i j
      simp only [SK, Matrix.map_apply]
      have := RingHom.ext_zmod (ρ.toRingHom.comp ι) ι
      exact congrArg (fun f => f (S i j)) this
    simp only [MulAut.mul_apply]
    rw [dualAut_proj, hgrev, fieldAut_proj, map_inv, hmap, map_inv]

end


section

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem kleinBigInv_projectiveSL_four {n : ℕ} (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (hK2 : Nat.card K = 2 ^ 2) : KleinBigInv (projectiveSL n K) := by
  classical
  intro B hcomm hsq hcard hinn
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have : Finite (MulAut (projectiveSL n K)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.finite_mulAut_projectiveSL n
  have hInnN : ∀ δ ∈ linearAutGroup n K, δ * δ = 1 →
      δ ∈ CFSG.RankThree.PartOne.OutStructure.Inn (projectiveSL n K) := fun δ hδ h2 =>
    CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two hn (not_two_dvd_card_sub_one n)
      δ hδ 1 (by rw [pow_one, pow_two, h2]; exact Subgroup.one_mem _)
  have hE : ∀ α ∈ B, α ∈ semilinearAutGroup n K → α ≠ 1 →
      ∃ (A : GL (Fin n) K) (σ : K ≃+* K), α = conjAut n K A * fieldAut n K σ ∧ σ ≠ 1 ∧
        ∀ x, σ x = x ^ 2 := by
    intro α hαB hαE hα1
    obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hαE
    have hα2 : (conjAut n K A * fieldAut n K σ) ^ 2 = 1 := by rw [pow_two]; exact hsq _ hαB
    have hσ1 : σ ≠ 1 := by
      intro hσ1
      subst hσ1
      rw [map_one, mul_one] at hαB hα1 hα2
      have hDinn := hInnN _ (conjAut_mem_linearAutGroup A) (by rw [← pow_two]; exact hα2)
      have : conjAut n K A ∈ B ⊓ CFSG.RankThree.PartOne.OutStructure.Inn (projectiveSL n K) :=
        ⟨hαB, hDinn⟩
      rw [hinn] at this
      exact hα1 (by simpa using this)
    obtain ⟨-, hσpow, -⟩ := even_linear_field_involution_descent (f := 2) (by norm_num) hK2 hn A σ
      hσ1 hα2
    exact ⟨A, σ, rfl, hσ1, fun x => by simpa using hσpow x⟩
  obtain ⟨α₁, ⟨hα₁B, hα₁E⟩, hα₁1⟩ := exists_mem_inf_of_index_le_two B _ hidx' (by omega)
  obtain ⟨A₁, σ₁, hα₁eq, hσ₁1, hσ₁pow⟩ := hE α₁ hα₁B hα₁E hα₁1
  obtain ⟨β, hβB, hβE⟩ : ∃ β ∈ B, β ∉ semilinearAutGroup n K := by
    by_contra hall
    push Not at hall
    obtain ⟨u, v, hu, hv, huv⟩ := exists_two_ne_one_of_card_eq_four hcard
    have hu' : (u : MulAut (projectiveSL n K)) ≠ 1 := fun h => hu (Subtype.ext h)
    have hv' : (v : MulAut (projectiveSL n K)) ≠ 1 := fun h => hv (Subtype.ext h)
    obtain ⟨Au, σu, hueq, hσu1, hσupow⟩ := hE u u.2 (hall u u.2) hu'
    obtain ⟨Av, σv, hveq, hσv1, hσvpow⟩ := hE v v.2 (hall v v.2) hv'
    have hσuv : σu = σv := RingEquiv.ext fun x => by rw [hσupow, hσvpow]
    subst hσuv
    have hσσ : σu * σu = 1 := by
      ext x
      have : x ^ Nat.card K = x := by
        rw [Nat.card_eq_fintype_card]; exact FiniteField.pow_card x
      simp only [RingAut.mul_apply, hσupow, RingAut.one_apply]
      rw [← pow_mul, hK2] at *
      simpa using this
    have hprod : (u : MulAut (projectiveSL n K)) * v =
        conjAut n K (Au * GeneralLinearGroup.map (σu : K →+* K) Av) := by
      rw [hueq, hveq, conjAut_mul_fieldAut_mul, hσσ, map_one, mul_one]
    have hprodB : (u : MulAut (projectiveSL n K)) * v ∈ B := B.mul_mem u.2 v.2
    have hprodInn := hInnN ((u : MulAut (projectiveSL n K)) * v)
      (by rw [hprod]; exact conjAut_mem_linearAutGroup _) (hsq _ hprodB)
    have : (u : MulAut (projectiveSL n K)) * v ∈ B ⊓
        CFSG.RankThree.PartOne.OutStructure.Inn (projectiveSL n K) := ⟨hprodB, hprodInn⟩
    rw [hinn] at this
    have h1 : (u : MulAut (projectiveSL n K)) * v = 1 := by simpa using this
    apply huv
    have hvv : (v : MulAut (projectiveSL n K)) * v = 1 := hsq _ v.2
    have h2 : (u : MulAut (projectiveSL n K)) = (v : MulAut (projectiveSL n K))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right hvv] at h2
    exact Subtype.ext h2
  obtain ⟨Bm, τ, ε, hε, hβeq⟩ := hgen β
  have hε1 : ε = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with h | h
    · exfalso
      apply hβE
      rw [hβeq, h, pow_zero, mul_one]
      exact mem_semilinearAutGroup_iff.mpr ⟨Bm, τ, rfl⟩
    · exact h
  subst hε1
  rw [pow_one] at hβeq
  obtain ⟨α', C, ρ, hα'B, hα'eq, hρ1⟩ : ∃ (α' : MulAut (projectiveSL n K))
      (C : GL (Fin n) K) (ρ : K ≃+* K), α' ∈ B ∧
      α' = conjAut n K C * fieldAut n K ρ * dualAut n K ∧ ρ ≠ 1 := by
    by_cases hτ : τ = 1
    · refine ⟨α₁ * β, A₁ * GeneralLinearGroup.map (σ₁ : K →+* K) Bm, σ₁,
        B.mul_mem hα₁B hβB, ?_, hσ₁1⟩
      rw [hα₁eq, hβeq, hτ, map_one, mul_one, map_mul]
      have h1 : fieldAut n K σ₁ * conjAut n K Bm =
          conjAut n K (GeneralLinearGroup.map (σ₁ : K →+* K) Bm) * fieldAut n K σ₁ := by
        have := htrans.2.2.1 σ₁ Bm
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      calc conjAut n K A₁ * fieldAut n K σ₁ * (conjAut n K Bm * dualAut n K)
          = conjAut n K A₁ * (fieldAut n K σ₁ * conjAut n K Bm) * dualAut n K := by group
        _ = _ := by rw [h1]; group
    · exact ⟨β, Bm, τ, hβB, hβeq, hτ⟩
  have hα'2 : (conjAut n K C * fieldAut n K ρ * dualAut n K) ^ 2 = 1 := by
    rw [← hα'eq, pow_two]; exact hsq _ hα'B
  obtain ⟨-, -, H, hH⟩ := odd_linear_graph_field_involution_conjugacy Nat.prime_two (f := 2)
    (by norm_num) hK2 hn C ρ hρ1 hα'2
  obtain ⟨y, hy7, hyinv⟩ : ∃ y : projectiveSL n K, orderOf y = 7 ∧
      ∀ ρ : K ≃+* K, (fieldAut n K ρ * dualAut n K) y = y⁻¹ := by
    rcases (by omega : n = 3 ∨ n = 4) with rfl | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := symm3_spec
      exact exists_proj_of_symm hn symm3 h1 h2 h3 h4
    · obtain ⟨h1, h2, h3, h4⟩ := symm4_spec
      exact exists_proj_of_symm hn symm4 h1 h2 h3 h4
  refine ⟨α', hα'B, ?_⟩
  rw [hα'eq, hH]
  exact BigInv.of_inv _ _ y (by norm_num) (Or.inr rfl) hy7 (hyinv ρ)

end


open CFSG.Assembly.LowTwoRank in
theorem kleinBigInv_PSL_ge_three_all {X : Type} [Group X] {n m : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel X .PSL n 2 m) : KleinBigInv X := by
  by_cases hexc : m = 2 ∧ n ≤ 4
  · obtain ⟨hm, hn4⟩ := hexc
    subst hm
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
      rw [← Nat.card_eq_fintype_card, hK])
    have e' : X ≃* projectiveSL n K :=
      (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
    exact KleinBigInv.of_mulEquiv e'.symm (kleinBigInv_projectiveSL_four hn hn4 hK)
  · exact kleinBigInv_PSL_ge_three hn hexc h

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
