module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Centralizer
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting

public section

namespace CFSG.LinearAlgebra

open Matrix Polynomial CFSG.RepresentationTheory

theorem isIrreducibleMatrixRep_zpowers_of_orderOf_eq
    {K : Type*} [Field K] [Fintype K] {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = n)
    {u : GL (Fin n) K} (hu : orderOf u = p) :
    IsIrreducibleMatrixRep (Subgroup.zpowers u).subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M : Matrix (Fin n) (Fin n) K := (u : Matrix (Fin n) (Fin n) K)
  have hMp : M ^ p = 1 := by
    have h1 : u ^ p = 1 := by
      rw [← hu]
      exact pow_orderOf_eq_one u
    simpa [M] using
      congrArg (fun v : GL (Fin n) K => (v : Matrix (Fin n) (Fin n) K)) h1
  have hM1 : M ≠ 1 := by
    intro h
    have hu1 : u = 1 := Units.ext h
    have h1 : orderOf u = 1 := by rw [hu1, orderOf_one]
    rw [hu] at h1
    exact hp.one_lt.ne' h1
  obtain ⟨hirr, hdeg⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.minpoly_irreducible_natDegree_eq
      (K := K) (p := p) (n := n) hn hord hMp hM1
  have hirr' : Irreducible (minpoly K (Matrix.toLin' M)) := by
    rw [Matrix.minpoly_toLin']
    exact hirr
  have hdeg' : (minpoly K (Matrix.toLin' M)).natDegree = Module.finrank K (Fin n → K) := by
    rw [Matrix.minpoly_toLin', hdeg, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hWE : ∀ w ∈ W, Matrix.toLin' M w ∈ W := by
      intro w hw
      have hmem : (u : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W :=
        hW ⟨u, Subgroup.mem_zpowers u⟩ w hw
      simpa [M, Matrix.toLin'_apply] using hmem
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hbot
    let g : Module.End K W := (Matrix.toLin' M).restrict hWE
    have hzero : aeval g (minpoly K (Matrix.toLin' M)) = 0 := by
      refine LinearMap.ext fun w => Subtype.ext ?_
      have h : ∀ P : K[X],
          ((aeval g P) w : Fin n → K) = aeval (Matrix.toLin' M) P (w : Fin n → K) := by
        intro P
        induction P using Polynomial.induction_on' with
        | add P Q hP hQ => simp [map_add, hP, hQ]
        | monomial m a =>
            simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply,
              LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul]
            congr 1
            rw [show g = (Matrix.toLin' M).restrict hWE from rfl,
              Module.End.pow_restrict m hWE]
            rfl
      rw [h (minpoly K (Matrix.toLin' M))]
      exact LinearMap.congr_fun (minpoly.aeval K (Matrix.toLin' M)) (w : Fin n → K)
    have hdvd : minpoly K g ∣ minpoly K (Matrix.toLin' M) := minpoly.dvd K g hzero
    obtain ⟨q, hq⟩ := hdvd
    have hmon : (minpoly K g).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral g)
    have hgne : minpoly K g ≠ 1 := minpoly.ne_one K g
    rcases hirr'.isUnit_or_isUnit hq with h | h
    · exact absurd (hmon.eq_one_of_isUnit h) hgne
    · have hq0 : q.natDegree = 0 := natDegree_eq_zero_of_isUnit h
      have hqne : q ≠ 0 := h.ne_zero
      have h5 : (minpoly K g).natDegree = Module.finrank K (Fin n → K) := by
        rw [← hdeg', hq, natDegree_mul hmon.ne_zero hqne, hq0, add_zero]
      have h6 : (minpoly K g).natDegree ≤ Module.finrank K W := by
        have := natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly g)
          (LinearMap.charpoly_monic g).ne_zero
        rwa [LinearMap.charpoly_natDegree] at this
      exact Submodule.eq_top_of_finrank_eq
        (le_antisymm (Submodule.finrank_le W) (h5 ▸ h6))

theorem isIrreducibleMatrixRep_zpowers_of_orderOf_eq_seven
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    {u : GL (Fin 3) K} (hu : orderOf u = 7) :
    IsIrreducibleMatrixRep (Subgroup.zpowers u).subtype := by
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hK]
  have hord : orderOf ((Fintype.card K : ℕ) : ZMod 7) = 3 := by
    rw [hcard]
    exact orderOf_eq_prime (by decide : (4 : ZMod 7) ^ 3 = 1) (by decide : (4 : ZMod 7) ≠ 1)
  exact isIrreducibleMatrixRep_zpowers_of_orderOf_eq (K := K) (p := 7) (n := 3)
    Nat.prime_seven (by norm_num) hord hu

end CFSG.LinearAlgebra
