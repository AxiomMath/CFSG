module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.Glue

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix TauCeti CFSG.Assembly.LowTwoRank

abbrev SpJ (r : ℕ) : Type := ↥(GLSymplecticFin r (ZMod 2))

@[expose] noncomputable def matJ (r : ℕ) : SpJ r →* Matrix (Fin (r + r)) (Fin (r + r)) (ZMod 2) :=
  (Units.coeHom _).comp (GLSymplecticFin r (ZMod 2)).subtype

theorem matJ_apply {r : ℕ} (x : SpJ r) :
    matJ r x = ((x : GL (Fin (r + r)) (ZMod 2)) : Matrix (Fin (r + r)) (Fin (r + r)) (ZMod 2)) :=
  rfl

theorem matJ_injective (r : ℕ) : Function.Injective (matJ r) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem exists_of_sympl {r : ℕ} {M : Matrix (Fin (r + r)) (Fin (r + r)) (ZMod 2)}
    (h : Mᵀ * JFin r (ZMod 2) * M = JFin r (ZMod 2)) : ∃ x : SpJ r, matJ r x = M := by
  have hneg : (-1 : Matrix (Fin (r + r)) (Fin (r + r)) (ZMod 2)) = 1 := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> decide
  have hJ : JFin r (ZMod 2) * JFin r (ZMod 2) = 1 := by
    exact (JFin_mul_self r (ZMod 2)).trans hneg
  set N : Matrix (Fin (r + r)) (Fin (r + r)) (ZMod 2) :=
    JFin r (ZMod 2) * Mᵀ * JFin r (ZMod 2) with hN
  have hNM : N * M = 1 := by
    have h1 : N * M = JFin r (ZMod 2) * (Mᵀ * JFin r (ZMod 2) * M) := by
      simp [hN, Matrix.mul_assoc]
    rw [h1, h, hJ]
  have hMN : M * N = 1 := mul_eq_one_comm.mpr hNM
  refine ⟨⟨⟨M, N, hMN, hNM⟩, ?_⟩, rfl⟩
  rw [GLSymplecticFin.mem_iff']
  exact h

theorem nonempty_mulEquiv_spJ {G : Type} [Group G] {r : ℕ} (hr : 1 ≤ r)
    (hcl : StatedClassicalModel G .PSp r 2 1) : Nonempty (G ≃* SpJ r) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hcl
  have hcard' : Nat.card K = 2 ^ 1 := by simpa using hcard
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hcard'
  have : NeZero r := ⟨by omega⟩
  have hbij := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
    (r := r) (K := K) le_rfl hcard').1
  let π : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
  obtain ⟨ψ⟩ := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.nonempty_statedSp_mulEquiv_zmod_two
    (K := K) r hcard
  exact ⟨((e'.trans π.symm).trans ψ).trans (CFSG.LieType.Universal.Symplectic.equivStatedSp r
    (ZMod 2)).symm⟩

end CFSG.HardMathSupport.Foote.E27
