module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODEigen
public import Mathlib.FieldTheory.KummerPolynomial

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Polynomial Module

theorem exists_monomial_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {p : ℕ} [NeZero p] (hp : p.Prime) {ζ : K} (hζ : ∀ b : K, b ^ p ≠ ζ)
    {T : Module.End K V} (hT : T ^ p = algebraMap K (Module.End K V) ζ) :
    ∃ (m : ℕ) (b : Basis (Fin p × Fin m) K V) (u : Fin p × Fin m → K),
      ∀ x : Fin p × Fin m, T (b x) = u x • b (x.1 + 1, x.2) := by
  haveI : Fact (Irreducible (X ^ p - C ζ)) := ⟨X_pow_sub_C_irreducible_of_prime hp hζ⟩
  have hf0 : (X ^ p - C ζ : K[X]) ≠ 0 := (monic_X_pow_sub_C ζ hp.ne_zero).ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  have hdim : pb.dim = p := by simp [pb, natDegree_X_pow_sub_C]
  have hroot : aeval T (X ^ p - C ζ : K[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hT, sub_self]
  let φ : AdjoinRoot (X ^ p - C ζ : K[X]) →+* Module.End K V :=
    Ideal.Quotient.lift (Ideal.span {(X ^ p - C ζ : K[X])}) (aeval T : K[X] →ₐ[K] _).toRingHom
      (fun a ha => by
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 ha
        change aeval T ((X ^ p - C ζ) * g) = 0
        rw [map_mul, hroot, zero_mul])
  have hφmk : ∀ g : K[X], φ (AdjoinRoot.mk (X ^ p - C ζ : K[X]) g) = aeval T g := fun g => rfl
  letI : Module (AdjoinRoot (X ^ p - C ζ : K[X])) V := Module.compHom V φ
  have hsmul : ∀ (e : AdjoinRoot (X ^ p - C ζ : K[X])) (v : V), e • v = φ e v := fun e v => rfl
  haveI : IsScalarTower K (AdjoinRoot (X ^ p - C ζ : K[X])) V := by
    refine IsScalarTower.of_algebraMap_smul fun r v => ?_
    rw [hsmul, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, hφmk, aeval_C]
    rfl
  haveI : Module.Finite (AdjoinRoot (X ^ p - C ζ : K[X])) V :=
    Module.Finite.of_restrictScalars_finite K _ V
  let c := Module.Free.chooseBasis (AdjoinRoot (X ^ p - C ζ : K[X])) V
  let ι := Module.Free.ChooseBasisIndex (AdjoinRoot (X ^ p - C ζ : K[X])) V
  let e1 : Fin p ≃ Fin pb.dim := finCongr hdim.symm
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let b : Basis (Fin p × Fin (Fintype.card ι)) K V :=
    (pb.basis.smulTower c).reindex (Equiv.prodCongr e1.symm eι)
  refine ⟨Fintype.card ι, b, fun x => if (x.1 : ℕ) + 1 < p then 1 else ζ, fun ⟨j, i⟩ => ?_⟩
  have hb : ∀ (j : Fin p) (i : Fin (Fintype.card ι)), b (j, i) =
      AdjoinRoot.root (X ^ p - C ζ : K[X]) ^ (j : ℕ) • c (eι.symm i) := by
    intro j i
    simp [b, Basis.reindex_apply, Basis.smulTower_apply, e1, pb, PowerBasis.coe_basis]
  have hTv : ∀ v : V, T v = AdjoinRoot.root (X ^ p - C ζ : K[X]) • v := by
    intro v
    rw [hsmul, AdjoinRoot.root, hφmk, aeval_X]
  have hrp : AdjoinRoot.root (X ^ p - C ζ : K[X]) ^ p = algebraMap K _ ζ := by
    have := AdjoinRoot.eval₂_root (X ^ p - C ζ : K[X])
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at this
    rw [AdjoinRoot.algebraMap_eq]
    exact sub_eq_zero.1 this
  have hval : ((j + 1 : Fin p) : ℕ) = ((j : ℕ) + 1) % p := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hp.one_lt]
  rw [hb, hTv, smul_smul, ← pow_succ']
  change _ = (if (j : ℕ) + 1 < p then (1 : K) else ζ) • b (j + 1, i)
  rw [hb (j + 1) i, hval]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h, one_smul]
  · have hj : (j : ℕ) + 1 = p := by omega
    rw [hj, hrp, Nat.mod_self, pow_zero]
    have h1 := algebraMap_smul (AdjoinRoot (X ^ p - C ζ : K[X])) ζ (c (eι.symm i))
    rw [AdjoinRoot.algebraMap_eq] at h1
    simpa using h1

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC
