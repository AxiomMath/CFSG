module

public import CFSG.LieType.AlgebraicGroups.GLFrobeniusFixedField
public import CFSG.LocalAnalysis.UniquenessCase.UCInspConjN
public import CFSG.LocalAnalysis.StandardType.GGCentA2StdAux
public import CFSG.RankThree.Classical2.SLnFrobeniusFormFixed

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.AlgebraicGroups

open Matrix CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open CFSG.Open
open CFSG.RankThree.Classical2 (invTransposeSL statedSUToSL
  exists_isAlgClosure_powFixedSubfield eqLocus_conjSLn_frobenius_unitary_canonical)
open scoped MatrixGroups

variable {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}

theorem sl_inner_frobenius_fixed_field (p e : ℕ) [Fact p.Prime] [CharP k p]
    (he : 1 ≤ e) (g : GeneralLinearGroup (Fin n) k) :
    let Φ := SpecialLinearGroup.map (n := Fin n) (iterateFrobenius k p e)
    let Ψ := (conjSLn g).comp Φ
    let K := (iterateFrobenius k p e).eqLocusField (RingHom.id k)
    Nat.card K = p ^ e ∧
      Nonempty (SpecialLinearGroup (Fin n) K ≃* Ψ.eqLocus (MonoidHom.id _)) := by
  intro Φ Ψ K
  obtain ⟨h, hh⟩ := gl_frobenius_inner_twist (ι := Fin n) p e he g
  let c := conjSLnEquiv h
  have hψ : ∀ x : SpecialLinearGroup (Fin n) k, Ψ x = c.symm (Φ (c x)) := by
    intro x
    apply Subtype.ext
    exact congrArg (fun a : GeneralLinearGroup (Fin n) k =>
      (a : Matrix (Fin n) (Fin n) k)) (hh (SpecialLinearGroup.toGL x))
  have hfixed : ∀ x : SpecialLinearGroup (Fin n) k, Ψ x = x ↔ Φ (c x) = c x := by
    intro x
    rw [hψ]
    constructor
    · intro hx
      simpa only [MulEquiv.apply_symm_apply] using congrArg c hx
    · intro hx
      apply c.injective
      simpa only [MulEquiv.apply_symm_apply] using hx
  let E : Ψ.eqLocus (MonoidHom.id _) ≃* Φ.eqLocus (MonoidHom.id _) :=
    { toFun := fun x => ⟨c x, (hfixed x).1 x.property⟩
      invFun := fun x => ⟨c.symm x, (hfixed (c.symm x)).2 (by
        have hx : Φ (x : SpecialLinearGroup (Fin n) k) = x := x.property
        simpa only [MulEquiv.apply_symm_apply] using hx)⟩
      left_inv := fun x => Subtype.ext (c.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (c.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext
        (map_mul c (x : SpecialLinearGroup (Fin n) k) (y : SpecialLinearGroup (Fin n) k)) }
  refine ⟨(gl_inner_frobenius_fixed_field (ι := Fin n) p e he g).1, ?_⟩
  have hK : CFSG.StandardType.NTPlane.ntpA2S_fixedField (iterateFrobenius k p e) = K := by
    ext a
    rw [CFSG.StandardType.NTPlane.ntpA2S_mem_fixedField]
    rfl
  have E0 := CFSG.StandardType.NTPlane.ntpA2S_splitFixedEquiv n (iterateFrobenius k p e)
  rw [hK] at E0
  exact ⟨E0.trans E.symm⟩

theorem sl_inner_frobenius_fixed_field_extension
    {F : Type} [Field F] [Finite F] [Algebra F k]
    (p f m : ℕ) [Fact p.Prime] [CharP k p]
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hF : Nat.card F = p ^ f)
    (g : GeneralLinearGroup (Fin n) k) :
    let Φ := SpecialLinearGroup.map (n := Fin n) (iterateFrobenius k p (f * m))
    let Ψ := (conjSLn g).comp Φ
    let K := (iterateFrobenius k p (f * m)).eqLocusField (RingHom.id k)
    ∃ ρ : F →+* K, K.subtype.comp ρ = algebraMap F k ∧
      Nat.card K = Nat.card F ^ m ∧
      Nonempty (SpecialLinearGroup (Fin n) K ≃* Ψ.eqLocus (MonoidHom.id _)) := by
  intro Φ Ψ K
  obtain ⟨ρ, hρ, hcard, -⟩ :=
    gl_inner_frobenius_fixed_field_extension (ι := Fin n) p f m hf hm hF g
  refine ⟨ρ, hρ, hcard, ?_⟩
  exact (sl_inner_frobenius_fixed_field p (f * m) (by nlinarith) g).2

end CFSG.LieType.AlgebraicGroups
