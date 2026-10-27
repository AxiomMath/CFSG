module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem eq_one_of_mul_self_eq_one_of_charTwo {L : Type} [Field L] [CharP L 2] {ε : L}
    (h : ε * ε = 1) : ε = 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hsq : (ε + 1) * (ε + 1) = 0 := by
    have : (ε + 1) * (ε + 1) = ε * ε + 2 * ε + 1 := by ring
    rw [this, h, h2, zero_mul, add_zero, ← two_mul, h2, zero_mul]
  have h1 : ε + 1 = 0 := mul_self_eq_zero.1 hsq
  rw [eq_neg_of_add_eq_zero_left h1, CharTwo.neg_eq]

set_option linter.unusedSectionVars false


theorem rootSpan_le_centralizer_canonicalRep {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) {e : Fin τ.rank → ℤ} (he : IsRoot τ e)
    (horth : ∀ γ ∈ Ψ, CFSG.LieType.Steinberg.Adjoint.iform γ e = 0) :
    rootSpan τ L Ψ ≤
      Subgroup.centralizer {canonicalRep (coxeterSystem τ) L (rootReflection e)} := by
  refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨ε, hε, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L (rootReflection e) (hΨ γ hγ)
  have hwγ : rootReflection e • γ = γ := by
    refine rootReflection_smul_of_iform_eq_zero he ?_
    rw [CFSG.LieType.Steinberg.Adjoint.iform_comm]
    exact horth γ hγ
  have hε1 : ε = 1 := eq_one_of_mul_self_eq_one_of_charTwo hε
  have h := hconj c
  rw [hwγ, hε1, one_mul] at h
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  calc pinnedX τ L γ c * canonicalRep (coxeterSystem τ) L (rootReflection e)
      = (canonicalRep (coxeterSystem τ) L (rootReflection e) * pinnedX τ L γ c *
          (canonicalRep (coxeterSystem τ) L (rootReflection e))⁻¹) *
        canonicalRep (coxeterSystem τ) L (rootReflection e) := by rw [h]
    _ = canonicalRep (coxeterSystem τ) L (rootReflection e) * pinnedX τ L γ c := by group

theorem rootChar_eq_one_of_mem_rootSpan_of_orth {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (a : Fin τ.rank → Lˣ) (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hd : rootDiagUnit τ a ∈ rootSpan τ L Ψ) {e : Fin τ.rank → ℤ} (he : IsRoot τ e)
    (horth : ∀ γ ∈ Ψ, CFSG.LieType.Steinberg.Adjoint.iform γ e = 0) : rootChar a e = 1 := by
  classical
  set n := canonicalRep (coxeterSystem τ) L (rootReflection e) with hn
  set d := rootDiagUnit τ a with hd'
  have hnd : d * n = n * d := by
    have := rootSpan_le_centralizer_canonicalRep (L := L) Ψ hΨ he horth hd
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  obtain ⟨ε, hε, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L (rootReflection e) he
  have hε1 : ε = 1 := eq_one_of_mul_self_eq_one_of_charTwo hε
  have hne : ∀ c : L, n * pinnedX τ L e c * n⁻¹ = pinnedX τ L (-e) c := by
    intro c
    rw [hn, hconj c, rootReflection_smul_self he, hε1, one_mul]
  have h1 : n * (d * pinnedX τ L e 1 * d⁻¹) * n⁻¹ =
      pinnedX τ L (-e) ((rootChar a e : L) * 1) := by
    rw [hd', rootDiagUnit_conj_pinnedX a he 1, hne]
  have h2 : n * (d * pinnedX τ L e 1 * d⁻¹) * n⁻¹ =
      pinnedX τ L (-e) ((rootChar a (-e) : L) * 1) := by
    have hnd' : n * d = d * n := hnd.symm
    have hdn' : d⁻¹ * n⁻¹ = n⁻¹ * d⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hnd]
    calc n * (d * pinnedX τ L e 1 * d⁻¹) * n⁻¹
        = d * (n * pinnedX τ L e 1 * n⁻¹) * d⁻¹ := by
          calc n * (d * pinnedX τ L e 1 * d⁻¹) * n⁻¹
              = (n * d) * pinnedX τ L e 1 * (d⁻¹ * n⁻¹) := by group
            _ = (d * n) * pinnedX τ L e 1 * (n⁻¹ * d⁻¹) := by rw [hnd', hdn']
            _ = d * (n * pinnedX τ L e 1 * n⁻¹) * d⁻¹ := by group
      _ = d * pinnedX τ L (-e) 1 * d⁻¹ := by rw [hne]
      _ = pinnedX τ L (-e) ((rootChar a (-e) : L) * 1) := by
          rw [hd', rootDiagUnit_conj_pinnedX a (IsRoot.neg he) 1]
  have h3 : ((rootChar a e : Lˣ) : L) = ((rootChar a (-e) : Lˣ) : L) := by
    have := pinnedX_injective τ L (-e) (h1.symm.trans h2)
    simpa using this
  have hinv : rootChar a (-e) = (rootChar a e)⁻¹ := by
    have h := rootChar_add a e (-e)
    rw [add_neg_cancel, rootChar_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  rw [hinv] at h3
  have h4 : ((rootChar a e : Lˣ) : L) * ((rootChar a e : Lˣ) : L) = 1 := by
    calc ((rootChar a e : Lˣ) : L) * ((rootChar a e : Lˣ) : L)
        = ((rootChar a e : Lˣ) : L) * (((rootChar a e)⁻¹ : Lˣ) : L) := by rw [← h3]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Units.ext (eq_one_of_mul_self_eq_one_of_charTwo h4)

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
