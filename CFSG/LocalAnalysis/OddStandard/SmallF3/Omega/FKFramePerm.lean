module

public import TauCeti.Data.Finset.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [FiniteDimensional (ZMod 3) U]
  {R : QuadraticForm (ZMod 3) U}

private lemma fkCoord_equiv (b : Module.Basis (Fin 3) (ZMod 3) U) (e : Equiv.Perm (Fin 3))
    (f : Fin 3 →₀ ZMod 3) (i : Fin 3) :
    b.repr ((b.reindex e).repr.symm f) i = f (e i) := by
  have h : (b.reindex e).repr ((b.reindex e).repr.symm f) = f := LinearEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun g : Fin 3 →₀ ZMod 3 => g (e i)) h
  simpa [Module.Basis.repr_reindex_apply] using h2

private lemma fkPerm_exists {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε))
    (σ : Equiv.Perm (Fin 3)) :
    ∃ g : OGroup R, ∀ i, (g : U ≃ₗ[ZMod 3] U) (fr.b i) = fr.b (σ i) := by
  let e : U ≃ₗ[ZMod 3] U := fr.b.equiv fr.b σ
  have he : ∀ i, e (fr.b i) = fr.b (σ i) := fun i => by simp [e]
  have hcoord : ∀ x i, fr.b.repr (e x) (σ i) = fr.b.repr x i := by
    intro x i
    have h := fkCoord_equiv fr.b σ.symm (fr.b.repr x) (σ i)
    simpa [e, Module.Basis.equiv] using h
  have hmem : e ∈ TauCeti.QuadraticMap.orthogonalGroup R := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have hsum : (∑ i, ε * (fr.b.repr (e x) i) ^ 2) =
        ∑ i, ε * (fr.b.repr x i) ^ 2 := by
      rw [← Equiv.sum_comp σ (fun i => ε * (fr.b.repr (e x) i) ^ 2)]
      exact Finset.sum_congr rfl fun i _ => by rw [hcoord x i]
    rw [fr.map_eq (e x), fr.map_eq x, hsum]
  exact ⟨⟨e, hmem⟩, he⟩

noncomputable def fkPerm {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε))
    (σ : Equiv.Perm (Fin 3)) : OGroup R :=
  Classical.choose (fkPerm_exists fr σ)

theorem fkPerm_basis {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε))
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ((fkPerm fr σ : OGroup R) : U ≃ₗ[ZMod 3] U) (fr.b i) = fr.b (σ i) :=
  Classical.choose_spec (fkPerm_exists fr σ) i

theorem fkPerm_mul {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε))
    (σ τ : Equiv.Perm (Fin 3)) :
    fkPerm fr (σ * τ) = fkPerm fr σ * fkPerm fr τ := by
  apply Subtype.ext; apply fr.b.ext'; intro i
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, fkPerm_basis, fkPerm_basis, fkPerm_basis]
  rfl

theorem fkPerm_one {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε)) :
    fkPerm fr 1 = 1 := by
  apply Subtype.ext; apply fr.b.ext'; intro i
  rw [fkPerm_basis]; simp

theorem fkPerm_mul_signChange {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε))
    (σ : Equiv.Perm (Fin 3)) (J : Finset (Fin 3)) :
    fkPerm fr σ * fr.signChange J =
      fr.signChange (J.map σ.toEmbedding) * fkPerm fr σ := by
  apply Subtype.ext; apply fr.b.ext'; intro i
  rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    fr.signChange_basis J i]
  by_cases hi : i ∈ J
  · have hmem : σ i ∈ J.map σ.toEmbedding := by rw [Finset.mem_map]; exact ⟨i, hi, rfl⟩
    rw [if_pos hi, map_neg, fkPerm_basis, fr.signChange_basis _ (σ i), if_pos hmem]
  · have hmem : σ i ∉ J.map σ.toEmbedding := by
      rw [Finset.mem_map]; rintro ⟨j, hj, hji⟩; exact hi (σ.injective hji ▸ hj)
    rw [if_neg hi, fkPerm_basis, fr.signChange_basis _ (σ i), if_neg hmem]

theorem fkConj_signChange {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε))
    (σ : Equiv.Perm (Fin 3)) (J K : Finset (Fin 3)) :
    (fkPerm fr σ * fr.signChange J) * fr.signChange K *
        (fkPerm fr σ * fr.signChange J)⁻¹ =
      fr.signChange (K.map σ.toEmbedding) := by
  have hJ : (fr.signChange J)⁻¹ = fr.signChange J :=
    inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)
  calc (fkPerm fr σ * fr.signChange J) * fr.signChange K *
        (fkPerm fr σ * fr.signChange J)⁻¹
      = fkPerm fr σ * (fr.signChange J * fr.signChange K * (fr.signChange J)⁻¹) *
          (fkPerm fr σ)⁻¹ := by group
    _ = fkPerm fr σ * fr.signChange K * (fkPerm fr σ)⁻¹ := by
          rw [fr.signChange_comm J K, mul_assoc (fr.signChange K), hJ,
            fr.signChange_mul_self J, mul_one]
    _ = fr.signChange (K.map σ.toEmbedding) := by
          rw [fkPerm_mul_signChange fr σ K, mul_assoc, mul_inv_cancel, mul_one]

theorem fkPerm_sq_eq_one_of_maps_pair (σ : Equiv.Perm (Fin 3)) (K : Finset (Fin 3))
    (hK : K.card = 2) (h : K.map σ.toEmbedding = K) : σ ^ 2 = 1 := by
  revert σ K
  decide

@[expose] noncomputable def fkE {ε : ZMod 3} (fr : PFrame R (Fin 3) (fun _ => ε)) :
    Subgroup (OGroup R) where
  carrier := {g | ∃ J : Finset (Fin 3), Even J.card ∧ g = fr.signChange J}
  one_mem' := ⟨∅, by simp, fr.signChange_empty.symm⟩
  mul_mem' := by
    rintro a b ⟨J, hJ, rfl⟩ ⟨K, hK, rfl⟩
    refine ⟨symmDiff J K, (Finset.even_card_symmDiff_iff J K).mpr (iff_of_true hJ hK),
      fr.signChange_mul J K⟩
  inv_mem' := by
    rintro a ⟨J, hJ, rfl⟩
    exact ⟨J, hJ, inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)⟩

end CFSG.OddStandard.SmallF3.Omega
