module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def sec4ISgn (u : ZMod 2) : (ZMod 3)ˣ := if u = 0 then 1 else -1

theorem sec4ISgn_zero : sec4ISgn 0 = 1 := by
  decide

theorem sec4ISgn_add (u w : ZMod 2) : sec4ISgn (u + w) = sec4ISgn u * sec4ISgn w := by
  revert u w
  decide

theorem sec4ISgn_injective : Function.Injective sec4ISgn := by
  decide

theorem sec4ISgn_sq (u : ZMod 2) : ((sec4ISgn u : (ZMod 3)ˣ) : ZMod 3) ^ 2 = 1 := by
  revert u
  decide

@[expose] noncomputable def sec4IMonoLin (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7))
    (u : Fin 7 → ZMod 2) : V ≃ₗ[ZMod 3] V :=
  fr.b.equiv (fr.b.unitsSMul fun j => sec4ISgn (u (σ.symm j))) σ

theorem sec4IMonoLin_apply (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2)
    (i : Fin 7) :
    sec4IMonoLin fr σ u (fr.b i) = ((sec4ISgn (u i) : (ZMod 3)ˣ) : ZMod 3) • fr.b (σ i) := by
  simp only [sec4IMonoLin, Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply,
    Equiv.symm_apply_apply, Units.smul_def]

theorem sec4IMonoLin_map (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2)
    (x : V) : Q (sec4IMonoLin fr σ u x) = Q x := by
  have h1 : sec4IMonoLin fr σ u x = ∑ j, (fr.b.repr x (σ.symm j) *
      ((sec4ISgn (u (σ.symm j)) : (ZMod 3)ˣ) : ZMod 3)) • fr.b j := by
    conv_lhs => rw [← fr.b.sum_repr x]
    rw [map_sum]
    simp only [map_smul, sec4IMonoLin_apply, smul_smul]
    rw [← Equiv.sum_comp σ.symm]
    simp only [Equiv.apply_symm_apply]
  rw [h1, fr.map_eq, fr.map_eq x, Module.Basis.repr_sum_self]
  congr 1
  rw [← Equiv.sum_comp σ.symm (fun i => fr.b.repr x i ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, sec4ISgn_sq, mul_one]

@[expose] noncomputable def sec4IMono (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7))
    (u : Fin 7 → ZMod 2) : OGroup Q :=
  ⟨sec4IMonoLin fr σ u,
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mpr fun x => sec4IMonoLin_map fr σ u x⟩

theorem sec4IMono_apply (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2)
    (i : Fin 7) :
    (sec4IMono fr σ u : V ≃ₗ[ZMod 3] V) (fr.b i) =
      ((sec4ISgn (u i) : (ZMod 3)ˣ) : ZMod 3) • fr.b (σ i) :=
  sec4IMonoLin_apply fr σ u i

theorem sec4I_ogroup_ext (fr : Sec4IFrame Q) {g h : OGroup Q}
    (hgh : ∀ i, (g : V ≃ₗ[ZMod 3] V) (fr.b i) = (h : V ≃ₗ[ZMod 3] V) (fr.b i)) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact fr.b.ext hgh

theorem sec4IMono_mul (fr : Sec4IFrame Q) (σ τ : Equiv.Perm (Fin 7)) (u w : Fin 7 → ZMod 2) :
    sec4IMono fr σ u * sec4IMono fr τ w = sec4IMono fr (σ * τ) (fun i => w i + u (τ i)) := by
  apply sec4I_ogroup_ext fr
  intro i
  change (sec4IMono fr σ u : V ≃ₗ[ZMod 3] V) ((sec4IMono fr τ w : V ≃ₗ[ZMod 3] V) (fr.b i)) = _
  rw [sec4IMono_apply, map_smul, sec4IMono_apply, smul_smul, sec4IMono_apply, sec4ISgn_add,
    Units.val_mul, Equiv.Perm.mul_apply, mul_comm]

theorem sec4IMono_one (fr : Sec4IFrame Q) : sec4IMono fr 1 0 = 1 := by
  apply sec4I_ogroup_ext fr
  intro i
  rw [sec4IMono_apply]
  simp [sec4ISgn_zero]

theorem sec4IMono_injective (fr : Sec4IFrame Q) {σ τ : Equiv.Perm (Fin 7)}
    {u w : Fin 7 → ZMod 2} (h : sec4IMono fr σ u = sec4IMono fr τ w) : σ = τ ∧ u = w := by
  have key : ∀ i, σ i = τ i ∧ u i = w i := by
    intro i
    have h1 := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) (fr.b i)) h
    simp only [sec4IMono_apply] at h1
    have hc : ((sec4ISgn (u i) : (ZMod 3)ˣ) : ZMod 3) ≠ 0 := (sec4ISgn (u i)).ne_zero
    have hσ : σ i = τ i := by
      by_contra hne
      have h2 := congrArg (fun v => fr.b.repr v (σ i)) h1
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        if_true, if_neg (Ne.symm hne), smul_eq_mul, mul_one, mul_zero] at h2
      exact hc h2
    rw [hσ] at h1
    have h3 := congrArg (fun v => fr.b.repr v (τ i)) h1
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      if_true, smul_eq_mul, mul_one] at h3
    exact ⟨hσ, sec4ISgn_injective (Units.ext h3)⟩
  exact ⟨Equiv.ext fun i => (key i).1, funext fun i => (key i).2⟩

@[expose] noncomputable def sec4IT (fr : Sec4IFrame Q) (u : Fin 7 → ZMod 2) : OGroup Q :=
  sec4IMono fr 1 u

@[expose] noncomputable def sec4IP (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) : OGroup Q :=
  sec4IMono fr σ 0

theorem sec4IT_add (fr : Sec4IFrame Q) (u w : Fin 7 → ZMod 2) :
    sec4IT fr (u + w) = sec4IT fr u * sec4IT fr w := by
  change sec4IMono fr 1 (u + w) = sec4IMono fr 1 u * sec4IMono fr 1 w
  rw [sec4IMono_mul, one_mul]
  congr 1
  funext i
  simp [add_comm]

theorem sec4IT_zero (fr : Sec4IFrame Q) : sec4IT fr 0 = 1 :=
  sec4IMono_one fr

theorem sec4IT_mul_self (fr : Sec4IFrame Q) (u : Fin 7 → ZMod 2) :
    sec4IT fr u * sec4IT fr u = 1 := by
  rw [← sec4IT_add]
  have h : u + u = 0 := by
    funext i
    have : ∀ x : ZMod 2, x + x = 0 := by decide
    exact this (u i)
  rw [h, sec4IT_zero]

theorem sec4IP_mul (fr : Sec4IFrame Q) (σ τ : Equiv.Perm (Fin 7)) :
    sec4IP fr σ * sec4IP fr τ = sec4IP fr (σ * τ) := by
  change sec4IMono fr σ 0 * sec4IMono fr τ 0 = sec4IMono fr (σ * τ) 0
  rw [sec4IMono_mul]
  congr 1

theorem sec4IP_one (fr : Sec4IFrame Q) : sec4IP fr 1 = 1 :=
  sec4IMono_one fr

theorem sec4IMono_eq_P_mul_T (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2) :
    sec4IMono fr σ u = sec4IP fr σ * sec4IT fr u := by
  change sec4IMono fr σ u = sec4IMono fr σ 0 * sec4IMono fr 1 u
  rw [sec4IMono_mul, mul_one]
  congr 1
  funext i
  simp

theorem sec4IMono_mul_T (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) (u s : Fin 7 → ZMod 2) :
    sec4IMono fr σ u * sec4IT fr s = sec4IT fr (permVec σ s) * sec4IMono fr σ u := by
  change sec4IMono fr σ u * sec4IMono fr 1 s = sec4IMono fr 1 (permVec σ s) * sec4IMono fr σ u
  rw [sec4IMono_mul, sec4IMono_mul, mul_one, one_mul]
  congr 1
  funext i
  simp [permVec, add_comm]

theorem sec4IMono_conj_T (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) (u s : Fin 7 → ZMod 2) :
    sec4IMono fr σ u * sec4IT fr s * (sec4IMono fr σ u)⁻¹ = sec4IT fr (permVec σ s) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact sec4IMono_mul_T fr σ u s

theorem sec4IT_apply_basis (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) (i : Fin 7) :
    (sec4IT fr s : V ≃ₗ[ZMod 3] V) (fr.b i) = ((sec4ISgn (s i) : (ZMod 3)ˣ) : ZMod 3) • fr.b i := by
  rw [sec4IT, sec4IMono_apply]
  rfl

theorem sec4IT_repr (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) (x : V) (k : Fin 7) :
    fr.b.repr ((sec4IT fr s : V ≃ₗ[ZMod 3] V) x) k =
      ((sec4ISgn (s k) : (ZMod 3)ˣ) : ZMod 3) * fr.b.repr x k := by
  have h : (sec4IT fr s : V ≃ₗ[ZMod 3] V) x = ∑ i, (fr.b.repr x i *
      ((sec4ISgn (s i) : (ZMod 3)ˣ) : ZMod 3)) • fr.b i := by
    conv_lhs => rw [← fr.b.sum_repr x]
    rw [map_sum]
    simp only [map_smul, sec4IT_apply_basis, smul_smul]
  rw [h, Module.Basis.repr_sum_self, mul_comm]

end CFSG.OddStandard.SmallF3.Omega
