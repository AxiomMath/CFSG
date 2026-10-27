module

public import CFSG.LieType.Multipliers.U43Action

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.LieType.Multipliers.U43 Equiv

@[expose] def frobF9 : F9 →+* F9 where
  toFun a := ⟨a.re, -a.im⟩
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem frobF9_frobF9 (a : F9) : frobF9 (frobF9 a) = a := by
  revert a
  decide

theorem frobF9_injective : Function.Injective frobF9 := fun a b h => by
  have := congrArg frobF9 h
  rwa [frobF9_frobF9, frobF9_frobF9] at this

instance : RingHomInvPair frobF9 frobF9 where
  comp_eq := RingHom.ext frobF9_frobF9
  comp_eq₂ := RingHom.ext frobF9_frobF9

instance : RingHomSurjective frobF9 :=
  ⟨fun a => ⟨frobF9 a, frobF9_frobF9 a⟩⟩

@[expose] def thetaSq : F9 := ⟨0, -1⟩

theorem thetaSq_ne_zero : thetaSq ≠ 0 := fun h => by
  have := congrArg F9.im h
  revert this
  decide

@[expose] def diagU (k : Fin 4) : F9 := if k = 2 then thetaSq else 1

theorem diagU_ne_zero (k : Fin 4) : diagU k ≠ 0 := by
  unfold diagU
  split_ifs
  · exact thetaSq_ne_zero
  · exact one_ne_zero

@[expose] def semiFun (v : V) : V := fun k => diagU k * frobF9 (v k)

@[expose] def semiMap : V →ₛₗ[frobF9] V where
  toFun := semiFun
  map_add' v w := by
    funext k
    simp only [semiFun, Pi.add_apply, map_add, mul_add]
  map_smul' c v := by
    funext k
    simp only [semiFun, Pi.smul_apply, smul_eq_mul, map_mul]
    ring

theorem semiMap_injective : Function.Injective semiMap := fun v w h => by
  funext k
  have := congrFun h k
  change diagU k * frobF9 (v k) = diagU k * frobF9 (w k) at this
  exact frobF9_injective (mul_left_cancel₀ (diagU_ne_zero k) this)

@[expose] noncomputable def rhoPt : Pt → Pt := Projectivization.map semiMap semiMap_injective

theorem rhoPt_injective : Function.Injective rhoPt :=
  Projectivization.map_injective (τ := frobF9) semiMap semiMap_injective

theorem rhoPt_bijective : Function.Bijective rhoPt :=
  Finite.injective_iff_bijective.1 rhoPt_injective

@[expose] noncomputable def rhoPerm : Perm (Fin 820) :=
  ptEquiv.permCongr (Equiv.ofBijective rhoPt rhoPt_bijective)

theorem rhoPerm_apply (i : Fin 820) : (rhoPerm i : ℕ) = ptIndex (semiFun (decode i)) := by
  have h1 : rhoPerm i = ptEquiv (rhoPt (ptEquiv.symm i)) := by
    unfold rhoPerm
    rw [Equiv.permCongr_apply, Equiv.ofBijective_apply]
  have hs : ∀ v : V, semiMap v = semiFun v := fun v => rfl
  rw [h1, ptEquiv_symm_apply, rhoPt, Projectivization.map_mk, ptEquiv_apply, ptFin_mk,
    Fin.val_mk, hs]

@[expose] noncomputable def U43Ext : Subgroup (Perm (Fin 820)) :=
  Subgroup.closure (Set.range (psi : X₀ →* Perm (Fin 820)) ∪ {rhoPerm})

end CFSG.EvenSporadicStandard.Fin76b
