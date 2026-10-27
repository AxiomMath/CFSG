module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarCent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.HbarCoords

open Subgroup Matrix

variable {G : Type} [Group G] {z : G} {T : Subgroup G} {κ : GL (Fin 3) (ZMod 2) →* G}
  {E₀ : Subgroup G} {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}

section Coord6

variable (cT) in
@[expose] def cT6 (x : Fin 6 → ZMod 2) : G :=
  cT (fun i => x (Fin.castAdd 3 i)) (fun i => x (Fin.natAdd 3 i))

theorem cT6_append (v w : Fin 3 → ZMod 2) : cT6 cT (Fin.append v w) = cT v w := by
  simp only [cT6, Fin.append_left, Fin.append_right]

theorem exists_eq_append (x : Fin 6 → ZMod 2) : ∃ v w : Fin 3 → ZMod 2, x = Fin.append v w :=
  ⟨_, _, (Fin.append_castAdd_natAdd (m := 3) (n := 3) (f := x)).symm⟩

variable (hc : ModIso.TCoords z T κ E₀ cT)
include hc

theorem cT6_mem (x : Fin 6 → ZMod 2) : cT6 cT x ∈ T := hc.mem _ _

theorem cT6_add (x y : Fin 6 → ZMod 2) : cT6 cT (x + y) = cT6 cT x * cT6 cT y :=
  hc.add _ _ _ _

theorem cT6_injective : Function.Injective (cT6 cT) := by
  intro x y h
  obtain ⟨v, w, rfl⟩ := exists_eq_append x
  obtain ⟨v', w', rfl⟩ := exists_eq_append y
  rw [cT6_append, cT6_append] at h
  obtain ⟨h1, h2⟩ := (cT_eq_iff hc).1 h
  rw [h1, h2]

theorem exists_cT6_eq {t : G} (ht : t ∈ T) : ∃ x, cT6 cT x = t := by
  obtain ⟨v, w, rfl⟩ := hc.surj t ht
  exact ⟨Fin.append v w, cT6_append v w⟩

end Coord6

section Psi

variable (hc : ModIso.TCoords z T κ E₀ cT)

@[expose] noncomputable def coordEquiv : (Fin 6 → ZMod 2) ≃ T :=
  Equiv.ofBijective (fun x => ⟨cT6 cT x, cT6_mem hc x⟩)
    ⟨fun _ _ h => cT6_injective hc (congrArg Subtype.val h), fun t => by
      obtain ⟨x, hx⟩ := exists_cT6_eq hc t.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem coe_coordEquiv (x : Fin 6 → ZMod 2) : (coordEquiv hc x : G) = cT6 cT x := rfl

theorem coordEquiv_add (x y : Fin 6 → ZMod 2) :
    coordEquiv hc (x + y) = coordEquiv hc x * coordEquiv hc y :=
  Subtype.ext (cT6_add hc x y)

theorem coordEquiv_symm_mul (s t : T) :
    (coordEquiv hc).symm (s * t) = (coordEquiv hc).symm s + (coordEquiv hc).symm t := by
  apply (coordEquiv hc).injective
  rw [coordEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[expose] noncomputable def addOf (φ : MulAut T) : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2) where
  toEquiv := ((coordEquiv hc).trans φ.toEquiv).trans (coordEquiv hc).symm
  map_add' x y := by
    show (coordEquiv hc).symm (φ (coordEquiv hc (x + y))) =
      (coordEquiv hc).symm (φ (coordEquiv hc x)) + (coordEquiv hc).symm (φ (coordEquiv hc y))
    rw [coordEquiv_add, map_mul, coordEquiv_symm_mul]

@[expose] noncomputable def linOf (φ : MulAut T) :
    (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (addOf hc φ).toLinearEquiv (fun c x => ZMod.map_smul (addOf hc φ) c x)

theorem linOf_apply (φ : MulAut T) (x : Fin 6 → ZMod 2) :
    linOf hc φ x = (coordEquiv hc).symm (φ (coordEquiv hc x)) := rfl

@[expose] noncomputable def autOf (f : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :
    MulAut T where
  toEquiv := ((coordEquiv hc).symm.trans f.toEquiv).trans (coordEquiv hc)
  map_mul' s t := by
    show coordEquiv hc (f ((coordEquiv hc).symm (s * t))) =
      coordEquiv hc (f ((coordEquiv hc).symm s)) * coordEquiv hc (f ((coordEquiv hc).symm t))
    rw [coordEquiv_symm_mul, map_add, coordEquiv_add]

theorem autOf_apply (f : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) (t : T) :
    autOf hc f t = coordEquiv hc (f ((coordEquiv hc).symm t)) := rfl

@[expose] noncomputable def autLin :
    MulAut T ≃* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) where
  toFun := linOf hc
  invFun := autOf hc
  left_inv φ := by
    refine MulEquiv.ext fun t => ?_
    rw [autOf_apply, linOf_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  right_inv f := by
    refine LinearEquiv.ext fun x => ?_
    rw [linOf_apply, autOf_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  map_mul' φ ψ := by
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, linOf_apply, linOf_apply, linOf_apply, MulAut.mul_apply,
      Equiv.apply_symm_apply]

@[expose] noncomputable def psi : MulAut T ≃* GL (Fin 6) (ZMod 2) :=
  (autLin hc).trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Fin 6 → ZMod 2)).symm.trans Matrix.GeneralLinearGroup.toLin.symm)

theorem psi_mulVec (φ : MulAut T) (x : Fin 6 → ZMod 2) :
    ((psi hc φ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x =
      (coordEquiv hc).symm (φ (coordEquiv hc x)) := by
  have h1 : Matrix.GeneralLinearGroup.toLin (psi hc φ) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 6 → ZMod 2)).symm
        (autLin hc φ) := by
    simp only [psi, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have h2 := congrArg (fun g => LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Fin 6 → ZMod 2) g x) h1
  simp only [MulEquiv.apply_symm_apply] at h2
  rw [← linOf_apply]
  exact h2

theorem psi_apply (φ : MulAut T) (x : Fin 6 → ZMod 2) :
    ((φ (coordEquiv hc x) : T) : G) =
      cT6 cT ((psi hc φ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x) := by
  rw [psi_mulVec, ← coe_coordEquiv hc, Equiv.apply_symm_apply]

theorem psi_apply_cT (φ : MulAut T) (v w : Fin 3 → ZMod 2) :
    ((φ ⟨cT v w, hc.mem v w⟩ : T) : G) =
      cT6 cT ((psi hc φ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w) := by
  have : (⟨cT v w, hc.mem v w⟩ : T) = coordEquiv hc (Fin.append v w) :=
    Subtype.ext (cT6_append v w).symm
  rw [this, psi_apply]

theorem psi_eq_of {φ : MulAut T} {M : GL (Fin 6) (ZMod 2)}
    (h : ∀ v w, ((φ ⟨cT v w, hc.mem v w⟩ : T) : G) =
      cT6 cT ((M : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w)) :
    psi hc φ = M := by
  have hx : ∀ x, ((psi hc φ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x =
      (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x := by
    intro x
    apply cT6_injective hc
    obtain ⟨v, w, rfl⟩ := exists_eq_append x
    rw [← psi_apply_cT, h]
  apply Units.ext
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun x => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hx]

theorem conj_eq_psi_normAct (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2) :
    (g : G) * cT v w * (g : G)⁻¹ =
      cT6 cT ((psi hc (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
        Fin.append v w) := by
  rw [← psi_apply_cT hc, AltStdBal.coe_normAct_apply]

theorem psi_normAct_eq_of {g : normalizer (T : Set G)} {M : GL (Fin 6) (ZMod 2)}
    (h : ∀ v w, (g : G) * cT v w * (g : G)⁻¹ =
      cT6 cT ((M : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w)) :
    psi hc (AltStdBal.normAct T g) = M :=
  psi_eq_of hc fun v w => (AltStdBal.coe_normAct_apply T g _).trans (h v w)

end Psi

end CFSG.OddStandard.AltStdSmall4.HbarCoords
