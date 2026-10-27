module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_simAct_mem_omegaGroup (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (γ : simGroup Q) {t : OGroup Q}
    (ht : t ∈ omegaGroup hQ) : simAct Q γ t ∈ omegaGroup hQ := by
  rw [omegaGroup_eq_commutator hQ h2, commutator_def] at ht ⊢
  have hmap := Subgroup.map_commutator (H₁ := ⊤) (H₂ := ⊤) (simAct Q γ).toMonoidHom
  have htop : (⊤ : Subgroup (OGroup Q)).map (simAct Q γ).toMonoidHom = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top_of_surjective _ (simAct Q γ).surjective
  rw [htop] at hmap
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ ht

theorem ff_projSimAct_mem_omegaProj (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (x : ProjSim Q) {w : ProjOrth Q}
    (hw : w ∈ omegaProj hQ) : projSimAct Q x w ∈ omegaProj hQ := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨t, ht, rfl⟩ := (mem_omegaProj_iff hQ).mp hw
  rw [projSimAct_mk, projActAux_toProj]
  exact (mem_omegaProj_iff hQ).mpr ⟨_, ff_simAct_mem_omegaGroup hQ h2 γ ht, rfl⟩

@[expose] noncomputable def ffOmegaAutOf (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (x : ProjSim Q) : MulAut (omegaProj hQ) where
  toFun w := ⟨projSimAct Q x w, ff_projSimAct_mem_omegaProj hQ h2 x w.2⟩
  invFun w := ⟨projSimAct Q x⁻¹ w, ff_projSimAct_mem_omegaProj hQ h2 x⁻¹ w.2⟩
  left_inv w := by
    apply Subtype.ext
    change projSimAct Q x⁻¹ (projSimAct Q x w) = w
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  right_inv w := by
    apply Subtype.ext
    change projSimAct Q x (projSimAct Q x⁻¹ w) = w
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  map_mul' a b := Subtype.ext (map_mul (projSimAct Q x) _ _)

@[expose] noncomputable def ffSimOmegaAct (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) : ProjSim Q →* MulAut (omegaProj hQ) :=
  MonoidHom.mk' (ffOmegaAutOf hQ h2) (fun a b => by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change projSimAct Q (a * b) w = projSimAct Q a (projSimAct Q b w)
    rw [map_mul, MulAut.mul_apply])

theorem coe_ffSimOmegaAct (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (x : ProjSim Q) (w : omegaProj hQ) :
    ((ffSimOmegaAct hQ h2 x w : omegaProj hQ) : ProjOrth Q) = projSimAct Q x (w : ProjOrth Q) :=
  rfl

theorem ffSimOmegaAct_projOrthToProjSim (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (y : ProjOrth Q) :
    ffSimOmegaAct hQ h2 (projOrthToProjSim Q y) = MulAut.conjNormal y := by
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [coe_ffSimOmegaAct, projSimAct_projOrthToProjSim, MulAut.conjNormal_apply]

theorem ffSimOmegaAct_eq_one_iff (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (γ : simGroup Q) :
    ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) = 1 ↔
      ∀ t ∈ omegaGroup hQ, simAct Q γ t = t ∨ simAct Q γ t = piOrth Q * t := by
  have key : ∀ t : OGroup Q, projSimAct Q (QuotientGroup.mk γ) (toProj Q t) =
      toProj Q (simAct Q γ t) := fun t => by rw [projSimAct_mk, projActAux_toProj]
  constructor
  · intro h t ht
    have h1 := congrArg (fun φ : MulAut (omegaProj hQ) =>
      ((φ ⟨toProj Q t, (mem_omegaProj_iff hQ).mpr ⟨t, ht, rfl⟩⟩ : omegaProj hQ) : ProjOrth Q)) h
    simp only [MulAut.one_apply] at h1
    rw [coe_ffSimOmegaAct, key] at h1
    have h3 : (simAct Q γ t)⁻¹ * t ∈ piGroup Q := QuotientGroup.eq.mp h1
    rcases mem_piGroup_iff.mp h3 with h4 | h4
    · exact Or.inl (inv_mul_eq_one.mp h4)
    · right
      have h5 : simAct Q γ t = t * (piOrth Q)⁻¹ :=
        eq_mul_inv_of_mul_eq (inv_mul_eq_iff_eq_mul.mp h4).symm
      rw [h5, inv_eq_of_mul_eq_one_right piOrth_mul_self]
      exact (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t)
  · intro h
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    obtain ⟨t, ht, hw⟩ := (mem_omegaProj_iff hQ).mp w.2
    rw [coe_ffSimOmegaAct, MulAut.one_apply, ← hw, key]
    rcases h t ht with h1 | h1
    · rw [h1]
    · rw [h1, map_mul, toProj_piOrth, one_mul]

end CFSG.OddStandard.SmallF3.Omega
