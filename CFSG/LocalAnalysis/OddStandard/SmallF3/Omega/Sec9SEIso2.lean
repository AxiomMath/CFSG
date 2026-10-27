module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  [AddCommGroup V'] [Module (ZMod 3) V'] [FiniteDimensional (ZMod 3) V']
  {Q : QuadraticForm (ZMod 3) V} {Q' : QuadraticForm (ZMod 3) V'}

private theorem ffSimOmegaAct_bijective_of (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Function.Bijective (ffSimOmegaAct hQ h2 : ProjSim Q →* MulAut (omegaProj hQ)) := by
  have h2b : 2 ≤ Module.finrank (ZMod 3) V := by
    rcases h with ⟨h5, -⟩ | ⟨h6, -⟩ <;> omega
  have hb : Function.Bijective
      (ffSimOmegaAct hQ h2b : ProjSim Q →* MulAut (omegaProj hQ)) :=
    ffSimOmegaAct_bijective hQ h
  rwa [show (ffSimOmegaAct hQ h2 : ProjSim Q →* MulAut (omegaProj hQ)) =
      ffSimOmegaAct hQ h2b from
    congrArg (ffSimOmegaAct hQ) (Subsingleton.elim h2 h2b)]

theorem simHasDim_of_conj_iso (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (hm' : Module.finrank (ZMod 3) V' = 6 ∧ quadSign Q' = -1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (h2' : 2 ≤ Module.finrank (ZMod 3) V')
    (θ : omegaProj hQ ≃* omegaProj hQ') {x : ProjSim Q} {x' : ProjSim Q'}
    (hθ : ∀ a : omegaProj hQ,
      ffSimOmegaAct hQ' h2' x' (θ a) = θ (ffSimOmegaAct hQ h2 x a))
    {r : ℕ} (h : SimHasDim x' r) : SimHasDim x r := by
  obtain ⟨σ⟩ := equivalent_of_quadSign_eq hQ hQ' (hm.1.trans hm'.1.symm)
    (hm.2.trans hm'.2.symm)
  obtain ⟨t', ht', hdim', hproj'⟩ := h
  let t : OGroup Q := (orthogonalGroupCongr σ).symm t'
  have hσt : orthogonalGroupCongr σ t = t' := (orthogonalGroupCongr σ).apply_symm_apply t'
  have htt : t * t = 1 := by
    apply (orthogonalGroupCongr σ).injective
    rw [map_mul, hσt, ht', map_one]
  have hdim : invDim t = r := by
    rw [← invDim_orthogonalGroupCongr σ t, hσt, hdim']
  let x₁ : ProjSim Q := projOrthToProjSim Q (toProj Q t)
  have h₁ : SimHasDim x₁ r := ⟨t, htt, hdim, rfl⟩
  have hproj_σ : projOrthToProjSim Q' (projOrthCongr σ (toProj Q t)) = x' := by
    rw [projOrthCongr_toProj, hσt]
    exact hproj'
  have hinter : ∀ a : omegaProj hQ,
      omegaProjCongr hQ hQ' σ h2 (ffSimOmegaAct hQ h2 x₁ a) =
        ffSimOmegaAct hQ' h2' x' (omegaProjCongr hQ hQ' σ h2 a) := by
    intro a
    have hkey := ffSimOmegaAct_omegaProjCongr hQ hQ' σ h2 h2' (toProj Q t) a
    rw [hproj_σ] at hkey
    exact hkey
  let ν : omegaProj hQ ≃* omegaProj hQ := (omegaProjCongr hQ hQ' σ h2).trans θ.symm
  let α : MulAut (omegaProj hQ) := ffSimOmegaAct hQ h2 x
  have hνθ : ∀ a : omegaProj hQ, θ (ν a) = omegaProjCongr hQ hQ' σ h2 a := fun a =>
    MulEquiv.apply_symm_apply θ (omegaProjCongr hQ hQ' σ h2 a)
  have hνA : ∀ a : omegaProj hQ, ν (ffSimOmegaAct hQ h2 x₁ a) = α (ν a) := by
    intro a
    calc ν (ffSimOmegaAct hQ h2 x₁ a)
        = θ.symm (omegaProjCongr hQ hQ' σ h2 (ffSimOmegaAct hQ h2 x₁ a)) := rfl
      _ = θ.symm (ffSimOmegaAct hQ' h2' x' (omegaProjCongr hQ hQ' σ h2 a)) := by
            rw [hinter a]
      _ = θ.symm (ffSimOmegaAct hQ' h2' x' (θ (ν a))) := by rw [hνθ a]
      _ = θ.symm (θ (α (ν a))) := by rw [hθ (ν a)]
      _ = α (ν a) := MulEquiv.symm_apply_apply θ (α (ν a))
  have hA₁ : ffSimOmegaAct hQ h2 x₁ = ν⁻¹ * α * ν := by
    apply MulEquiv.ext
    intro a
    rw [MulAut.mul_apply, MulAut.mul_apply]
    calc ffSimOmegaAct hQ h2 x₁ a = ν⁻¹ (ν (ffSimOmegaAct hQ h2 x₁ a)) :=
          (MulEquiv.symm_apply_apply ν (ffSimOmegaAct hQ h2 x₁ a)).symm
      _ = ν⁻¹ (α (ν a)) := by rw [hνA a]
  obtain ⟨w, hw⟩ :=
    (ffSimOmegaAct_bijective_of hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) h2).2 ν
  have hx₁ : x₁ = w⁻¹ * x * w := by
    apply (ffSimOmegaAct_bijective_of hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) h2).1
    rw [map_mul, map_mul, map_inv, hw]
    exact hA₁
  have hx_eq : x = w * x₁ * w⁻¹ := by
    rw [hx₁]
    group
  have hconj : SimHasDim (w * x₁ * w⁻¹) r := simHasDim_conj h₁ w
  rwa [← hx_eq] at hconj

theorem simHasDim_of_inducesViaP {G : Type} [Group G] {L : Subgroup G} {s : G}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (hm' : Module.finrank (ZMod 3) V' = 6 ∧ quadSign Q' = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (e' : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ')
    {x : ProjSim Q} {x' : ProjSim Q'}
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hx' : InducesViaP L (Subgroup.center ↥L) hQ' e' s x')
    {r : ℕ} (h : SimHasDim x' r) : SimHasDim x r := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have h2' : 2 ≤ Module.finrank (ZMod 3) V' := by omega
  refine simHasDim_of_conj_iso hQ hQ' hm hm' h2 h2' (e.symm.trans e') ?_ h
  intro a
  let q : ↥L ⧸ Subgroup.center ↥L := e.symm a
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective q
  have hl' : s * (l : G) * s⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hx.1 (l : G)).mp l.2
  let l' : ↥L := ⟨s * (l : G) * s⁻¹, hl'⟩
  have he : e (QuotientGroup.mk l') = ffSimOmegaAct hQ h2 x (e (QuotientGroup.mk l)) := by
    apply Subtype.ext
    rw [coe_ffSimOmegaAct]
    exact hx.2 l l' rfl
  have he' : e' (QuotientGroup.mk l') = ffSimOmegaAct hQ' h2' x' (e' (QuotientGroup.mk l)) := by
    apply Subtype.ext
    rw [coe_ffSimOmegaAct]
    exact hx'.2 l l' rfl
  have ha' : e (QuotientGroup.mk l) = a := by
    rw [hl]
    exact e.apply_symm_apply a
  have hθa : (e.symm.trans e') a = e' (QuotientGroup.mk l) := by
    rw [← ha', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  calc ffSimOmegaAct hQ' h2' x' ((e.symm.trans e') a)
      = ffSimOmegaAct hQ' h2' x' (e' (QuotientGroup.mk l)) := by rw [hθa]
    _ = e' (QuotientGroup.mk l') := he'.symm
    _ = (e.symm.trans e') (e (QuotientGroup.mk l')) := by
          rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    _ = (e.symm.trans e') (ffSimOmegaAct hQ h2 x (e (QuotientGroup.mk l))) := by rw [he]
    _ = (e.symm.trans e') (ffSimOmegaAct hQ h2 x a) := by rw [ha']

end CFSG.OddStandard.SmallF3.Omega
