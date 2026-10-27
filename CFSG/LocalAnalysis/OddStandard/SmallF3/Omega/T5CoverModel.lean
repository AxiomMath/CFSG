module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

variable {V' : Type} [AddCommGroup V'] [Module (ZMod 3) V'] [FiniteDimensional (ZMod 3) V']
  {Q' : QuadraticForm (ZMod 3) V'}

private theorem map_omegaGroup_mulAut (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (φ : MulAut (OGroup Q)) :
    (omegaGroup hQ).map φ.toMonoidHom = omegaGroup hQ := by
  rw [omegaGroup_eq_commutator hQ h2, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ φ.surjective]

private noncomputable def projSimOmegaAct (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (x : ProjSim Q) :
    omegaGroup hQ ≃* omegaGroup hQ :=
  (MulEquiv.subgroupMap (projSimActO Q x) (omegaGroup hQ)).trans
    (MulEquiv.subgroupCongr (map_omegaGroup_mulAut hQ h2 (projSimActO Q x)))

private theorem coe_projSimOmegaAct (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (x : ProjSim Q) (t : omegaGroup hQ) :
    ((projSimOmegaAct hQ h2 x t : omegaGroup hQ) : OGroup Q) =
      projSimActO Q x (t : OGroup Q) :=
  rfl

private theorem omegaToProj_projSimOmegaAct (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (x : ProjSim Q) (t : omegaGroup hQ) :
    omegaToProj hQ (projSimOmegaAct hQ h2 x t) =
      ffSimOmegaAct hQ h2 x (omegaToProj hQ t) := by
  apply Subtype.ext
  simp only [coe_omegaToProj, coe_ffSimOmegaAct, coe_projSimOmegaAct, toProj_projSimActO]

private noncomputable def omegaGroupCongr (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    omegaGroup hQ ≃* omegaGroup hQ' :=
  (MulEquiv.subgroupMap (TauCeti.QuadraticMap.orthogonalGroupCongr e) (omegaGroup hQ)).trans
    (MulEquiv.subgroupCongr (isoO_map_omegaGroup hQ hQ' e h2))

private theorem coe_omegaGroupCongr (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) (t : omegaGroup hQ) :
    ((omegaGroupCongr hQ hQ' e h2 t : omegaGroup hQ') : OGroup Q') =
      TauCeti.QuadraticMap.orthogonalGroupCongr e (t : OGroup Q) :=
  rfl

private theorem omegaToProj_omegaGroupCongr (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) (t : omegaGroup hQ) :
    omegaToProj hQ' (omegaGroupCongr hQ hQ' e h2 t) =
      omegaProjCongr hQ hQ' e h2 (omegaToProj hQ t) := by
  apply Subtype.ext
  simp only [coe_omegaToProj, coe_omegaProjCongr, projOrthCongr_toProj, coe_omegaGroupCongr]

theorem t5_cover_of_model (hS : Asc82SchurU43) (hL : IsOm6Z2 L)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    ∃ φ : ↥L →* omegaGroup hQ, IsCoverMap L φ ∧
      ∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φ l) := by
  obtain ⟨V', i1, i2, i3, Q', hQ', φ₀, hcov⟩ := t5_exists_cover hS hL
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨e₀, he₀⟩ := t5_exists_model hL hcov
  have hdim' : Module.finrank (ZMod 3) V' = 6 := hcov.finrank_eq
  have hs' : quadSign Q' = -1 := hcov.quadSign_eq
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have h2' : 2 ≤ Module.finrank (ZMod 3) V' := by omega
  obtain ⟨T⟩ := equivalent_of_quadSign_eq hQ' hQ (hdim'.trans hdim.symm) (hs'.trans hs.symm)
  let g : omegaGroup hQ' ≃* omegaGroup hQ := omegaGroupCongr hQ' hQ T h2'
  let c : omegaProj hQ' ≃* omegaProj hQ := omegaProjCongr hQ' hQ T h2'
  have hg : ∀ t : omegaGroup hQ', g t = omegaGroupCongr hQ' hQ T h2' t := fun _ => rfl
  have hc : ∀ a : omegaProj hQ', c a = omegaProjCongr hQ' hQ T h2' a := fun _ => rfl
  have hbij : Function.Bijective
      (ffSimOmegaAct hQ h2 : ProjSim Q →* MulAut (omegaProj hQ)) := by
    have h := ffSimOmegaAct_bijective_six_minus hQ hdim hs
    rwa [show ffSimOmegaAct hQ h2 = ffSimOmegaAct hQ (by omega) from
      congrArg (ffSimOmegaAct hQ) (Subsingleton.elim h2 (by omega))] at h
  obtain ⟨x, hx⟩ := hbij.2 (c.symm.trans (e₀.symm.trans e))
  let φ : ↥L →* omegaGroup hQ :=
    (projSimOmegaAct hQ h2 x).toMonoidHom.comp (g.toMonoidHom.comp φ₀)
  have hsurj : Function.Surjective φ :=
    (projSimOmegaAct hQ h2 x).surjective.comp (g.surjective.comp hcov.surjective)
  have hker : φ.ker = oddCore ↥L := by
    change ((projSimOmegaAct hQ h2 x).toMonoidHom.comp (g.toMonoidHom.comp φ₀)).ker =
      oddCore ↥L
    rw [MonoidHom.ker_comp_of_injective _ _ (projSimOmegaAct hQ h2 x).injective,
      MonoidHom.ker_comp_of_injective _ _ g.injective, hcov.ker_eq]
  refine ⟨φ, ⟨hsurj, hker, hdim, hs⟩, ?_⟩
  intro l
  have h1 : c (e₀ (QuotientGroup.mk l)) = omegaToProj hQ (g (φ₀ l)) := by
    rw [hc (e₀ (QuotientGroup.mk l)), he₀ l, hg (φ₀ l)]
    exact (omegaToProj_omegaGroupCongr hQ' hQ T h2' (φ₀ l)).symm
  calc e (QuotientGroup.mk l)
      = (e₀.symm.trans e) (e₀ (QuotientGroup.mk l)) := by
        simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    _ = (c.symm.trans (e₀.symm.trans e)) (c (e₀ (QuotientGroup.mk l))) := by
        simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    _ = ffSimOmegaAct hQ h2 x (c (e₀ (QuotientGroup.mk l))) := by rw [hx]
    _ = ffSimOmegaAct hQ h2 x (omegaToProj hQ (g (φ₀ l))) := by rw [h1]
    _ = omegaToProj hQ (projSimOmegaAct hQ h2 x (g (φ₀ l))) :=
          (omegaToProj_projSimOmegaAct hQ h2 x (g (φ₀ l))).symm
    _ = omegaToProj hQ (φ l) := rfl

end CFSG.OddStandard.SmallF3.Omega
