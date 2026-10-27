module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf

theorem altPumpSpor_HS :
    AltPumpSporClauseFor .HS := by
  intro S _ _ _ hna ⟨e⟩ σ P h hex m hm hm7 ⟨eP⟩
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  let θ : S ≃* hsP := e.trans hsPermEquiv
  set α : MulAut hsP := MulAut.congr θ σ with hαdef
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hσσ, map_one]
  have hα1 : α ≠ 1 := fun h1 =>
    hσ1 ((MulAut.congr θ).injective (by rw [← hαdef, h1, map_one]))
  obtain ⟨r, hr, g, -, x, -, -, hfix⟩ := QuasithinUnique.Id2519.SporHS.fix_data α hα2 hα1
  have hmap : (fixedSubgroup σ).map θ.toMonoidHom = QuasithinUnique.Id2519.fixSubgroup α := by
    ext y
    rw [QuasithinUnique.Id2519.mem_fixSubgroup]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : σ z = z := hz
      change θ (σ (θ.symm (θ z))) = θ z
      rw [MulEquiv.symm_apply_apply, hz']
    · intro hy
      have h1 : θ (σ (θ.symm y)) = y := hy
      refine ⟨θ.symm y, ?_, by simp⟩
      change σ (θ.symm y) = θ.symm y
      apply θ.injective
      rw [h1, MulEquiv.apply_symm_apply]
  let E : fixedSubgroup σ ≃* ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) :=
    (((fixedSubgroup σ).equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hmap)).trans (QuasithinUnique.Id2519.SporHS.fixEquiv hfix)
  have hcardC : Nat.card (fixedSubgroup σ) = r.centOrder := by
    rw [Nat.card_congr E.toEquiv]
    obtain ⟨-, -, -, hrows, -⟩ := hs_involution_centralizers
    exact (hrows r hr).2.2.2.2.1
  have h2520 : 2520 ∣ r.centOrder :=
    hcardC ▸ (dvd_card_of_alt hm7 eP).2.trans (Subgroup.card_dvd_of_le h.2.1)
  rcases QuasithinUnique.Id2519.SporHS.hsRows_cases hr with h1 | ⟨-, -, h1, -⟩ | ⟨hrep, -⟩ | h1
  · rw [h1] at h2520
    exact absurd h2520 (by decide)
  · rw [h1] at h2520
    exact absurd h2520 (by decide)
  swap
  · rw [h1] at h2520
    exact absurd h2520 (by decide)
  have hO : hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) =
      QuasithinUnique.Id2519.HSAut.outerC := by
    rw [hrep]
    rfl
  have hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥ :=
    oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_HS hna e) hσ2
  obtain ⟨hcomp, ⟨eL⟩⟩ := exact_component_of_oddCore h hcore hex
  let E' : fixedSubgroup σ ≃* ↥QuasithinUnique.Id2519.HSAut.outerC :=
    E.trans (MulEquiv.subgroupCongr hO)
  set L := P.subgroupOf (fixedSubgroup σ)
  have hB := isComponent_map_mulEquiv E' hcomp
  have eB : ↥(L.map E'.toMonoidHom) ≃* alternatingGroup (Fin m) :=
    (L.equivMapOfInjective E'.toMonoidHom E'.injective).symm.trans (eL.trans eP)
  have : IsSimpleGroup ↥(commutator ↥QuasithinUnique.Id2519.HSAut.outerC) :=
    QuasithinUnique.Id2519.HSAut.commutator_simple'
  have hBle := QuasithinUnique.Id2519.le_commutator_of_isQuasisimple hB.1
  have htop := QuasithinUnique.Id2519.isComponent_eq_top_of_isSimpleGroup
    (CFSG.LocalCores.component_overgroup hB hBle)
  have hBeq : L.map E'.toMonoidHom = commutator ↥QuasithinUnique.Id2519.HSAut.outerC :=
    le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)
  have hc := card_of_mulEquiv_alt (by omega) eB
  rw [hBeq, QuasithinUnique.Id2519.HSAut.card_commutator'] at hc
  exact factorial_div_two_ne 9 (by decide) (by decide) m hm hm7 hc.symm

end CFSG.ComponentClassification.SolMax
