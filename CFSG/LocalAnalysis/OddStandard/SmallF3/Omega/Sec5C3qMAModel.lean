module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDInd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5c3qma_frame (hS : Asc82SchurU43) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z r : G} {B A : Subgroup G} (hR : Sec5RCtx G t L S z r B A) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
      (φc : ↥L →* omegaGroup hQ) (φ : (Fin 6 → ZMod 2) → G),
      IsCoverMap L φc ∧ Sec5Model58 t L z r A φ ∧
        (∀ w, CoverAct L φc (φ w) (orthToSim Q (fr.signChange (sec5c_supp w)))) ∧
        (∀ (w : Fin 6 → ZMod 2) (hw : φ w ∈ L), IsEvenVec w →
          ((φc ⟨φ w, hw⟩ : omegaGroup hQ) : OGroup Q) = fr.signChange (sec5c_supp w)) := by
  obtain ⟨V, _, _, _, Q, hQ, fr, i, e, φc, hφ, he, habs, hind⟩ := sec5c_model hS hR
  have hL : IsOm6Z2 L := hR.toSec5Ctx.toSec5Setting.isOm6Z2
  have ht2 : orderOf t = 2 := hR.involution
  have hA : A = zpowers r ⊔ B := hR.A_eq
  have htB : t ∈ B := hR.B_split.1
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (hR.B_le hb)).1
  have htL : t ∈ L := hBL htB
  have htc : t ∈ centerIn L := sec5_mem_centerIn_iff.mpr ⟨htL, fun y hy =>
    Subgroup.mem_centralizer_iff.mp (hR.component.1 hy) t (Set.mem_singleton t)⟩
  have hzI : IsI4PlusIn L z := hR.pocket
  have hzL : z ∈ L := by
    obtain ⟨-, K, hzK, hKle, -, -⟩ := hzI
    exact (Subgroup.mem_inf.mp (hKle hzK)).1
  have hzz : z * z = 1 := by rw [← pow_two, ← hzI.1]; exact pow_orderOf_eq_one z
  have hzB : z ∈ B := habs.mem_B_of_comm hzL hzz fun b hb => by
    have hbA : b ∈ A := by rw [hA]; exact Subgroup.mem_sup_right hb
    exact hR.central b (hR.A_le hbA)
  refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, fr, φc,
    sec5c_phi L B r i fr φc, hφ, ⟨?_, habs.phi_ones htL htB (hφ.map_central hL htc ht2 htL),
    ⟨i, habs.phi_single⟩, ?_, habs.phi_mem_L_iff, ?_, ?_⟩, ?_, ?_⟩
  · subst hA
    unfold IsPerm6 IsPermModuleVia
    refine ⟨fun v w _ _ => habs.phi_add v w, fun v w _ _ hvw => habs.phi_inj hvw,
      fun x => ⟨fun hx => ?_, fun ⟨v, _, hv⟩ => habs.mem_A_iff.mpr ⟨v, hv⟩⟩, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := habs.mem_A_iff.mp hx
      exact ⟨v, trivial, hv⟩
    · intro g hg
      obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨σ, hσ, hform⟩ := habs.perm_of_mem ⟨g, hgL⟩ hgN
      exact ⟨σ, hσ, fun v _ => hform v⟩
    · intro σ hσ
      obtain ⟨g, hgN, hform⟩ := habs.exists_of_perm hσ
      exact ⟨g, Subgroup.mem_inf.mpr ⟨g.2, hgN⟩, fun v _ => hform v⟩
  · obtain ⟨v, hv⟩ := habs.mem_A_iff.mp (show z ∈ zpowers r ⊔ B from Subgroup.mem_sup_right hzB)
    have hvL : sec5c_phi L B r i fr φc v ∈ L := by rw [hv]; exact hzL
    have hev : IsEvenVec v := (habs.phi_mem_L_iff v).mp hvL
    refine ⟨v, habs.weight_of_invType hev hvL ?_, hv⟩
    have hcast : (⟨sec5c_phi L B r i fr φc v, hvL⟩ : ↥L) = ⟨z, hzL⟩ := Subtype.ext hv
    rw [hcast]
    exact t5_phi_pocket_invType hφ hL hzI hzL
  · intro v hv
    have hK : (sec5c_supp v).card = 1 ∨ (sec5c_supp v).card = 5 := by
      simpa only [sec5c_vecWeight] using hv
    obtain ⟨α, hα⟩ := sec5c_simHasType_one hQ fr hK
    refine ⟨α, ?_⟩
    unfold InducesTypeSome
    exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, _, habs.dim, habs.sgn,
      habs.phi_induces he hind v, hα⟩
  · intro v hv
    have hK : (sec5c_supp v).card = 3 := by
      simpa only [sec5c_vecWeight] using hv
    obtain ⟨α, hα⟩ := sec5c_simHasType_three hQ fr hK
    refine ⟨α, ?_⟩
    unfold InducesTypeSome
    exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, _, habs.dim, habs.sgn,
      habs.phi_induces he hind v, hα⟩
  · intro w
    exact t5_coverAct_of_inducesViaP hL hφ he (habs.phi_induces he hind w)
      (projOrthToProjSim_toProj _).symm
  · intro w hw hev
    have hJ : Even (sec5c_supp w).card := (sec5c_isEvenVec_iff w).mp hev
    have hlift : (⟨sec5c_phi L B r i fr φc w, hw⟩ : ↥L) =
        sec5c_liftL L B φc (fr.signChange (sec5c_supp w)) := Subtype.ext (habs.phi_even hev)
    rw [hlift]
    exact habs.map_liftL (signChange_mem_ffB0 fr hJ)

end CFSG.OddStandard.SmallF3.Omega
