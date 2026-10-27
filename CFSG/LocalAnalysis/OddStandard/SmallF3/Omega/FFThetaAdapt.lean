module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTransAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU1
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

private theorem aux_projOrthToProjSim_projSimAct (δ : ProjSim Q) (y : ProjOrth Q) :
    projOrthToProjSim Q (projSimAct Q δ y) = δ * projOrthToProjSim Q y * δ⁻¹ := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  change QuotientGroup.mk (orthToSim Q (simAct Q γ t)) =
    QuotientGroup.mk γ * QuotientGroup.mk (orthToSim Q t) * (QuotientGroup.mk γ)⁻¹
  rw [sec9u_orthToSim_simAct, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]

private theorem aux_projSimAct_mul_inv_apply (y : ProjSim Q) (w : ProjOrth Q) :
    projSimAct Q y (projSimAct Q y⁻¹ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem aux_ffSimOmegaAct_inv_mul_apply (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (y : ProjSim Q) (w : omegaProj hQ) :
    ffSimOmegaAct hQ h2 y⁻¹ (ffSimOmegaAct hQ h2 y w) = w := by
  apply Subtype.ext
  rw [coe_ffSimOmegaAct, coe_ffSimOmegaAct, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, MulAut.one_apply]

theorem simInGStar_conj {x : ProjSim Q} (δ : ProjSim Q) (hx : SimInGStar x) :
    SimInGStar (δ * x * δ⁻¹) := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨projSimAct Q δ y, by rw [aux_projOrthToProjSim_projSimAct, hy]⟩

theorem simInGStar_conj_iff (x δ : ProjSim Q) : SimInGStar (δ⁻¹ * x * δ) ↔ SimInGStar x := by
  constructor
  · intro h
    have h1 := simInGStar_conj (x := δ⁻¹ * x * δ) δ h
    have heq : δ * (δ⁻¹ * x * δ) * δ⁻¹ = x := by group
    rwa [heq] at h1
  · intro h
    have h1 := simInGStar_conj (x := x) δ⁻¹ h
    rwa [inv_inv] at h1

@[expose] noncomputable def ffAdapt {hQ : Q.Nondegenerate} (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (y : ProjSim Q) :
    ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ :=
  e.trans (ffSimOmegaAct hQ h2 y⁻¹)

theorem ffAdapt_apply {hQ : Q.Nondegenerate} (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (y : ProjSim Q) (q : ↥L ⧸ Subgroup.center ↥L) :
    ffAdapt h2 e y q = ffSimOmegaAct hQ h2 y⁻¹ (e q) :=
  rfl

theorem ff6mPhi_ffAdapt {hQ : Q.Nondegenerate} (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (y : ProjSim Q) (l : ↥L) :
    ff6mPhi (ffAdapt h2 e y) l = ffSimOmegaAct hQ h2 y⁻¹ (ff6mPhi e l) :=
  rfl

theorem inducesViaP_ffAdapt {hQ : Q.Nondegenerate} (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (y : ProjSim Q) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) :
    InducesViaP L (Subgroup.center ↥L) hQ (ffAdapt h2 e y) s (y⁻¹ * x * y) := by
  refine ⟨hs.1, ?_⟩
  intro l l' hl'
  rw [ffAdapt_apply, ffAdapt_apply, coe_ffSimOmegaAct, coe_ffSimOmegaAct, hs.2 l l' hl']
  rw [map_mul, MulAut.mul_apply, aux_projSimAct_mul_inv_apply, ← MulAut.mul_apply, ← map_mul]

theorem ffImg_ffAdapt {hQ : Q.Nondegenerate} (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (y : ProjSim Q) (B : Subgroup G)
    (U : Subgroup ↥(omegaProj hQ))
    (hB : ffImg (ff6mPhi e) B = U.map (ffSimOmegaAct hQ h2 y).toMonoidHom) :
    ffImg (ff6mPhi (ffAdapt h2 e y)) B = U := by
  have hcomp : ff6mPhi (ffAdapt h2 e y) =
      (ffSimOmegaAct hQ h2 y⁻¹).toMonoidHom.comp (ff6mPhi e) :=
    MonoidHom.ext fun l => ff6mPhi_ffAdapt h2 e y l
  have hcompid : (ffSimOmegaAct hQ h2 y⁻¹).toMonoidHom.comp
      (ffSimOmegaAct hQ h2 y).toMonoidHom = MonoidHom.id ↥(omegaProj hQ) :=
    MonoidHom.ext fun w => aux_ffSimOmegaAct_inv_mul_apply hQ h2 y w
  rw [hcomp]
  calc ffImg ((ffSimOmegaAct hQ h2 y⁻¹).toMonoidHom.comp (ff6mPhi e)) B
      = (ffImg (ff6mPhi e) B).map (ffSimOmegaAct hQ h2 y⁻¹).toMonoidHom := by
        simp only [ffImg]
        exact (Subgroup.map_map _ _ _).symm
    _ = (U.map (ffSimOmegaAct hQ h2 y).toMonoidHom).map
          (ffSimOmegaAct hQ h2 y⁻¹).toMonoidHom := by rw [hB]
    _ = U := by rw [Subgroup.map_map, hcompid, Subgroup.map_id]

end CFSG.OddStandard.SmallF3.Omega
