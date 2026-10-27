module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def fgRho (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) : ↥L →* ↥(omegaProj hQ) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem fgRho_apply (hQ : Q.Nondegenerate) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (l : ↥L) : fgRho hQ e l = e (QuotientGroup.mk l) := rfl

theorem fg_ker_rho (hQ : Q.Nondegenerate) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    (fgRho hQ e).ker = Subgroup.center ↥L := by
  ext l
  rw [MonoidHom.mem_ker, fgRho_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem fg_oddCentralCover_rho (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hodd : Odd (Nat.card (Subgroup.center ↥L))) :
    OddCentralCover (fgRho hQ e) where
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  ker_le_center := (fg_ker_rho hQ e).le
  odd_card_ker := by
    rw [fg_ker_rho hQ e]
    exact hodd

theorem fg_rho_conj (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {x : G} (hx2 : x * x = 1) (hxN : x ∈ normalizer (L : Set G)) (l : ↥L) :
    fgRho hQ e (conjAut L hx2 hxN l) =
      ffSimOmegaAct hQ h2 (ffTheta hQ h e ⟨x, hxN⟩) (fgRho hQ e l) := by
  apply Subtype.ext
  rw [coe_ffSimOmegaAct]
  exact (ffTheta_conj hQ h e ⟨x, hxN⟩ l (conjAut L hx2 hxN l) rfl).symm

theorem fg_isComponentIn_rho (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {x : G} (hx2 : x * x = 1)
    (hxN : x ∈ normalizer (L : Set G)) {X : Subgroup G}
    (hX : IsComponentIn X (L ⊓ centralizer ({x} : Set G))) :
    IsComponentIn ((X.subgroupOf L).map (fgRho hQ e))
      (ffFix hQ h2 (ffTheta hQ h e ⟨x, hxN⟩)) := by
  have hXL : X ≤ L := hX.1.trans inf_le_left
  have h1 : IsComponentIn (X.subgroupOf L) (fixSub (conjAut L hx2 hxN)) := by
    rw [← sec63PT_isComponentIn_map_iff L.subtype L.subtype_injective,
      Subgroup.subgroupOf_map_subtype, sec63PT_map_subtype_fixSub L hx2 hxN, inf_eq_left.mpr hXL]
    exact hX
  have hcov := fg_oddCentralCover_rho hQ e hodd
  have h3 := sec63PT_isComponentIn_map (fgRho hQ e) hcov.ker_le_center h1
  rw [sec63PT_map_fixSub hcov (conjAut_mul_self L hx2 hxN) (fg_rho_conj hQ h e h2 hx2 hxN)] at h3
  exact h3

@[expose] noncomputable def fgThetaR (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G)) : ↥R →* ProjSim Q :=
  (ffTheta hQ h e).comp (Subgroup.inclusion hR)

theorem fg_thetaR_ker (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hLp : commutator ↥L = ⊤) {R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G)) :
    (fgThetaR hQ h e hR).ker = (centralizer (L : Set G)).subgroupOf R := by
  ext r
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ffTheta_eq_one_iff hQ h e hLp ⟨(r : G), hR r.2⟩

theorem fg_relIndex_eq_card_range (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hLp : commutator ↥L = ⊤) {R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G)) :
    (centralizer (L : Set G)).relIndex R = Nat.card (fgThetaR hQ h e hR).range := by
  rw [Subgroup.relIndex, ← fg_thetaR_ker hQ h e hLp hR, Subgroup.index_ker]

theorem fg_thetaR_centralizes (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {X R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G)) :
    ∀ a ∈ (fgThetaR hQ h e (hR.trans inf_le_left)).range,
      ∀ j ∈ (X.subgroupOf L).map (fgRho hQ e),
        projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q) := by
  rintro _ ⟨r, rfl⟩ _ ⟨x₀, hx₀, rfl⟩
  have hrC : (r : G) ∈ centralizer (X : Set G) := (hR r.2).2
  have hcomm : (x₀ : G) * (r : G) = (r : G) * (x₀ : G) := mem_centralizer_iff.mp hrC _ hx₀
  exact ffTheta_conj hQ h e ⟨(r : G), (hR r.2).1⟩ x₀ x₀
    (eq_mul_inv_iff_mul_eq.mpr hcomm)

end CFSG.OddStandard.SmallF3.Omega
