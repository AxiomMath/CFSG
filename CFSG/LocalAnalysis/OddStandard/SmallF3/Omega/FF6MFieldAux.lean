module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem ff6m_sq_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

theorem ff6m_model_data (h : IsOm6M L) {s : G} (hs2 : orderOf s = 2)
    (hsn : s ∈ normalizer (L : Set G)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (x : ProjSim Q),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 ∧
        InducesViaP L (Subgroup.center ↥L) hQ e s x ∧ x * x = 1 := by
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff6m_exists_model h
  obtain ⟨x, hx⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e hsn
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, hx,
    ff6m_induces_sq hQ (by omega) e hx (ff6m_sq_of_orderOf_eq_two hs2)⟩

section Cover

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_cover_of_model (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hs2 : orderOf s = 2) :
    ∃ ρ : ↥(L ⊓ centralizer ({s} : Set G)) →* ↥(ffFix hQ (by omega) x), OddCentralCover ρ := by
  obtain ⟨ρ, hρ, -⟩ := ff6m_exists_centCover hQ (by omega) e (ff6m_odd_center h) hs
    (ff6m_sq_of_orderOf_eq_two hs2)
  exact ⟨ρ, hρ⟩

theorem ff6m_bot_of_solvable (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hs2 : orderOf s = 2) (hsol : Group.IsSolvable ↥(ffFix hQ (by omega) x)) :
    layerCent L s = ⊥ := by
  obtain ⟨ρ, hρ⟩ := ff6m_cover_of_model h hdim hs hs2
  exact ff6m_cover_layer_eq_bot hρ hsol

theorem ff6m_shape_L29 (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hs2 : orderOf s = 2) (hlm : LayerModel ↥(ffFix hQ (by omega) x) .PSL 2 2) :
    IsL29 (layerCent L s) ∧ XOut L s = layerCent L s := by
  obtain ⟨ρ, hρ⟩ := ff6m_cover_of_model h hdim hs hs2
  exact ff6m_cover_isL29 hρ hlm

theorem ff6m_shape_Omega5 (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hs2 : orderOf s = 2) (hlm : LayerModel ↥(ffFix hQ (by omega) x) .PSp 2 1) :
    IsOmega5 (layerCent L s) ∧ XOut L s = layerCent L s := by
  obtain ⟨ρ, hρ⟩ := ff6m_cover_of_model h hdim hs hs2
  exact ff6m_cover_isOmega5 hρ hlm

theorem ff6m_shape_U33 (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hs2 : orderOf s = 2) (hlm : LayerModel ↥(ffFix hQ (by omega) x) .PSU 3 1) :
    IsU33 (layerCent L s) ∧ XOut L s = layerCent L s := by
  obtain ⟨ρ, hρ⟩ := ff6m_cover_of_model h hdim hs hs2
  exact ff6m_cover_isU33 hρ hlm

theorem ff6m_xTwoCore_of (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hs2 : orderOf s = 2) (hX : XTwoCore ↥(ffFix hQ (by omega) x)) :
    XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G))) := by
  obtain ⟨ρ, hρ⟩ := ff6m_cover_of_model h hdim hs hs2
  exact ff6m_cover_X_eq_pCore hρ hX

theorem ff6m_not_centralizer (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hx : x ≠ 1) :
    s ∉ centralizer (L : Set G) := fun hc =>
  hx ((ff6m_centralizer_iff_eq_one h.1 hQ (by omega) e hs).mp hc)

end Cover

end CFSG.OddStandard.SmallF3.Omega
