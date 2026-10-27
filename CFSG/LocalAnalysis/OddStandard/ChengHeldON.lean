module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldONPerm
public import CFSG.LocalAnalysis.OddStandard.ChengHeldONRelators

public section

namespace CFSG.OddStandard.ChengHeld

open CFSG.ONSchreier CFSG.Blueprint

namespace ONSylow

theorem exists_sylow_of_mulEquiv {Γ G P : Type*} [Group Γ] [Group G] [Group P] [Finite P]
    (e : G ≃* P) (S : Sylow 2 P) (f : Γ ≃* ↥(S : Subgroup P)) :
    ∃ R : Sylow 2 G, Nonempty (Γ ≃* ↥(R : Subgroup G)) := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have hS : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  have eK : ↥(S : Subgroup P) ≃* ↥(S.mapSurjective hS : Subgroup G) :=
    (Subgroup.equivMapOfInjective _ _ e.symm.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective hS S).symm)
  exact ⟨S.mapSurjective hS, ⟨f.trans eK⟩⟩

theorem exists_sylow_onT32Chain :
    ∃ R : Sylow 2 NativeSporadic.ON,
      Nonempty (↥onT32Chain.originalSubgroup ≃* ↥(R : Subgroup NativeSporadic.ON)) := by
  have e3 : onT32Chain.originalSubgroup ≃* onT :=
    (MulEquiv.subgroupCongr rhoT_range.symm).trans (MonoidHom.ofInjective rhoT_injective).symm
  have e4 : onT ≃* ↥(onTSylow : Subgroup Pv) :=
    (Subgroup.subgroupOfEquivOfLe onT_le).symm.trans
      (MulEquiv.subgroupCongr onTSylow_coe.symm)
  exact exists_sylow_of_mulEquiv onEquivPv onTSylow (e3.trans e4)

end ONSylow

open ONSylow

theorem exists_mulEquiv_onSylow
    {G : Type} [Group G] [Finite G]
    {t pi tau mu lam ze xi z : G}
    (hf : Frame4 0 t pi tau mu lam ze xi) (hz2 : z * z = 1)
    (hz : Kind.unitary.Act 0 t pi tau mu lam ze xi z)
    {X : Subgroup G} (hX : X = Subgroup.closure ({t, pi, tau, mu, lam, ze, xi, z} : Set G))
    (hcard : Nat.card X = 512) (hpres : Finite ONPres ∧ Nat.card ONPres ≤ 512) :
    ∃ T : Sylow 2 NativeSporadic.ON, Nonempty (X ≃* (T : Subgroup NativeSporadic.ON)) := by
  have hfin := hpres.1
  have hP := hpres.2
  have hXc : X = Subgroup.closure (Set.range ![t, pi, tau, mu, lam, ze, xi, z]) := by
    rw [hX, range_eight]
  obtain ⟨e1⟩ := exists_mulEquiv_closure hP _ (wprod_onRels hf hz2 hz) (by rw [← hXc, hcard])
  obtain ⟨e2⟩ := exists_mulEquiv_t32 hpres
  obtain ⟨R, ⟨e3⟩⟩ := exists_sylow_onT32Chain
  exact ⟨R, ⟨((MulEquiv.subgroupCongr hXc).trans e1.symm).trans (e2.trans e3)⟩⟩

end CFSG.OddStandard.ChengHeld
