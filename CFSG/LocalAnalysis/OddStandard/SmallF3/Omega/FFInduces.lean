module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

theorem ff_center_map_normalizerMonoidHom (L : Subgroup G) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    (Subgroup.center ↥L).map (Subgroup.normalizerMonoidHom L ⟨s, hs⟩ : ↥L →* ↥L) =
      Subgroup.center ↥L :=
  (Subgroup.characteristic_iff_map_eq.mp inferInstance) _

@[expose] noncomputable def ffCenterQuotAut (L : Subgroup G) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) : MulAut (↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L)
    (Subgroup.normalizerMonoidHom L ⟨s, hs⟩) (ff_center_map_normalizerMonoidHom L hs)

theorem ffCenterQuotAut_mk (L : Subgroup G) {s : G} (hs : s ∈ Subgroup.normalizer (L : Set G))
    (l l' : ↥L) (hl : (l' : G) = s * l * s⁻¹) :
    ffCenterQuotAut L hs (QuotientGroup.mk l) = QuotientGroup.mk l' := by
  have h : Subgroup.normalizerMonoidHom L ⟨s, hs⟩ l = l' := Subtype.ext hl.symm
  rw [ffCenterQuotAut, QuotientGroup.congr_mk, h]

theorem ff_exists_induces_of_surjective {L : Subgroup G} (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hsurj : Function.Surjective (ffSimOmegaAct hQ h2 : ProjSim Q →* MulAut (omegaProj hQ)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    ∃ x : ProjSim Q, InducesViaP L (Subgroup.center ↥L) hQ e s x := by
  obtain ⟨x, hx⟩ := hsurj ((ffCenterQuotAut L hs).congr e)
  refine ⟨x, hs, fun l l' hl => ?_⟩
  have h1 : e (QuotientGroup.mk l') = ffSimOmegaAct hQ h2 x (e (QuotientGroup.mk l)) := by
    rw [hx]
    show _ = e (ffCenterQuotAut L hs (e.symm (e (QuotientGroup.mk l))))
    rw [MulEquiv.symm_apply_apply, ffCenterQuotAut_mk L hs l l' hl]
  rw [h1]
  exact coe_ffSimOmegaAct hQ h2 x _

theorem ff_exists_induces (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    {L : Subgroup G} (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    ∃ x : ProjSim Q, InducesViaP L (Subgroup.center ↥L) hQ e s x :=
  ff_exists_induces_of_surjective hQ (by rcases h with ⟨h5, -⟩ | ⟨h6, -⟩ <;> omega)
    (ffSimOmegaAct_bijective hQ h).2 e hs

theorem ff_induces_unique (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    {L : Subgroup G} (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x x' : ProjSim Q}
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hx' : InducesViaP L (Subgroup.center ↥L) hQ e s x') : x = x' := by
  refine (ffSimOmegaAct_injective hQ h5) (MulEquiv.ext fun w => ?_)
  obtain ⟨q, rfl⟩ := e.surjective w
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hl : s * (l : G) * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx.1 (l : G)).mp l.2
  let l' : ↥L := ⟨s * (l : G) * s⁻¹, hl⟩
  apply Subtype.ext
  rw [coe_ffSimOmegaAct hQ (by omega), coe_ffSimOmegaAct hQ (by omega), ← hx.2 l l' rfl,
    ← hx'.2 l l' rfl]

end CFSG.OddStandard.SmallF3.Omega
