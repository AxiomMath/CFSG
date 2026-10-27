module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IPocketL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem sec4ILift_rho_phi (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {P : Subgroup G} (hP : IsSylow2Of P L)
    {fr : Sec4IFrame Sec4IQ} (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e)))
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) :
    ∃ hx : sec4ILiftPhi e fr P v ∈ L,
      ((e (QuotientGroup.mk (⟨sec4ILiftPhi e fr P v, hx⟩ : ↥L)) : Sec4IOmega) :
        ProjOrth Sec4IQ) = sec4IPsi fr v := by
  obtain ⟨hx, -, h⟩ := sec4ILiftPhi_spec hL e hP hfr hv
  exact ⟨hx, h⟩

theorem sec4ILift_type2 (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    ∀ v, IsEvenVec v → v ≠ 0 →
      (vecWeight v = 2 ↔ InducesTypeSome L (sec4ILiftPhi e fr P v) 7 1 2 (-1)) := by
  intro v hv h0
  obtain ⟨hx, hρ⟩ := sec4ILift_rho_phi hL e hP hfr hv
  rw [sec4I_inducesTypeSome_mem_iff e hx (Or.inl rfl), hρ]
  exact sec4IPsi_hasType_two sec4IQ_nondegenerate fr hv h0

theorem sec4ILift_type4 (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    ∀ v, IsEvenVec v → v ≠ 0 → (vecWeight v = 4 ↔ IsI4PlusIn L (sec4ILiftPhi e fr P v)) := by
  intro v hv h0
  obtain ⟨hx, hρ⟩ := sec4ILift_rho_phi hL e hP hfr hv
  have hne : sec4ILiftPhi e fr P v ≠ 1 := by
    intro h1
    apply sec4IPsi_ne_one fr hv h0
    rw [← hρ]
    have : (⟨sec4ILiftPhi e fr P v, hx⟩ : ↥L) = 1 := Subtype.ext h1
    rw [this]
    simp
  have hsq : sec4ILiftPhi e fr P v ^ 2 = 1 :=
    (sec4ILift_isMax hL e hP hfr).2.1.2 _ (sec4ILiftPhi_mem hL e hP hfr hv)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (sec4ILiftPhi e fr P v) = 2 := orderOf_eq_prime hsq hne
  rw [sec4I_isI4PlusIn_iff hL e]
  constructor
  · intro h4
    refine ⟨hx, hord, ?_⟩
    rw [hρ]
    exact (sec4IPsi_hasType_four sec4IQ_nondegenerate fr hv h0).mp h4
  · rintro ⟨hw, -, hty⟩
    rw [hρ] at hty
    exact (sec4IPsi_hasType_four sec4IQ_nondegenerate fr hv h0).mpr hty

theorem sec4ILift_type6 (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    ∀ v, IsEvenVec v → v ≠ 0 →
      (vecWeight v = 6 ↔ InducesTypeSome L (sec4ILiftPhi e fr P v) 7 1 6 (-1)) := by
  intro v hv h0
  obtain ⟨hx, hρ⟩ := sec4ILift_rho_phi hL e hP hfr hv
  rw [sec4I_inducesTypeSome_mem_iff e hx (Or.inr (Or.inr rfl)), hρ]
  exact sec4IPsi_hasType_six sec4IQ_nondegenerate fr hv h0

end CFSG.OddStandard.SmallF3.Omega
