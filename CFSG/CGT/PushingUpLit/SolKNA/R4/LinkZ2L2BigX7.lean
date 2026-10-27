module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.exists_Ry_data (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y}
    (hyL : IsUniqueInvolution L y) (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {V : Subgroup Y}
    (hVL : V ≤ L) (hVA : V ≤ edgeCent (P : Subgroup Y) t u) (hyV : y ∈ V)
    (hU : V ∈ USet (CoreAssembly.conjClass (tightCore R))) :
    ∃ (Ry : Subgroup Y) (e : ↥Ry ≃* QuaternionGroup (2 ^ (r - 2))),
      IsSylow2In Ry L ∧ V = QSub.xc e ∧ quatInvolution r e = y ∧
        (∀ z ∈ Subgroup.closure ({t, u} : Set Y), z ∈ Subgroup.normalizer (Ry : Set Y)) ∧
        Nat.card ↥V = 2 ^ (r - 1) ∧ Nat.card ↥Ry = 2 ^ r := by
  classical
  obtain ⟨R', hR', J', hJ', hR'J', hVR', hcyc, hcard', hV4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hs.large.datum.hypOmegaGen hU
  have hVy : V ≤ Subgroup.centralizer ({y} : Set Y) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    haveI : IsCyclic ↥V := hcyc
    have hcomm := (IsCyclic.commGroup (α := ↥V)).mul_comm (⟨v, hv⟩ : ↥V) (⟨y, hyV⟩ : ↥V)
    simpa using congrArg Subtype.val hcomm
  obtain ⟨Ry, hRy, hVRy, hE⟩ :=
    hs.exists_sylow_E_invariant hyA hL hyL hVA hVy hVL
  have hJ'L : J' = L :=
    Sec6Gen.eq_of_mem_USet hs.large.datum.hypOmegaGen hU hJ' hL
      (hVR'.trans hR'J'.1) hVL
  have hR'L : IsSylow2In R' L := hJ'L ▸ hR'J'
  have hcardR' : Nat.card ↥Ry = Nat.card ↥R' := hRy.natCard_eq hR'L
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat L hL Ry hRy
  have hRycard : Nat.card ↥Ry = 2 ^ r := natCard_eq_of_quat (by omega) e
  have hr1 : r = (r - 1) + 1 := by omega
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    conv_lhs => rw [hr1]
    rw [pow_succ, mul_comm]
  have hVcard : Nat.card ↥V = 2 ^ (r - 1) := by
    have h1 : 2 * Nat.card ↥V = 2 ^ r := by
      rw [← hcard', ← hcardR', hRycard]
    rw [hpow] at h1
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hi : V.relIndex Ry = 2 := by
    have h1 := Subgroup.relIndex_mul_card V Ry
    rw [inf_eq_left.mpr hVRy, hVcard, hRycard, hpow] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h1
  have hVxc : V = QSub.xc e := QSub.eq_xc_of_cyclic_index_two e hr hVRy hcyc hi
  exact ⟨Ry, e, hRy, hVxc,
    quatInvolution_eq_of_uniqueInvolution hr hyL hRy.1 e, hE, hVcard, hRycard⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
