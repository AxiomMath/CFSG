module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadFrameStd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3AM
open scoped commutatorElement MatrixGroups

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.commMod_exactCore3 [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {K' : Subgroup G} (hKK' : K' ∈ omegaNbr Ω K)
    (hJK' : K' ∈ omegaNbr Ω J) {u : G} (hu : IsUniqueInvolution K' u) (hut : u = z * t) :
    ∀ a ∈ Q3NL.exactCore3 z J, ∀ b ∈ Q3NL.exactCore3 z K',
      a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (Q3NL.exactLayer3 Ω z) := by
  classical
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hΩ3 : Q3.InClass3 Ω := Q3T7.inClass3_of_stand3 hs3
  have hBelow : Q3.CIT3Below (Nat.card G) := Q3T7.cit3Below_of_stand3 hs3
  have hnab : ∃ a b : G, a * b ≠ b * a := h.nonabelian
  have hz1 : IsUniqueInvolution K z := hs.hz
  have hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Q3W.not_subset_center_of_ne_one hnab hz1.ne_one
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz1.sq
  have hK'Ω : K' ∈ Ω := hKK'.1
  have hK'tq : K' ∈ Q3NL.tqMembers3 Ω z := mem_tqMembers3_of_omegaNbr hΩ hnt hz1 hKK' hu
  have hK'cl : Q3.IsClassicalMember3 K' u :=
    isClassicalMember3_of_uniqueInvolution hs.stand.modU hK'Ω hu
  have hedge : EdgeSetup K z J K' t u := h.toEdgeSetup hint hs.hJ.1 hJK' hs.ht hu
  intro a ha b hb
  have haJ : a ∈ J := ha.1
  have haz : a ∈ Subgroup.centralizer ({z} : Set G) := ha.2
  have hbK' : b ∈ K' := hb.1
  have hbz : b ∈ Subgroup.centralizer ({z} : Set G) := hb.2
  have haz' : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haz
  have hat : a * t = t * a := isUniqueInvolution_comm hs.ht haJ
  have hau' : a ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hut]
    calc a * (z * t) = (a * z) * t := by group
      _ = (z * a) * t := by rw [haz']
      _ = z * (a * t) := by group
      _ = z * (t * a) := by rw [hat]
      _ = z * t * a := by group
  have hau : a ∈ J ⊓ Subgroup.centralizer ({u} : Set G) := ⟨haJ, hau'⟩
  have hO : a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf K' := by
    have := hedge.commutator_centM_le_oddCore hnab hBelow a hau b hbK'
    rw [commutatorElement_def] at this
    exact this
  have hnormK' : conjSub a K' = K' := hedge.conjSub_eq_of_mem_centM hnab hBelow a hau
  have hK'm : a * b * a⁻¹ * b⁻¹ ∈ K' := by
    have h1 : a * b * a⁻¹ ∈ K' := by
      have := conj_mem_conjSub (n := a) hbK'
      rwa [hnormK'] at this
    exact K'.mul_mem h1 (K'.inv_mem hbK')
  have hcen : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    have := (Subgroup.centralizer ({z} : Set G)).mul_mem
      ((Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.centralizer ({z} : Set G)).mul_mem haz hbz)
        ((Subgroup.centralizer ({z} : Set G)).inv_mem haz))
      ((Subgroup.centralizer ({z} : Set G)).inv_mem hbz)
    exact this
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (Q3NL.exactCore3 z K') := by
    rw [Q3NL.oddCoreIn_exactCore3 hK'cl hc2 hK'tq.2]
    exact ⟨⟨hK'm, hcen⟩, hO⟩
  exact Q3DB.oddCoreIn_exactCore3_le_exactLayer hΩ3 hc2 hBelow hnc hK'tq hK'cl hmem

end Gen

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
