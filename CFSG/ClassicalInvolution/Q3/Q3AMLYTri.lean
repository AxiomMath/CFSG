module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Tri

variable {G : Type} [Group G] [Finite G]

theorem commutes_modOddIn_exactCore3_of_triangle [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z) {K' : Subgroup G}
    (hKK' : K' ∈ omegaNbr Ω K) (hJK' : K' ∈ omegaNbr Ω J) :
    Commutes (modOddIn (nbrLayer Ω K z) (exactCore3 z J))
      (modOddIn (nbrLayer Ω K z) (exactCore3 z K')) := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
  have hnab : ∃ x y : G, x * y ≠ y * x := h.nonabelian
  have hz : IsUniqueInvolution K z := hstd.hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hKK'.1
  have hut : u = z * t := h.eq_mul_of_nbr_nbr hKK' hJK' hu
  have hedge : EdgeSetup K z J K' t u := h.toEdgeSetup hint hstd.hJ.1 hJK' hstd.ht hu
  have hedgeK : EdgeSetup K z K K' z u := h.toEdgeSetup hint hstd.stand.mem hKK' hz hu
  have hK'cl : IsClassicalMember3 K' u :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hKK'.1 hu
  have hcK : z ∈ trivialOnQuot K' := trivialOnQuot_of_edge hedgeK hnab hBelow
  have hsec := isSectionMember3_exactCore3 hK'cl hc2 hcK
  have hcard := nbrLayer_exact_images h hint hstd.stand.mem hz K' hKK'
  have hcomm : ∀ a ∈ exactCore3 z J, ∀ b ∈ exactCore3 z K',
      ⁅a, b⁆ ∈ oddCoreOf (nbrLayer Ω K z) := by
    intro a ha b hb
    have haJ : a ∈ J := ha.1
    have haz : a ∈ Subgroup.centralizer ({z} : Set G) := ha.2
    have hbK' : b ∈ K' := hb.1
    have hbz : b ∈ Subgroup.centralizer ({z} : Set G) := hb.2
    have haz' : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haz
    have hat : a * t = t * a := isUniqueInvolution_comm hstd.ht haJ
    have hau' : a ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hut]
      calc a * (z * t) = (a * z) * t := by group
        _ = (z * a) * t := by rw [haz']
        _ = z * (a * t) := by group
        _ = z * (t * a) := by rw [hat]
        _ = z * t * a := by group
    have hau : a ∈ J ⊓ Subgroup.centralizer ({u} : Set G) := ⟨haJ, hau'⟩
    have hO : ⁅a, b⁆ ∈ oddCoreOf K' := hedge.commutator_centM_le_oddCore hnab hBelow a hau b hbK'
    have hnormK' : conjSub a K' = K' := hedge.conjSub_eq_of_mem_centM hnab hBelow a hau
    have hK'm : ⁅a, b⁆ ∈ K' := by
      have h1 : a * b * a⁻¹ ∈ K' := mem_of_conjSub_eq hnormK' hbK'
      rw [commutatorElement_def]
      exact K'.mul_mem h1 (K'.inv_mem hbK')
    have hcen : ⁅a, b⁆ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [commutatorElement_def]
      exact (Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.centralizer ({z} : Set G)).mul_mem
          ((Subgroup.centralizer ({z} : Set G)).mul_mem haz hbz)
          ((Subgroup.centralizer ({z} : Set G)).inv_mem haz))
        ((Subgroup.centralizer ({z} : Set G)).inv_mem hbz)
    have hO' : ⁅a, b⁆ ∈ oddCoreOf (exactCore3 z K') := by
      have h1 : Balance.oddCoreIn (exactCore3 z K') = exactCore3 z K' ⊓ Balance.oddCoreIn K' :=
        oddCoreIn_exactCore3 hK'cl hc2 hcK
      have h2 : ⁅a, b⁆ ∈ Balance.oddCoreIn (exactCore3 z K') := by
        rw [h1]
        exact ⟨⟨hK'm, hcen⟩, hO⟩
      exact h2
    exact oddCoreOf_le_of_card_image (exactCore3_le_nbrLayer hKK') hcard hsec.nonempty_equiv hO'
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  refine (mk_comm_eq_iff x.2 y.2).mpr ?_
  have := hcomm _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)
  rwa [commutatorElement_def] at this

end Tri

end CFSG.ClassicalInvolution.Q3.Q3AM
