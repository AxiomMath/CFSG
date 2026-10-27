module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem dsaCaseI_omega1_centerOf_le {G : Type} [Group G] (Q : Subgroup G) :
    dsOmega1 (centerOf Q) ≤ Q :=
  ((Subgroup.closure_le (centerOf Q)).2 fun _ hx => hx.1).trans inf_le_left

theorem dsaCaseI_le_of_sup_frattini {G : Type} [Group G] [Finite G] {Q M : Subgroup G}
    (hM : M ≤ Q) (h : M ⊔ dsFrattini Q = Q) : Q ≤ M := by
  have hA : M.subgroupOf Q ⊔ frattini ↥Q = ⊤ := by
    apply Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have hAtop : M.subgroupOf Q = ⊤ := frattini_nongenerating hA
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥Q) ∈ M.subgroupOf Q := by
    rw [hAtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem dsaCaseI_comm_mem {G : Type} [Group G] {Q Z : Subgroup G} {z q : G}
    (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hqN : q ∈ Subgroup.normalizer (Z : Set G))
    (hz : z ∈ Z) (hq : q ∈ Q) : ⁅z, q⁆ ∈ Z ⊓ Q := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : q * z * q⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hqN z).mp hz
    have e : ⁅z, q⁆ = z * (q * z * q⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem hz (Z.inv_mem h1)
  · have h2 : z * q * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hzN q).mp hq
    rw [commutatorElement_def]
    exact Q.mul_mem h2 (Q.inv_mem hq)

theorem dsaCaseI_half {G : Type} [Group G] [Finite4 G]
    [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIOffender] [DSLeaf LeafFrattiniChief]
    [DSLeaf LeafFrattiniFaithful] [DSLeaf LeafZiStructure] [DSLeaf LeafSylowS]
    {La Lb S : Subgroup G} (h : DSAHyp La Lb S)
    (ca : ⁅dsZi La S, La⁆ ≠ ⊥) (cb : ⁅dsZi Lb S, Lb⁆ ≠ ⊥) :
    dsQ La Lb S = dsZi La S := by
  have hZS : ZSetting La Lb S := ⟨h.hyp, (dsa_no_field h).2.2⟩
  obtain ⟨-, -, hZa_Om, -, -, hZa_N, -⟩ := zi_structure hZS
  obtain ⟨-, -, hZb_Om, -, -, hZb_N, -⟩ := zi_structure hZS.symm
  obtain ⟨-, hNoff2, -, -, hint_eq, -, -⟩ := dsa_case_i_offender h ca cb
  have hZa_Q : dsZi La S ≤ dsQ La Lb S := hZa_Om.trans (dsaCaseI_omega1_centerOf_le _)
  have hQa_S : dsQ La Lb S ≤ S := (sylow_s h.hyp).2.2
  have hQb_S : dsQ Lb La S ≤ S := (sylow_s h.hyp.symm).2.2
  have hZb_S : dsZi Lb S ≤ S := (hZb_Om.trans (dsaCaseI_omega1_centerOf_le _)).trans hQb_S
  have hS_B : S ≤ bigB La Lb S := le_sup_right
  have hS_Pa : S ≤ La ⊔ bigB La Lb S := hS_B.trans le_sup_right
  have hS_Pb : S ≤ Lb ⊔ bigB Lb La S := (le_sup_right : S ≤ bigB Lb La S).trans le_sup_right
  have hPa_Qa : La ⊔ bigB La Lb S ≤ Subgroup.normalizer (dsQ La Lb S : Set G) :=
    CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 _
  have hS_Qa : S ≤ Subgroup.normalizer (dsQ La Lb S : Set G) := hS_Pa.trans hPa_Qa
  have hS_Zb : S ≤ Subgroup.normalizer (dsZi Lb S : Set G) := hS_Pb.trans hZb_N
  have hA5 : A5Par La (La ⊔ bigB La Lb S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hC := frattini_chief hA5
  have hΦ_Q : dsFrattini (dsQ La Lb S) ≤ dsQ La Lb S := Subgroup.map_subtype_le _
  have hX := hC.irred (dsFrattini (dsQ La Lb S) ⊔ dsZi La S) le_sup_left (sup_le hΦ_Q hZa_Q)
    (CFSG.Quasithin.F1.le_normalizer_sup hC.norm_K hZa_N)
  rcases hX with hX | hX
  ·
    exfalso
    have hZΦ : dsZi La S ≤ dsFrattini (dsQ La Lb S) := le_of_le_of_eq le_sup_right hX
    have hint : dsZi Lb S ⊓ dsQ La Lb S ≤ dsZi La S := by
      rw [← hint_eq]; exact inf_le_left
    have hZbQ : dsZi Lb S ≤ dsQ La Lb S := fun z hz =>
      CFSG.GH74.QTGen4.DSGen4.frattini_faithful hA5.charTwo z (hS_Pa (hZb_S hz))
        (fun q hq => hZΦ (hint (dsaCaseI_comm_mem (hS_Qa (hZb_S hz)) (hS_Zb (hQa_S hq)) hz hq)))
    exact hNoff2 hZbQ
  ·
    have hsup : dsZi La S ⊔ dsFrattini (dsQ La Lb S) = dsQ La Lb S := (sup_comm _ _).trans hX
    exact (le_antisymm hZa_Q (dsaCaseI_le_of_sup_frattini hZa_Q hsup)).symm

theorem leafDSACaseIFrattini [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIOffender] [DSLeaf LeafFrattiniChief] [DSLeaf LeafFrattiniFaithful] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafSylowS] : LeafDSACaseIFrattini := by
  intro G _ _ L1 L2 S h c1 c2
  exact ⟨dsaCaseI_half h c1 c2, dsaCaseI_half h.symm c2 c1⟩

end CFSG.GH74.QTGen4.DSGen4
