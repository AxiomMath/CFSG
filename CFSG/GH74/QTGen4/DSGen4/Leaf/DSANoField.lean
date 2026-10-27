module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSANoField

theorem relIndex_sup_of_le_normalizer {G : Type} [Group G] {H N : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hH
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hH).toEquiv).symm

theorem side [DSLeaf LeafSylowS] [DSLeaf LeafM2] {G : Type} [Group G] [Finite4 G]
    {La Lb S : Subgroup G} (h : Hyp111R La Lb S) (hna : ¬ Group.IsSolvable ↥La) {d : G}
    (hd : d ∈ bigB La Lb S) (hdN : d ∈ Subgroup.normalizer (S : Set G)) (hd3 : orderOf d = 3) :
    S = (S ⊓ La) ⊔ dsQ La Lb S ∧ borelOf La S ≤ Subgroup.normalizer (S : Set G) := by
  set P := La ⊔ bigB La Lb S
  set Q := pCoreOf 2 P
  have hA : A5Par La P := A5Par.of_hyp111R Finite4.gen4 h hna
  have hsyl : IsSylowTwoOf S P := (sylow_s h).2.1
  have hQS : Q ≤ S := (sylow_s h).2.2
  have hrel : Q.relIndex S = 4 :=
    (m2 hA hsyl hQS).2.2 d (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hd, hdN⟩) hd3
  have hsylL : IsSylowTwoOf (S ⊓ La) La := h.hyp.h1.sylow
  have hcard : Nat.card ↥(S ⊓ La) = 4 * Nat.card ↥(pCoreOf 2 La) :=
    (DSBA5.three_and_card hsylL hA.quot).2
  have hpc : Q ⊓ La = pCoreOf 2 La := F1.inf_pCoreOf_parabolic_eq h
  have hpcQ : pCoreOf 2 La ≤ Q := by
    rw [← hpc]
    exact inf_le_left
  have hQSa : Q ⊓ (S ⊓ La) = pCoreOf 2 La := by
    apply le_antisymm
    · rw [← hpc]
      exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf hpcQ (F7.isSylowTwoOf_pCoreOf_le hsylL)
  have hrelA : Q.relIndex (S ⊓ La) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := S ⊓ La)
    rw [hQSa, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hSLQ : S ⊓ La ≤ Subgroup.normalizer (Q : Set G) :=
    (inf_le_right.trans (le_sup_left : La ≤ P)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hrelSup : Q.relIndex (S ⊓ La ⊔ Q) = 4 := by
    rw [relIndex_sup_of_le_normalizer hSLQ, hrelA]
  have hsupS : S ⊓ La ⊔ Q ≤ S := sup_le inf_le_left hQS
  have hSeq : S = S ⊓ La ⊔ Q := by
    have h1 := Subgroup.relIndex_mul_relIndex (H := Q) (K := S ⊓ La ⊔ Q) (L := S) le_sup_right hsupS
    rw [hrelSup, hrel] at h1
    have h2 : (S ⊓ La ⊔ Q).relIndex S = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hsupS
  have hBa : borelOf La S ≤ Subgroup.normalizer (S : Set G) := by
    have h1 : borelOf La S ≤ Subgroup.normalizer ((S ⊓ La : Subgroup G) : Set G) :=
      F1.borelOf_le_normalizer La S
    have h2 : borelOf La S ≤ Subgroup.normalizer (Q : Set G) :=
      ((F1.borelOf_le La S).trans (le_sup_left : La ≤ P)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    have h3 := F1.le_normalizer_sup h1 h2
    rw [← hSeq] at h3
    exact h3
  exact ⟨hSeq, hBa⟩

end DSANoField

theorem leafDSANoField [DSLeaf LeafSylowS] [DSLeaf LeafM2] [DSLeaf LeafFrattiniChief] : LeafDSANoField := by
  intro G _ _ L1 L2 S h
  have key : ∀ {d : G}, d ∈ bigB L1 L2 S → d ∈ Subgroup.normalizer (S : Set G) → orderOf d = 3 →
      S = (S ⊓ L1) ⊔ dsQ L1 L2 S ∧ S = (S ⊓ L2) ⊔ dsQ L2 L1 S ∧
        bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
    intro d hd hdN hd3
    obtain ⟨e1, b1⟩ := DSANoField.side h.hyp h.ns1 hd hdN hd3
    have hd' : d ∈ bigB L2 L1 S := by
      rw [bigB_comm]
      exact hd
    obtain ⟨e2, b2⟩ := DSANoField.side h.hyp.symm h.ns2 hd' hdN hd3
    exact ⟨e1, e2, sup_le (sup_le b1 b2) Subgroup.le_normalizer⟩
  rcases h.norm with hn | hn
  ·
    have hBN : borelOf L1 S ≤ Subgroup.normalizer (S : Set G) :=
      (le_sup_right : borelOf L1 S ≤ S ⊔ borelOf L1 S).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : S ≤ S ⊔ borelOf L1 S)).mp hn)
    obtain ⟨⟨d, hdB, hd3⟩, -⟩ :=
      DSBA5.three_and_card h.hyp.hyp.h1.sylow (A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1).quot
    exact key ((le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) hdB) (hBN hdB) hd3
  ·
    have hBN : borelOf L2 S ≤ Subgroup.normalizer (S : Set G) :=
      (le_sup_right : borelOf L2 S ≤ S ⊔ borelOf L2 S).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : S ≤ S ⊔ borelOf L2 S)).mp hn)
    obtain ⟨⟨d, hdB, hd3⟩, -⟩ :=
      DSBA5.three_and_card h.hyp.hyp.h2.sylow (A5Par.of_hyp111R Finite4.gen4 h.hyp.symm h.ns2).quot
    have hdB' : d ∈ bigB L1 L2 S := by
      have h1 : d ∈ bigB L2 L1 S := (le_sup_left.trans le_sup_left : borelOf L2 S ≤ bigB L2 L1 S) hdB
      rwa [bigB_comm] at h1
    exact key hdB' (hBN hdB) hd3

end CFSG.GH74.QTGen4.DSGen4
