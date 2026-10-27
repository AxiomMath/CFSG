module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem step4_card_le_four {X : Type} [Group X] [Finite X] (hX : Nat.card X = 60)
    {H : Subgroup X} (hH : IsPGroup 2 H) : Nat.card H ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hH
  have hdvd : Nat.card H ∣ 60 := by
    rw [← hX]
    exact Subgroup.card_subgroup_dvd_card H
  rw [hk] at hdvd ⊢
  have hk2 : k ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    norm_num at this
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

private theorem step4_relIndex_ne_zero {G : Type} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

private theorem step4_relIndex_pCoreOf {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hTL : T ≤ L) (hT : IsPGroup 2 T) :
    (pCoreOf 2 L).relIndex T ≤ 4 := by
  have hcard : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [IsL2Quot.card (by norm_num) hq]
    norm_num
  have hTl : IsPGroup 2 (T.subgroupOf L) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hR : (pCoreOf 2 L).subgroupOf L = pCore 2 ↥L :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective L) _
  have hker : (QuotientGroup.mk' (pCore 2 ↥L) : ↥L →* oTwoQuot ↥L).ker = pCore 2 ↥L :=
    QuotientGroup.ker_mk' _
  have h1 := Subgroup.relIndex_subgroupOf (H := pCoreOf 2 L) (K := T) (L := L) hTL
  rw [hR] at h1
  have h2 := Subgroup.relIndex_ker (T.subgroupOf L) (QuotientGroup.mk' (pCore 2 ↥L))
  rw [hker] at h2
  have h3 : Nat.card ↥((T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) ≤ 4 :=
    step4_card_le_four hcard (hTl.map _)
  rw [← h1, h2]
  exact h3

private theorem step4_relIndex_le_four {G : Type} [Group G] [Finite G] {L1 S Q : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L1)) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (Q : Set G)) (hQS : Q ≤ S) (hSQ : S = (S ⊓ L1) ⊔ Q)
    (hRQ : pCoreOf 2 L1 ≤ Q) : Q.relIndex S ≤ 4 := by
  haveI : (Q.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQS).mpr hSN
  have hsup : (S ⊓ L1).subgroupOf S ⊔ Q.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup inf_le_left hQS, ← hSQ, Subgroup.subgroupOf_self]
  have key := Subgroup.relIndex_sup_right (H := (S ⊓ L1).subgroupOf S) (K := Q.subgroupOf S)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf inf_le_left] at key
  have hE : Q.relIndex S = Q.relIndex (S ⊓ L1) := key
  have hR0 : (pCoreOf 2 L1).relIndex (S ⊓ L1) ≠ 0 := step4_relIndex_ne_zero _ _
  have hle : Q.relIndex (S ⊓ L1) ≤ (pCoreOf 2 L1).relIndex (S ⊓ L1) :=
    Subgroup.relIndex_le_of_le_left hRQ hR0
  have hT : (pCoreOf 2 L1).relIndex (S ⊓ L1) ≤ 4 :=
    step4_relIndex_pCoreOf hq (inf_le_right : S ⊓ L1 ≤ L1) hS2.to_inf_left
  omega

private theorem step4_join {G : Type} [Group G] [Finite G] {S Q1 Q2 : Subgroup G}
    (h1 : Q1 ≤ S) (h2 : Q2 ≤ S) (hi : Q1.relIndex S ≤ 4)
    (hc1 : Nat.card Q1 = 16) (hc2 : Nat.card Q2 = 16) (hI : Nat.card ↥(Q1 ⊓ Q2) = 4) :
    Q1 ⊔ Q2 = S ∧ Nat.card S = 2 ^ 6 := by
  have hQ1M : Q1 ≤ Q1 ⊔ Q2 := le_sup_left
  have hQ2M : Q2 ≤ Q1 ⊔ Q2 := le_sup_right
  have hMS : Q1 ⊔ Q2 ≤ S := sup_le h1 h2
  have ea : Q1.relIndex (Q1 ⊔ Q2) * 16 = Nat.card ↥(Q1 ⊔ Q2) := by
    have h := Subgroup.relIndex_mul_card (H := Q1) (K := Q1 ⊔ Q2)
    rwa [inf_eq_left.mpr hQ1M, hc1] at h
  have eb : Q2.relIndex (Q1 ⊔ Q2) * 16 = Nat.card ↥(Q1 ⊔ Q2) := by
    have h := Subgroup.relIndex_mul_card (H := Q2) (K := Q1 ⊔ Q2)
    rwa [inf_eq_left.mpr hQ2M, hc2] at h
  have ec : (Q1 ⊓ Q2).relIndex (Q1 ⊔ Q2) * 4 = Nat.card ↥(Q1 ⊔ Q2) := by
    have h := Subgroup.relIndex_mul_card (H := Q1 ⊓ Q2) (K := Q1 ⊔ Q2)
    rwa [inf_eq_left.mpr (inf_le_left.trans hQ1M), hI] at h
  have hle := Subgroup.relIndex_inf_le (H := Q1) (K := Q2) (L := Q1 ⊔ Q2)
  have hm := Subgroup.relIndex_mul_relIndex (H := Q1) (K := Q1 ⊔ Q2) (L := S) hQ1M hMS
  have hQ1S0 : Q1.relIndex S ≠ 0 := step4_relIndex_ne_zero _ _
  have hN0 : 0 < Nat.card ↥(Q1 ⊔ Q2) := Nat.card_pos
  obtain ⟨a, ha⟩ : ∃ a, Q1.relIndex (Q1 ⊔ Q2) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, Q2.relIndex (Q1 ⊔ Q2) = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (Q1 ⊓ Q2).relIndex (Q1 ⊔ Q2) = c := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, Nat.card ↥(Q1 ⊔ Q2) = N := ⟨_, rfl⟩
  obtain ⟨m, hm'⟩ : ∃ m, (Q1 ⊔ Q2).relIndex S = m := ⟨_, rfl⟩
  rw [ha, hm'] at hm
  rw [ha, hN] at ea
  rw [hb, hN] at eb
  rw [hc, hN] at ec
  rw [ha, hb, hc] at hle
  rw [hN] at hN0
  have hab : b = a := by omega
  rw [hab] at hle
  have hc4 : c = 4 * a := by omega
  rw [hc4] at hle
  have ha0 : 0 < a := by omega
  have ha4 : 4 ≤ a := by nlinarith
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact hQ1S0 hm.symm
  have hm1 : m = 1 := by
    have : m ≤ 1 := by nlinarith
    omega
  subst hm1
  have hMeq : Q1 ⊔ Q2 = S := le_antisymm hMS (Subgroup.relIndex_eq_one.mp hm')
  rw [mul_one] at hm
  have ha4' : a = 4 := by omega
  have hN64 : N = 64 := by omega
  refine ⟨hMeq, ?_⟩
  rw [← hMeq, hN, hN64]
  norm_num

private theorem step4_elemAbelian {G : Type} [Group G] {E : Subgroup G} (h : IsElemSec ⊥ E) :
    IsElemAbelian 2 E := by
  obtain ⟨-, hc, hsq⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => Subgroup.mem_bot.mp (hsq x hx)⟩
  have h1 : ⁅(a : G), (b : G)⁆ = 1 :=
    Subgroup.mem_bot.mp (hc (Subgroup.commutator_mem_commutator a.2 b.2))
  exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h1)

theorem leafDSACaseIStep4 [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIOffender] [DSLeaf LeafDSACaseIFrattini] [DSLeaf LeafSylowS] [DSLeaf LeafZiChief] : LeafDSACaseIStep4 := by
  intro G _ _ L1 L2 S h c1 c2
  obtain ⟨hNF1, -, hBN⟩ := dsa_no_field h
  obtain ⟨-, -, -, -, -, -, hI⟩ := dsa_case_i_offender h c1 c2
  obtain ⟨hF1, hF2⟩ := dsa_case_i_frattini h c1 c2
  obtain ⟨-, hSP1, hQS1⟩ := sylow_s h.hyp
  obtain ⟨-, -, hQS2⟩ := sylow_s h.hyp.symm
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) := (A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1).quot
  have hq2 : IsL2Quot 2 (oTwoQuot ↥L2) := (A5Par.of_hyp111R Finite4.gen4 h.hyp.symm h.ns2).quot
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, hBN⟩
  obtain ⟨hA1, -⟩ := zi_chief hZS hq1 c1
  obtain ⟨hA2, -⟩ := zi_chief hZS.symm hq2 c2
  have hc1 : Nat.card (dsZi L1 S) = 16 := by
    have := hA1.card
    rwa [Subgroup.relIndex_bot_left] at this
  have hc2 : Nat.card (dsZi L2 S) = 16 := by
    have := hA2.card
    rwa [Subgroup.relIndex_bot_left] at this
  have he1 : IsElemAbelian 2 (dsZi L1 S) := step4_elemAbelian hA1.sec
  have he2 : IsElemAbelian 2 (dsZi L2 S) := step4_elemAbelian hA2.sec
  have hQS1' : dsQ L1 L2 S ≤ S := hQS1
  have hQS2' : dsQ L2 L1 S ≤ S := hQS2
  have hSN1 : S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    hSP1.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
  have hi1 : (dsQ L1 L2 S).relIndex S ≤ 4 :=
    step4_relIndex_le_four (Q := dsQ L1 L2 S) hq1 hSP1.2.1 hSN1 hQS1' hNF1
      (F1.pCoreOf_le_pCoreOf_parabolic h.hyp)
  obtain ⟨hJ, hS⟩ := step4_join (Q1 := dsQ L1 L2 S) (Q2 := dsQ L2 L1 S) hQS1' hQS2' hi1
    (by rw [hF1]; exact hc1) (by rw [hF2]; exact hc2) (by rw [hF1, hF2]; exact hI)
  refine ⟨hJ, hS, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hF1]
    exact he1
  · rw [hF1]
    exact hc1
  · rw [hF2]
    exact he2
  · rw [hF2]
    exact hc2

end CFSG.GH74.QTGen4.DSGen4
