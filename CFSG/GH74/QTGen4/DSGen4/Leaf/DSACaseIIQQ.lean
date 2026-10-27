module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSACaseIIQQ

theorem oTwoQuot_pStar_nonempty {G : Type} [Group G] [Finite G] {Li Lj S : Subgroup G}
    (h : Hyp111R Li Lj S) :
    Nonempty (oTwoQuot ↥Li ≃* oTwoQuot ↥(pStar Li (bigB Li Lj S))) := by
  have hLiPs : Li ≤ pStar Li (bigB Li Lj S) := le_sup_right
  have hQLi : pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤ Subgroup.normalizer (Li : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (F1.parabolic_le_normalizer h)
  let φ : ↥Li →* ↥(pStar Li (bigB Li Lj S)) ⧸ pCore 2 ↥(pStar Li (bigB Li Lj S)) :=
    (QuotientGroup.mk' (pCore 2 ↥(pStar Li (bigB Li Lj S)))).comp (Subgroup.inclusion hLiPs)
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := a
      have hx' : x ∈ pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ Li := hx
      obtain ⟨q, hq, l, hl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hQLi).mp hx'
      refine ⟨⟨l, hl⟩, ?_⟩
      have hqPs : q ∈ pCoreOf 2 (pStar Li (bigB Li Lj S)) := by
        rw [F1.pCoreOf_pStar h]; exact hq
      have e : (⟨q * l, hx⟩ : ↥(pStar Li (bigB Li Lj S))) =
          ⟨q, Subgroup.mem_sup_left hq⟩ * ⟨l, hLiPs hl⟩ := rfl
      show QuotientGroup.mk (⟨l, hLiPs hl⟩ : ↥(pStar Li (bigB Li Lj S))) =
        QuotientGroup.mk ⟨q * l, hx⟩
      have hq1 : (QuotientGroup.mk (⟨q, Subgroup.mem_sup_left hq⟩ :
          ↥(pStar Li (bigB Li Lj S))) : ↥(pStar Li (bigB Li Lj S)) ⧸
            pCore 2 ↥(pStar Li (bigB Li Lj S))) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr
          ((F1.mem_pCore_iff_coe (⟨q, Subgroup.mem_sup_left hq⟩ :
            ↥(pStar Li (bigB Li Lj S)))).mpr hqPs)
      rw [e, QuotientGroup.mk_mul, hq1, one_mul]
  have hker : pCore 2 ↥Li = φ.ker := by
    ext l
    rw [MonoidHom.mem_ker, F1.mem_pCore_iff_coe]
    show (l : G) ∈ pCoreOf 2 Li ↔
      QuotientGroup.mk (⟨l, hLiPs l.2⟩ : ↥(pStar Li (bigB Li Lj S))) = 1
    rw [QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]
    show (l : G) ∈ pCoreOf 2 Li ↔ (l : G) ∈ pCoreOf 2 (pStar Li (bigB Li Lj S))
    rw [F1.pCoreOf_pStar h]
    constructor
    · intro hl
      exact F1.pCoreOf_le_pCoreOf_parabolic h hl
    · intro hl
      rw [← F1.inf_pCoreOf_parabolic_eq h]
      exact ⟨hl, l.2⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

theorem isL2Quot_pStar {G : Type} [Group G] [Finite G] {Li Lj S : Subgroup G}
    (h : Hyp111R Li Lj S) (hq : IsL2Quot 2 (oTwoQuot ↥Li)) :
    IsL2Quot 2 (oTwoQuot ↥(pStar Li (bigB Li Lj S))) := by
  obtain ⟨e⟩ := hq
  obtain ⟨e'⟩ := oTwoQuot_pStar_nonempty h
  exact ⟨e'.symm.trans e⟩

theorem dsOmega1_centerOf_le {G : Type} [Group G] (X : Subgroup G) :
    dsOmega1 (centerOf X) ≤ X := by
  have hc : centerOf X ≤ X := inf_le_left
  exact (Subgroup.closure_le X).2 fun _ hx => hc hx.1

end DSACaseIIQQ

theorem leafDSACaseIIQQ [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIIOmega] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafM5] [DSLeaf LeafSylowS] : LeafDSACaseIIQQ := by
  intro G _ _ L1 L2 S h _ _
  obtain ⟨hdec1, hdec2, hbn⟩ := dsa_no_field h
  have hQ1S : dsQ L1 L2 S ≤ S := le_sup_right.trans hdec1.symm.le
  have hQ2S : dsQ L2 L1 S ≤ S := le_sup_right.trans hdec2.symm.le
  have hJS : dsQ L1 L2 S ⊔ dsQ L2 L1 S ≤ S := sup_le hQ1S hQ2S
  have hA1 : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hA2 : A5Par L2 (L2 ⊔ bigB L2 L1 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp.symm h.ns2
  have hsyl1 : IsSylowTwoOf S (pStar L1 (bigB L1 L2 S)) := by
    have e : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ (S ⊓ L1) = S := (sup_comm _ _).trans hdec1.symm
    have h0 := F1.isSylowTwoOf_pCoreOf_sup h.hyp
    rwa [e] at h0
  have hsyl2 : IsSylowTwoOf S (pStar L2 (bigB L2 L1 S)) := by
    have e : pCoreOf 2 (L2 ⊔ bigB L2 L1 S) ⊔ (S ⊓ L2) = S := (sup_comm _ _).trans hdec2.symm
    have h0 := F1.isSylowTwoOf_pCoreOf_sup h.hyp.symm
    rwa [e] at h0
  have hN1 : pStar L1 (bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) ≤ bigB L1 L2 S := by
    have e : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ (S ⊓ L1) = S := (sup_comm _ _).trans hdec1.symm
    have h0 := F1.pStar_inf_normalizer h.hyp
    rw [e] at h0
    rw [h0]
    exact sup_le (F1.pCoreOf_parabolic_le_bigB h.hyp) (le_sup_left.trans le_sup_left)
  have hN2 : pStar L2 (bigB L2 L1 S) ⊓ Subgroup.normalizer (S : Set G) ≤ bigB L2 L1 S := by
    have e : pCoreOf 2 (L2 ⊔ bigB L2 L1 S) ⊔ (S ⊓ L2) = S := (sup_comm _ _).trans hdec2.symm
    have h0 := F1.pStar_inf_normalizer h.hyp.symm
    rw [e] at h0
    rw [h0]
    exact sup_le (F1.pCoreOf_parabolic_le_bigB h.hyp.symm) (le_sup_left.trans le_sup_left)
  have hP1N : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hP2N : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hBQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    le_sup_right.trans hP1N
  have hBQ2 : bigB L2 L1 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
    le_sup_right.trans hP2N
  have hBQ1' : bigB L2 L1 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) := by
    rw [bigB_comm L1 L2 S]; exact hBQ1
  have hBQ2' : bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := by
    rw [← bigB_comm L1 L2 S]; exact hBQ2
  have hJ1 : pStar L1 (bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((dsQ L1 L2 S ⊔ dsQ L2 L1 S : Subgroup G) : Set G) :=
    hN1.trans (F1.le_normalizer_sup hBQ1 hBQ2')
  have hJ2 : pStar L2 (bigB L2 L1 S) ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((dsQ L1 L2 S ⊔ dsQ L2 L1 S : Subgroup G) : Set G) :=
    hN2.trans (F1.le_normalizer_sup hBQ1' hBQ2)
  have hQ1p : pCoreOf 2 (pStar L1 (bigB L1 L2 S)) = dsQ L1 L2 S := F1.pCoreOf_pStar h.hyp
  have hQ2p : pCoreOf 2 (pStar L2 (bigB L2 L1 S)) = dsQ L2 L1 S := F1.pCoreOf_pStar h.hyp.symm
  have hm1 := (m5 (DSACaseIIQQ.isL2Quot_pStar h.hyp hA1.quot) hsyl1).1
    (dsQ L1 L2 S ⊔ dsQ L2 L1 S) ((le_of_eq hQ1p).trans le_sup_left) hJS hJ1
  rcases hm1 with hJa | hJa
  ·
    have hm2 := (m5 (DSACaseIIQQ.isL2Quot_pStar h.hyp.symm hA2.quot) hsyl2).1
      (dsQ L1 L2 S ⊔ dsQ L2 L1 S) ((le_of_eq hQ2p).trans le_sup_right) hJS hJ2
    rcases hm2 with hJb | hJb
    · exfalso
      have hQeq : dsQ L1 L2 S = dsQ L2 L1 S := ((hQ1p.symm.trans hJa.symm).trans hJb).trans hQ2p
      have hQ1bot : dsQ L1 L2 S = ⊥ := by
        refine coreFree h.hyp.hyp ?_ (hQ1S.trans le_sup_right) (le_sup_left.trans hP1N) ?_ ?_
        · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
        · rw [hQeq]; exact le_sup_left.trans hP2N
        · exact (le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right.trans hP1N)
      have hz := zi_structure (⟨h.hyp, hbn⟩ : ZSetting L1 L2 S)
      have hzle : dsZ S ≤ dsQ L1 L2 S :=
        hz.2.1.trans (hz.2.2.1.trans (DSACaseIIQQ.dsOmega1_centerOf_le _))
      rw [hQ1bot, le_bot_iff] at hzle
      exact hz.1 hzle
    · exact hJb
  · exact hJa

end CFSG.GH74.QTGen4.DSGen4
