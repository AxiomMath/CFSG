module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem dsa3_comm_mul_right {G : Type} [Group G] {z a b : G} (hb : b * z = z * b) :
    ⁅z, a * b⁆ = ⁅z, a⁆ := by
  have hb' : b * z⁻¹ = z⁻¹ * b := (Commute.inv_right (show Commute b z from hb)).eq
  rw [commutatorElement_def, commutatorElement_def]
  calc z * (a * b) * z⁻¹ * (a * b)⁻¹ = z * a * (b * z⁻¹) * (b⁻¹ * a⁻¹) := by group
    _ = z * a * (z⁻¹ * b) * (b⁻¹ * a⁻¹) := by rw [hb']
    _ = z * a * z⁻¹ * a⁻¹ := by group

private theorem dsa3_comm_mul_left {G : Type} [Group G] {z r q : G} (hr : r * z = z * r) :
    ⁅z, r * q⁆ = r * ⁅z, q⁆ * r⁻¹ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z * (r * q) * z⁻¹ * (r * q)⁻¹ = (z * r) * q * z⁻¹ * (q⁻¹ * r⁻¹) := by group
    _ = (r * z) * q * z⁻¹ * (q⁻¹ * r⁻¹) := by rw [hr.symm]
    _ = r * (z * q * z⁻¹ * q⁻¹) * r⁻¹ := by group

private theorem dsa3_mem_normalizer_inf {G : Type} [Group G] {g : G} {H K : Subgroup G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hH x) (hK x)

private theorem dsa3_mem_normalizer_sup {G : Type} [Group G] {g : G} {H K : Subgroup G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  F1.le_normalizer_sup (X := Subgroup.zpowers g) (Subgroup.zpowers_le.mpr hH)
    (Subgroup.zpowers_le.mpr hK) (Subgroup.mem_zpowers g)

theorem leafDSACaseIIStep3 [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIIOmega] [DSLeaf LeafDSACaseIIQQ] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafM3] [DSLeaf LeafM5] [DSLeaf LeafFrattiniChief] [DSLeaf LeafFrattiniFaithful] [DSLeaf LeafSylowS] : LeafDSACaseIIStep3 := by
  intro G _ _ L1 L2 S h c2 c1
  have hG : CFSG.GH74.Gen4 G := Finite4.gen4
  obtain ⟨hdec1, hdec2, hBN⟩ := dsa_no_field h
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, hBN⟩
  obtain ⟨-, -, -, -, -, hZiN, -⟩ := zi_structure hZS
  obtain ⟨hA5, hZiEq, hZS_eq, -⟩ := zi_chief hZS (CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 hG h.hyp.hyp.h1 h.ns1) c1
  obtain ⟨-, hOmFr⟩ := dsa_case_ii_omega h c2 c1
  have hQQ : dsQ L1 L2 S ⊔ dsQ L2 L1 S = S := dsa_case_iiqq h c2 c1
  obtain ⟨-, -, hQ1S⟩ := sylow_s h.hyp
  have hQ2S : dsQ L2 L1 S ≤ S := (sylow_s h.hyp.symm).2.2
  have hOmC : dsOmega1 (centerOf (dsQ L1 L2 S)) ≤ centerOf (dsQ L1 L2 S) :=
    (Subgroup.closure_le _).2 fun x hx => hx.1
  have hZ1Q1 : dsZi L1 S ≤ dsQ L1 L2 S := by
    rw [hZiEq]; exact hOmC.trans inf_le_left
  have hZ1S : dsZi L1 S ≤ S := hZ1Q1.trans hQ1S
  have hZ1cent : ∀ e ∈ dsZi L1 S, ∀ q ∈ dsQ L1 L2 S, q * e = e * q := by
    intro e he q hq
    have he2 : e ∈ dsOmega1 (centerOf (dsQ L1 L2 S)) := by rw [← hZiEq]; exact he
    exact Subgroup.mem_centralizer_iff.mp (hOmC he2).2 q hq
  have hSP1 : S ≤ L1 ⊔ bigB L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSP2 : S ≤ L2 ⊔ bigB L2 L1 S := (le_sup_right : S ≤ bigB L2 L1 S).trans le_sup_right
  have hN_Q1 : S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    hSP1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
  have hN_Q2 : S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
    hSP2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L2 ⊔ bigB L2 L1 S))
  have hS1N : S ⊓ L1 ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) := inf_le_left.trans hN_Q1
  have hS2N : S ⊓ L2 ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := inf_le_left.trans hN_Q2
  have hZ1N : dsZi L1 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := hZ1S.trans hN_Q2
  have hQ1N : dsQ L1 L2 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := hQ1S.trans hN_Q2
  have hZ1comm : ∀ z ∈ dsZi L1 S, ∀ g ∈ S, ⁅z, g⁆ ∈ dsZi L1 S := by
    intro z hz g hg
    rw [commutatorElement_def]
    have hconj : g * z⁻¹ * g⁻¹ ∈ dsZi L1 S :=
      (Subgroup.mem_normalizer_iff.mp (hZiN (hSP1 hg)) z⁻¹).mp (Subgroup.inv_mem _ hz)
    have e : z * g * z⁻¹ * g⁻¹ = z * (g * z⁻¹ * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hz hconj
  have hC2 : CharTwo (L2 ⊔ bigB L2 L1 S) := F1.parabolic_charTwo h.hyp.symm
  have hcardZ1 : Nat.card (dsZi L1 S) = 16 := by
    have h16 := hA5.card
    rw [Subgroup.relIndex_bot_left] at h16
    exact h16
  have hT1 : IsSylowTwoOf (S ⊓ L1) L1 := h.hyp.hyp.h1.sylow
  have hT2 : IsSylowTwoOf (S ⊓ L2) L2 := h.hyp.hyp.h2.sylow
  have hq2 : IsL2Quot 2 (oTwoQuot ↥L2) :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 hG h.hyp.hyp.h2 h.ns2
  have hnat_case : NatSec L1 ⊥ (dsZi L1 S) → dsZi L1 S ≤ dsQ L2 L1 S := by
    intro hnat
    obtain ⟨-, -, hcent, -, -⟩ := (m3 hA5 hT1).1 hnat
    intro z hz
    refine frattini_faithful hC2 z (hSP2 (hZ1S hz)) (fun q hq => ?_)
    have hqS : q ∈ S := hQ2S hq
    have hqS' : q ∈ S ⊓ L1 ⊔ dsQ L1 L2 S :=
      (congrArg (fun T : Subgroup G => q ∈ T) hdec1).mp hqS
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hS1N).mp hqS'
    have haS : a ∈ S := (Subgroup.mem_inf.mp ha).1
    have hf1 : ⁅z, a⁆ ∈ dsZi L1 S := hZ1comm z hz a haS
    have hf2 : ⁅z, a⁆ ∈ ⁅dsZi L1 S, S ⊓ L1⁆ ⊔ ⊥ := by
      rw [sup_bot_eq]
      exact Subgroup.commutator_mem_commutator hz ha
    have hfcent : ⁅z, a⁆ ∈ Subgroup.centralizer (S : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
      have hg' : g ∈ S ⊓ L1 ⊔ dsQ L1 L2 S :=
        (congrArg (fun T : Subgroup G => g ∈ T) hdec1).mp (SetLike.mem_coe.mp hg)
      obtain ⟨a', ha', b', hb', rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hS1N).mp hg'
      have hfa' : ⁅z, a⁆ * a' = a' * ⁅z, a⁆ :=
        commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hcent a' ha' _ hf2))
      have hfb' : b' * ⁅z, a⁆ = ⁅z, a⁆ * b' := hZ1cent _ hf1 b' hb'
      calc a' * b' * ⁅z, a⁆ = a' * (b' * ⁅z, a⁆) := mul_assoc _ _ _
        _ = a' * (⁅z, a⁆ * b') := by rw [hfb']
        _ = (a' * ⁅z, a⁆) * b' := (mul_assoc _ _ _).symm
        _ = (⁅z, a⁆ * a') * b' := by rw [hfa']
        _ = ⁅z, a⁆ * (a' * b') := mul_assoc _ _ _
    have hfZ : ⁅z, a⁆ ∈ dsZ S := by
      rw [hZS_eq]
      exact Subgroup.mem_inf.mpr ⟨hf1, hfcent⟩
    rw [dsa3_comm_mul_right (hZ1cent z hz b hb)]
    exact hOmFr hfZ
  have horth_case : ¬ NatSec L1 ⊥ (dsZi L1 S) → dsZi L1 S ≤ dsQ L2 L1 S := by
    intro hnat
    obtain ⟨-, -, h8, -⟩ := (m3 hA5 hT1).2 hnat
    rw [Subgroup.relIndex_bot_left, sup_bot_eq] at h8
    have hC_le : ⁅dsZi L1 S, S ⊓ L1⁆ ≤ dsQ L2 L1 S ⊓ dsZi L1 S := by
      refine Subgroup.commutator_le.mpr fun z hz a ha => ?_
      have haS : a ∈ S := (Subgroup.mem_inf.mp ha).1
      have haQ : a ∈ dsQ L1 L2 S ⊔ dsQ L2 L1 S :=
        (congrArg (fun T : Subgroup G => a ∈ T) hQQ.symm).mp haS
      obtain ⟨r, hr, q', hq', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hQ1N).mp haQ
      have hrz : r * z = z * r := hZ1cent z hz r hr
      have hq'S : q' ∈ S := hQ2S hq'
      have hx1 : ⁅z, q'⁆ ∈ dsZi L1 S := hZ1comm z hz q' hq'S
      have hx2 : ⁅z, q'⁆ ∈ dsQ L2 L1 S := by
        rw [commutatorElement_def]
        have h1 : z * q' * z⁻¹ ∈ dsQ L2 L1 S :=
          (Subgroup.mem_normalizer_iff.mp (hN_Q2 (hZ1S hz)) q').mp hq'
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hq')
      have hrx : r * ⁅z, q'⁆ = ⁅z, q'⁆ * r := hZ1cent _ hx1 r hr
      rw [dsa3_comm_mul_left hrz, hrx, mul_inv_cancel_right]
      exact Subgroup.mem_inf.mpr ⟨hx2, hx1⟩
    have hO60 : (pCoreOf 2 L2).relIndex L2 = 60 := by
      have e2 : (pCoreOf 2 L2).subgroupOf L2 = pCore 2 ↥L2 := by
        ext x
        rw [Subgroup.mem_subgroupOf]
        exact (F1.mem_pCore_iff_coe x).symm
      have e1 : (pCoreOf 2 L2).relIndex L2 = Nat.card (oTwoQuot ↥L2) :=
        congrArg (fun K : Subgroup ↥L2 => K.index) e2
      rw [e1]
      obtain ⟨e⟩ := hq2
      calc Nat.card (oTwoQuot ↥L2)
          = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
            Nat.card_congr e.toEquiv
        _ = 2 ^ 2 * ((2 ^ 2) ^ 2 - 1) := CFSG.Walter.psl2_even_card (by norm_num)
        _ = 60 := by norm_num
    have hmul : (pCoreOf 2 L2).relIndex (S ⊓ L2) * (S ⊓ L2).relIndex L2 = 60 := by
      rw [← hO60]
      exact Subgroup.relIndex_mul_relIndex _ _ _
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT2) inf_le_right
    have hodd : ¬ 2 ∣ (S ⊓ L2).relIndex L2 := CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hT2
    have hO4 : (pCoreOf 2 L2).relIndex (S ⊓ L2) = 4 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (pCoreOf 2 L2).relIndex (S ⊓ L2) = 2 ^ n :=
        hT2.2.1.index ((pCoreOf 2 L2).subgroupOf (S ⊓ L2))
      rw [hn] at hmul ⊢
      have hb : 0 < (S ⊓ L2).relIndex L2 := by
        rcases Nat.eq_zero_or_pos ((S ⊓ L2).relIndex L2) with h0 | h0
        · rw [h0, mul_zero] at hmul
          omega
        · exact h0
      have h3 : 2 ^ n ≤ 60 := by
        rw [← hmul]
        exact Nat.le_mul_of_pos_right _ hb
      have hn6 : n < 6 := by
        by_contra hcon
        have hcon' : 6 ≤ n := by omega
        have h1 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon'
        norm_num at h1
        omega
      have hn2 : n = 2 := by
        interval_cases n <;> first | rfl | (norm_num at hmul <;> omega)
      subst hn2
      norm_num
    have hQ2inf : dsQ L2 L1 S ⊓ (S ⊓ L2) = pCoreOf 2 L2 := by
      apply le_antisymm
      · intro x hx
        have hxQ : x ∈ pCoreOf 2 (L2 ⊔ bigB L2 L1 S) := (Subgroup.mem_inf.mp hx).1
        have hxL2 : x ∈ L2 := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2
        have hxin : x ∈ pCoreOf 2 (L2 ⊔ bigB L2 L1 S) ⊓ L2 :=
          Subgroup.mem_inf.mpr ⟨hxQ, hxL2⟩
        rw [F1.inf_pCoreOf_parabolic_eq h.hyp.symm] at hxin
        exact hxin
      · exact le_inf (F1.pCoreOf_le_pCoreOf_parabolic h.hyp.symm)
          (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT2)
    have hQ2idx : (dsQ L2 L1 S).relIndex S = 4 := by
      calc (dsQ L2 L1 S).relIndex S
          = (dsQ L2 L1 S).relIndex (S ⊓ L2 ⊔ dsQ L2 L1 S) := by rw [← hdec2]
        _ = (dsQ L2 L1 S).relIndex (S ⊓ L2) := F1.relIndex_sup_eq_of_le_normalizer hS2N
        _ = (dsQ L2 L1 S ⊓ (S ⊓ L2)).relIndex (S ⊓ L2) :=
          (Subgroup.inf_relIndex_right _ _).symm
        _ = (pCoreOf 2 L2).relIndex (S ⊓ L2) := by rw [hQ2inf]
        _ = 4 := hO4
    have hO2 : pCoreOf 2 L2 ≤ (dsZi L1 S ⊔ dsQ L2 L1 S) ⊓ (S ⊓ L2) :=
      le_inf ((F1.pCoreOf_le_pCoreOf_parabolic h.hyp.symm).trans le_sup_right)
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT2)
    have hN5 : L2 ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) ≤
        Subgroup.normalizer (((dsZi L1 S ⊔ dsQ L2 L1 S) ⊓ (S ⊓ L2) : Subgroup G) : Set G) := by
      intro g hg
      have e : L2 ⊓ bigB L1 L2 S = L2 ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
        rw [← bigB_comm]
        exact F1.inf_bigB_eq_borelOf h.hyp.symm
      have hgB : g ∈ L2 ⊓ bigB L1 L2 S := by
        rw [e]
        exact hg
      have hgB2 : g ∈ bigB L2 L1 S := by
        rw [bigB_comm]
        exact (Subgroup.mem_inf.mp hgB).2
      have hgZ : g ∈ Subgroup.normalizer (dsZi L1 S : Set G) :=
        hZiN ((le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) (Subgroup.mem_inf.mp hgB).2)
      have hgQ : g ∈ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L2 ⊔ bigB L2 L1 S)
          ((le_sup_right : bigB L2 L1 S ≤ L2 ⊔ bigB L2 L1 S) hgB2)
      exact dsa3_mem_normalizer_inf (dsa3_mem_normalizer_sup hgZ hgQ) (Subgroup.mem_inf.mp hg).2
    have hdich := (m5 hq2 hT2).1 ((dsZi L1 S ⊔ dsQ L2 L1 S) ⊓ (S ⊓ L2)) hO2 inf_le_right hN5
    rcases hdich with hO | hTT
    ·
      intro z hz
      have hzS : z ∈ S := hZ1S hz
      have hzd : z ∈ S ⊓ L2 ⊔ dsQ L2 L1 S :=
        (congrArg (fun T : Subgroup G => z ∈ T) hdec2).mp hzS
      obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hS2N).mp hzd
      have hAZ : a ∈ dsZi L1 S ⊔ dsQ L2 L1 S := by
        have key : a * b * b⁻¹ ∈ dsZi L1 S ⊔ dsQ L2 L1 S :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_left hz)
            (Subgroup.mem_sup_right (Subgroup.inv_mem _ hb))
        rwa [mul_inv_cancel_right] at key
      have haX : a ∈ (dsZi L1 S ⊔ dsQ L2 L1 S) ⊓ (S ⊓ L2) :=
        Subgroup.mem_inf.mpr ⟨hAZ, ha⟩
      rw [hO] at haX
      exact Subgroup.mul_mem _ (F1.pCoreOf_le_pCoreOf_parabolic h.hyp.symm haX) hb
    ·
      exfalso
      have hS2le : S ⊓ L2 ≤ dsZi L1 S ⊔ dsQ L2 L1 S :=
        (le_of_eq hTT.symm).trans inf_le_left
      have hSZ : dsZi L1 S ⊔ dsQ L2 L1 S = S :=
        le_antisymm (sup_le hZ1S hQ2S) (le_trans (le_of_eq hdec2) (sup_le hS2le le_sup_right))
      have h4Q : (dsQ L2 L1 S).relIndex (dsZi L1 S ⊔ dsQ L2 L1 S) = 4 := by
        rw [hSZ]
        exact hQ2idx
      rw [F1.relIndex_sup_eq_of_le_normalizer hZ1N] at h4Q
      have hmulC := Subgroup.relIndex_mul_card (dsQ L2 L1 S) (dsZi L1 S)
      rw [h4Q, hcardZ1] at hmulC
      have hQZ4 : Nat.card ↥(dsQ L2 L1 S ⊓ dsZi L1 S) = 4 := by omega
      have hle4 := Subgroup.card_le_of_le hC_le
      omega
  by_cases hnat : NatSec L1 ⊥ (dsZi L1 S)
  · exact hnat_case hnat
  · exact horth_case hnat

end CFSG.GH74.QTGen4.DSGen4
