module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreSetting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistence
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralizerSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J}

omit [Finite J] in
structure FourGen (Q : Sylow 2 J) (z : J) : Prop where
  mem : z ∈ (Q : Subgroup J)
  order : orderOf z = 2
  not_mem_center : z ∉ Subgroup.center J
  comm_mem_center : ∀ q ∈ (Q : Subgroup J), q * z * q⁻¹ * z⁻¹ ∈ Subgroup.center J

namespace Setting

theorem exists_involution_not_mem_center (h : Setting J Q B) :
    ∃ y : J, orderOf y = 2 ∧ y ∉ Subgroup.center J := by
  by_contra hno
  push Not at hno
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by decide : 1 < 2) (⊤ : Subgroup J)
  have hEZ : E ≤ Subgroup.center J := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact (Subgroup.center J).one_mem
    · exact hno x (orderOf_eq_prime (hE.2 x hx) hx1)
  have h4 : 2 ^ 2 ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h.rank
  have hle := Subgroup.card_le_of_le hEZ
  rw [h.center_card] at hle
  omega

theorem no_normal_four (h : Setting J Q B) (hno : ∀ z, ¬ FourGen Q z)
    (V : Subgroup (Q : Subgroup J)) (hVn : V.Normal) (hV : IsElemAbelian 2 V) :
    Nat.card V ≠ 4 := by
  intro hV4
  have hnil : Group.IsNilpotent (Q : Subgroup J) := Q.isPGroup'.isNilpotent
  have hVne : V ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hV4
    exact absurd hV4 (by decide)
  have hsq : ∀ x ∈ V, ((x : (Q : Subgroup J)) : J) ^ 2 = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hV.2 x hx)
  obtain ⟨⟨v, hvV, hvZ⟩, hv1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hVne)
  have hv1' : (v : J) ≠ 1 := fun h1 => hv1 (Subtype.ext (Subtype.ext h1))
  have hvc : (v : J) = centralElt J := by
    have hvZJ : (v : J) ∈ Subgroup.center J := by
      by_contra hvZJ
      refine hno (v : J) ⟨v.2, orderOf_eq_prime (hsq v hvV) hv1', hvZJ, fun q hq => ?_⟩
      have hcomm : q * (v : J) = (v : J) * q :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hvZ ⟨q, hq⟩)
      rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
      exact (Subgroup.center J).one_mem
    exact (h.mem_center_iff.mp hvZJ).resolve_left hv1'
  set ZP := (Subgroup.center J).subgroupOf (Q : Subgroup J) with hZP
  have hZPV : ZP ≤ V := by
    intro x hx
    rcases h.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hx) with hx1 | hxe
    · rw [show x = 1 from Subtype.ext hx1]
      exact V.one_mem
    · rw [show x = v from Subtype.ext (hxe.trans hvc.symm)]
      exact hvV
  set W := ZP.subgroupOf V with hW
  have hWcard : Nat.card W = 2 :=
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZPV).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.center_le_sylow).toEquiv)).trans
      h.center_card
  have hWindex : W.index = 2 := by
    have := W.index_mul_card
    rw [hWcard, hV4] at this
    omega
  have hmemW : ∀ x : V, x ∈ W ↔ ((x : (Q : Subgroup J)) : J) ∈ Subgroup.center J := fun x => by
    rw [hW, Subgroup.mem_subgroupOf, hZP, Subgroup.mem_subgroupOf]
  obtain ⟨w, hwW⟩ : ∃ w : V, w ∉ W := by
    by_contra hall
    push Not at hall
    have htop : W = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at hWindex
    exact absurd hWindex (by decide)
  have hw1 : ((w : (Q : Subgroup J)) : J) ≠ 1 := fun h1 =>
    hwW ((hmemW w).mpr (h1 ▸ (Subgroup.center J).one_mem))
  refine hno _ ⟨(w : (Q : Subgroup J)).2, orderOf_eq_prime (hsq w w.2) hw1,
    fun hZ => hwW ((hmemW w).mpr hZ), fun q hq => ?_⟩
  have ha : ⟨q, hq⟩ * (w : (Q : Subgroup J)) * ⟨q, hq⟩⁻¹ ∈ V := hVn.conj_mem _ w.2 _
  have haW : (⟨_, ha⟩ : V) ∉ W := by
    intro haW
    apply hwW
    rw [hmemW] at haW ⊢
    have := (inferInstance : (Subgroup.center J).Normal).conj_mem _ haW q⁻¹
    simpa [mul_assoc] using this
  have key := (Subgroup.mul_mem_iff_of_index_two hWindex (a := ⟨_, ha⟩) (b := w⁻¹)).mpr
    ⟨fun h' => absurd h' haW, fun h' => absurd (by simpa using W.inv_mem h') hwW⟩
  simpa [mul_assoc] using (hmemW _).mp key

theorem mem_center_of_cyclic (h : Setting J Q B) (hno : ∀ z, ¬ FourGen Q z)
    {C : Subgroup (Q : Subgroup J)} (hCn : C.Normal) (hC : IsCyclic C) (hCi : C.index ≤ 2)
    {y : J} (hy : orderOf y = 2) : y ∈ Subgroup.center J := by
  have hC0 : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show C.index = 1 ∨ C.index = 2 by omega) with h1 | h2
  ·
    rw [Subgroup.index_eq_one] at h1
    have hQc : IsCyclic (Q : Subgroup J) := by
      rw [h1] at hC
      exact (MulEquiv.isCyclic Subgroup.topEquiv).mp hC
    obtain ⟨u, -, hu⟩ := involution_conjugate_into_sylow Q ⊤ le_top y (Subgroup.mem_top y) hy
    have hord : orderOf (u⁻¹ * y * u) = 2 := by
      simpa only [MulAut.conj_apply, inv_inv, hy] using (MulAut.conj u⁻¹).orderOf_eq y
    have heq := eq_of_orderOf_eq_two_of_isCyclic hQc hu h.centralElt_mem_sylow hord
      h.orderOf_centralElt
    have hy' : y = u * centralElt J * u⁻¹ := by
      rw [← heq]
      group
    rw [hy', (h.commute_centralElt u).eq, mul_inv_cancel_right]
    exact h.centralElt_mem_center
  ·
    obtain ⟨g, hg⟩ := hC.exists_generator
    have hCg : C = Subgroup.zpowers (g : (Q : Subgroup J)) := by
      refine le_antisymm (fun c hc => ?_) (Subgroup.zpowers_le.mpr g.2)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨c, hc⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    set x : J := ((g : (Q : Subgroup J)) : J) with hx
    have hsub : (Subgroup.zpowers x).subgroupOf (Q : Subgroup J) = C := by
      rw [hCg]
      ext c
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, by rw [Subgroup.coe_zpow]⟩
    have hrel : (Subgroup.zpowers x).relIndex (Q : Subgroup J) = 2 := by
      rw [Subgroup.relIndex, hsub, h2]
    have hQcard : 2 ^ 2 ≤ Nat.card (Q : Subgroup J) := by
      obtain ⟨E, hEQ, -, hcard⟩ :=
        CFSG.SectionRank.exists_pRank (by decide : 1 < 2) (Q : Subgroup J)
      rw [sylow_two_rank_eq Q] at hcard
      calc 2 ^ 2 ≤ 2 ^ twoRank J := Nat.pow_le_pow_right (by norm_num) h.rank
        _ = Nat.card E := hcard.symm
        _ ≤ Nat.card (Q : Subgroup J) := Subgroup.card_le_of_le hEQ
    have hCeven : 2 ∣ Nat.card C := by
      have hmul := C.index_mul_card
      rw [h2] at hmul
      obtain ⟨n, hn⟩ := (Q.isPGroup'.to_subgroup C).exists_card_eq
      rw [hn] at hmul ⊢
      rcases n with _ | n
      · omega
      · exact dvd_pow_self 2 n.succ_ne_zero
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hCeven
    have hc' : orderOf (((c : (Q : Subgroup J)) : J)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
    have hcZ : ((c : (Q : Subgroup J)) : J) ∈ Subgroup.center J := by
      by_contra hcZ
      refine hno _ ⟨(c : (Q : Subgroup J)).2, hc', hcZ, fun q hq => ?_⟩
      have hmem : ⟨q, hq⟩ * (c : (Q : Subgroup J)) * ⟨q, hq⟩⁻¹ ∈ C := hCn.conj_mem _ c.2 _
      have hord : orderOf (⟨q, hq⟩ * (c : (Q : Subgroup J)) * ⟨q, hq⟩⁻¹) = 2 := by
        have h1 := (MulAut.conj (⟨q, hq⟩ : (Q : Subgroup J))).orderOf_eq (c : (Q : Subgroup J))
        simp only [MulAut.conj_apply] at h1
        rw [h1, Subgroup.orderOf_coe]
        exact hc
      have heq := eq_of_orderOf_eq_two_of_isCyclic hC hmem c.2 hord
        (by rw [Subgroup.orderOf_coe, hc])
      have heq' := congrArg Subtype.val heq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at heq'
      rw [heq', mul_inv_cancel]
      exact (Subgroup.center J).one_mem
    have hce : ((c : (Q : Subgroup J)) : J) = centralElt J := by
      refine (h.mem_center_iff.mp hcZ).resolve_left fun h1 => ?_
      rw [h1, orderOf_one] at hc'
      exact absurd hc' (by decide)
    have hZx : Subgroup.center J ≤ Subgroup.zpowers x := by
      intro w hw
      rcases h.mem_center_iff.mp hw with rfl | rfl
      · exact Subgroup.one_mem _
      · rw [← hce]
        have hcx : (c : (Q : Subgroup J)) ∈ (Subgroup.zpowers x).subgroupOf (Q : Subgroup J) := by
          rw [hsub]
          exact c.2
        exact Subgroup.mem_subgroupOf.mp hcx
    have hZne : Subgroup.center J ≠ ⊥ := fun hbot =>
      h.centralElt_ne_one (Subgroup.mem_bot.mp (hbot ▸ h.centralElt_mem_center))
    exact mem_center_of_cyclic_index_two h.perfect.commutator_eq_top h.center_isPGroup hZne Q
      (g : (Q : Subgroup J)).2 hrel hZx hy

theorem exists_fourGen (h : Setting J Q B) : ∃ z, FourGen Q z := by
  by_contra hno
  push Not at hno
  have hcyc : ∀ A : Subgroup (Q : Subgroup J), A.Normal → IsMulCommutative A → IsCyclic A :=
    fun A hA hAc => no_normal_four_abelian_normal_cyclic Q.isPGroup' (h.no_normal_four hno) A hAc
  obtain ⟨C, hCn, hC, hCi⟩ := cyclic_abelian_normal_index_two _ Q.isPGroup' hcyc
  obtain ⟨y, hy, hyZ⟩ := h.exists_involution_not_mem_center
  exact hyZ (h.mem_center_of_cyclic hno hCn hC hCi hy)

end Setting

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
