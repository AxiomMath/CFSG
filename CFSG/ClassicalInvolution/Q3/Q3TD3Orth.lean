module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Dn
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.Q3.Q3TY36
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.TWS6Sign

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement


section Model

theorem orthFacts3_plusDatum {m : ℕ} (hm : 5 ≤ m) :
    OrthFacts (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField 3 1) (by omega)))
      (GaloisField 3 1) := by
  have hm3 : 3 ≤ m := by omega
  have : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by
    rw [card_gf3]
    norm_num
  have hK' : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by omega)]
    norm_num
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1) := by
    rw [finrank_plus3]
    omega
  have hG := orthGeom_model (K' := GaloisField 3 (2 * 1)) hK hK' odd_gf3
    (nondegenerate_polarBilin_quadPlus m (GaloisField 3 1)) hdim
  have : Finite (spinGroup (quadPlus m (GaloisField 3 1))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcop : ∀ w ∈ Subgroup.center (spinGroup (quadPlus m (GaloisField 3 1))),
      ¬ 3 ∣ orderOf w := by
    intro w hw h3
    have h4 := pow_four_of_mem_center_spinPlus (K := GaloisField 3 1) hm3 hw
    have := h3.trans (orderOf_dvd_of_pow_eq_one h4)
    omega
  exact (centralQuot3_plus (by omega : 4 ≤ m)).orthFacts (not_three_dvd_card_center hcop) hG

theorem orthFacts3_plus {m : ℕ} (hm : 5 ≤ m) :
    OrthFacts (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D) (GaloisField 3 1) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by omega : 3 ≤ m)
  rw [e]
  exact orthFacts3_plusDatum hm

theorem signFacts3_plusDatum4 :
    RouteD.TWS6.SignFacts
      (fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
      (GaloisField 3 1) := by
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by
    rw [card_gf3]
    norm_num
  have hK' : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by omega)]
    norm_num
  have : NeZero 4 := ⟨by norm_num⟩
  have : Finite (spinGroup (quadPlus 4 (GaloisField 3 1))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hsign := RouteD.TWS6.orthGeom_sign_eight (Q := quadPlus 4 (GaloisField 3 1))
    (K' := GaloisField 3 (2 * 1)) hK hK' odd_gf3 (by rw [finrank_plus])
  have cq := centralQuot3_plus (m := 4) le_rfl
  have hcop : ∀ w ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))),
      ¬ 3 ∣ orderOf w := by
    intro w hw h3
    have h4 := pow_four_of_mem_center_spinPlus (K := GaloisField 3 1) (by norm_num : 3 ≤ 4) hw
    have := h3.trans (orderOf_dvd_of_pow_eq_one h4)
    omega
  have hC := not_three_dvd_card_center hcop
  refine ⟨fun R₁ h₁ R₂ h₂ R₃ h₃ a₁ a₃ k13 ⟨W, hW⟩ => ?_,
    fun ψ hψ R₁ h₁ R₂ h₂ hl => exists_lin_of_map3 hC ψ hψ (cq.pow3 R₁ h₁) (cq.pow3 R₂ h₂) hl⟩
  obtain ⟨W', hW'⟩ := hsign (R₁.map (spinAction (quadPlus 4 (GaloisField 3 1))))
    (cq.map_mem R₁ h₁) (R₂.map (spinAction (quadPlus 4 (GaloisField 3 1)))) (cq.map_mem R₂ h₂)
    (R₃.map (spinAction (quadPlus 4 (GaloisField 3 1)))) (cq.map_mem R₃ h₃)
    (cq.modelAdj h₁ h₂ a₁) (cq.modelAdj h₃ h₂ a₃) ((cq.commutes_iff h₁).mpr k13)
    ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
  exact exists_lin_of_map3 hC _ cq.ker_le (cq.pow3 R₂ h₂) (cq.pow3 R₃ h₃) ⟨W', hW'⟩

theorem signFacts3_plus4 :
    RouteD.TWS6.SignFacts (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D) (GaloisField 3 1) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num : 3 ≤ 4)
  rw [e]
  exact signFacts3_plusDatum4

end Model

section Witness

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag} {nY : ℕ}
  {N : Subgroup G} {x : G}

theorem star_config3 (cx : TCtx3 tY nY Ω N x)
    (hF : OrthGeom (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) (GaloisField 3 1))
    {c : Subgroup G} {wc : G} {l : Fin 3 → Subgroup G} {w : Fin 3 → G}
    (hc : c ∈ centralizingMembers Ω {x}) (hwc : IsClassicalMember3 c wc)
    (hl : ∀ i, l i ∈ centralizingMembers Ω {x}) (hw : ∀ i, IsClassicalMember3 (l i) (w i))
    (hadj : ∀ i, c ≠ l i ∧ ¬ Commutes c (l i) ∧ Commute wc (w i) ∧ conjSub (w i) c = c)
    (hcomm : ∀ i j, i ≠ j → l i ≠ l j ∧ Commutes (l i) (l j))
    (hdist : ∀ i j : Fin 3, i < j → ∃ d v, d ∈ centralizingMembers Ω {x} ∧
      IsClassicalMember3 d v ∧ d ≠ l i ∧ d ≠ l j ∧ Commute v (w i) ∧ Commute v (w j) ∧
      ¬ (Commutes d (l i) ↔ Commutes d (l j))) : False := by
  classical
  have hcL : IsLayerMember3 cx c :=
    IsLayerMember3.of_not_commutes cx hc (hl 0) (hadj 0).1 (hadj 0).2.1
  have hlL : ∀ i, IsLayerMember3 cx (l i) := fun i =>
    IsLayerMember3.of_not_commutes cx (hl i) hc (hadj i).1.symm
      (fun h => (hadj i).2.1 (commutes_symm h))
  obtain ⟨Rc, hRc, hcR⟩ := hcL.exists_fund
  have hex : ∀ i, ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      locImg Ω x (l i) = R.map cx.d.ψ := fun i => (hlL i).exists_fund
  choose R hR hlR using hex
  have hadjR : ∀ i, ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) Rc (R i) :=
    fun i =>
    cx.modelAdj_of_adj3 hc (hl i) hRc (hR i) hcR (hlR i) hwc (hw i) (hadj i).1 (hadj i).2.1
      (hadj i).2.2.1 (hadj i).2.2.2
  have hne : ∀ i j, i ≠ j → R i ≠ R j := fun i j hij h =>
    (hcomm i j hij).1 (cx.eq_of_locImg_eq (hl i) (hl j) (by rw [hlR i, hlR j, h]))
  have hcR' : ∀ i j, i ≠ j → Commutes (R i) (R j) := fun i j hij =>
    (cx.commutes_iff_fund (hl i) (hl j) (hR i) (hlR i) (hlR j)).mp (hcomm i j hij).2
  have key : ∀ i j : Fin 3, i < j →
      ModelIndist (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) (R i) (R j) → False := by
    intro i j hij hind
    obtain ⟨d, v, hd, hvd, hdi, hdj, hvi, hvj, hdn⟩ := hdist i j hij
    have hdL : IsLayerMember3 cx d := IsLayerMember3.of_distinguish cx hd (hl i) (hl j) hdi hdj hdn
    obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
    exact hdn (commutes_iff_of_indist3 cx (hl i) (hl j) hdL (hR i) (hR j) hRd (hlR i) (hlR j)
      hdR (hw i) (hw j) hvd hdi hdj hvi hvj hind)
  have hstar := hF.star Rc hRc (R 0) (hR 0) (R 1) (hR 1) (R 2) (hR 2) (hadjR 0) (hadjR 1)
    (hadjR 2) (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
    (hcR' 0 1 (by decide)) (hcR' 0 2 (by decide)) (hcR' 1 2 (by decide))
  rcases hstar with h | h | h
  · exact key 0 1 (by decide) h
  · exact key 0 2 (by decide) h
  · exact key 1 2 (by decide) h

theorem sign_config_sf3 (cx : TCtx3 tY nY Ω N x)
    (hF : RouteD.TWS6.SignFacts
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) (GaloisField 3 1))
    {a b d : Subgroup G} {wa wb wd : G} (ha : a ∈ centralizingMembers Ω {x})
    (hb : b ∈ centralizingMembers Ω {x}) (hd : d ∈ centralizingMembers Ω {x})
    (hwa : IsClassicalMember3 a wa) (hwb : IsClassicalMember3 b wb)
    (hwd : IsClassicalMember3 d wd) (hab : a ≠ b) (hbd : b ≠ d)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W a b) (hnbd : ¬ Commutes b d)
    (had : Commutes a d) (hcab : Commute wa wb) (hcdb : Commute wd wb)
    (hna : conjSub wb a = a) (hnd : conjSub wb d = d) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W b d := by
  obtain ⟨W, hW⟩ := hpair
  have hnab : ¬ Commutes a b := not_commutes_of_linearBlockStandardPair hW
  have haL : IsLayerMember3 cx a := IsLayerMember3.of_not_commutes cx ha hb hab hnab
  have hbL : IsLayerMember3 cx b := IsLayerMember3.of_not_commutes cx hb hd hbd hnbd
  have hdL : IsLayerMember3 cx d := IsLayerMember3.of_not_commutes cx hd hb hbd.symm
    (fun h => hnbd (commutes_symm h))
  obtain ⟨Ra, hRa, haR⟩ := haL.exists_fund
  obtain ⟨Rb, hRb, hbR⟩ := hbL.exists_fund
  obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
  have hadjab : ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) Ra Rb :=
    cx.modelAdj_of_adj3 ha hb hRa hRb haR hbR hwa hwb hab hnab hcab hna
  have hadjdb : ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) Rd Rb :=
    cx.modelAdj_of_adj3 hd hb hRd hRb hdR hbR hwd hwb hbd.symm
      (fun h => hnbd (commutes_symm h)) hcdb hnd
  have hcom : Commutes Ra Rd := (cx.commutes_iff_fund ha hd hRa haR hdR).mp had
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 ha hb hW
  rw [haR, hbR] at hW'
  have hlift := hF.lift cx.d.ψ cx.d.ker_le Ra hRa Rb hRb ⟨W', hW'⟩
  obtain ⟨W₂, hW₂⟩ := hF.sign Ra hRa Rb hRb Rd hRd hadjab hadjdb hcom hlift
  exact cx.stdPair_of_fund hb hd hW₂ hbR hdR

theorem sign_config_orth3 (cx : TCtx3 tY nY Ω N x)
    (hF : OrthFacts (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    {a b d : Subgroup G} {wa wb wd : G} (ha : a ∈ centralizingMembers Ω {x})
    (hb : b ∈ centralizingMembers Ω {x}) (hd : d ∈ centralizingMembers Ω {x})
    (hwa : IsClassicalMember3 a wa) (hwb : IsClassicalMember3 b wb)
    (hwd : IsClassicalMember3 d wd) (hab : a ≠ b) (hbd : b ≠ d)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W a b) (hnbd : ¬ Commutes b d)
    (had : Commutes a d) (hcab : Commute wa wb) (hcdb : Commute wd wb)
    (hna : conjSub wb a = a) (hnd : conjSub wb d = d) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W b d :=
  sign_config_sf3 cx ⟨hF.sign, hF.lift⟩ ha hb hd hwa hwb hwd hab hbd hpair hnbd had hcab hcdb hna
    hnd

end Witness

end CFSG.ClassicalInvolution.Q3.Q3TD
