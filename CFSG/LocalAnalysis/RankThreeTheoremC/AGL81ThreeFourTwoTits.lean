module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTitsL33
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoPairsBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Sporadic.Schreier.TitsAutD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.StandardType.TitsOvergroup CFSG.StandardType.TitsThree CFSG.StandardType.TitsGenerators
open CFSG.StandardType.SylowPair
open CFSG.Sporadic.Schreier.Tits (titsD)

theorem le_pairSide_of_pairP_le
    {Y : Subgroup (Equiv.Perm (Fin 1755))} (hPY : pairP pairData titsS ≤ Y) (hYG : Y ≤ titsD)
    (hY : Y ≠ titsD) : ∃ k < 2, Y ≤ pairSide pairData titsS (k + 2) := by
  have hc : titsThreeCheck () = true := Certificates.certificate465005
  obtain ⟨hpair, -, -⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, -, -, -, hSide, -, hGen, hMemS⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  have hcov : (Y : Set (Equiv.Perm (Fin pairData.n))) ⊆
      (pairSide pairData titsS 2 : Set (Equiv.Perm (Fin pairData.n))) ∪
        (pairSide pairData titsS 3 : Set (Equiv.Perm (Fin pairData.n))) := by
    intro y hy
    rcases dichotomy hS hpair hPY (hYG.trans (le_of_eq hG.symm)) (fun h => hY (h.trans hG)) hy
      with h | ⟨i, hi, hk, ⟨a, ha, b, hb, hyi⟩, -⟩
    · exact Or.inl (pairN_le_pairSide (k := 0) (by norm_num) h)
    · rcases kind_eq_cases hGen hi with h0 | h3 | h4
      · exact absurd h0 hk
      · have hg : (pairReps pairData titsS).getD (i + 1) 1 ∈ pairSide pairData titsS 2 :=
          pairReps_mem_side hS hSide hMemS hi (k := 2) h3
        refine Or.inl ?_
        rw [hyi]
        exact (pairSide pairData titsS 2).mul_mem ((pairSide pairData titsS 2).mul_mem
          (pairN_le_pairSide (k := 0) (by norm_num) ha) hg)
          (pairN_le_pairSide (k := 0) (by norm_num) hb)
      · have hg : (pairReps pairData titsS).getD (i + 1) 1 ∈ pairSide pairData titsS 3 :=
          pairReps_mem_side hS hSide hMemS hi (k := 3) h4
        refine Or.inr ?_
        rw [hyi]
        exact (pairSide pairData titsS 3).mul_mem ((pairSide pairData titsS 3).mul_mem
          (pairN_le_pairSide (k := 1) (by norm_num) ha) hg)
          (pairN_le_pairSide (k := 1) (by norm_num) hb)
  rcases le_or_le_of_subset_union hcov with h | h
  · exact ⟨0, by norm_num, h⟩
  · exact ⟨1, by norm_num, h⟩

theorem eq_pairSide_of_le
    {k : ℕ} (hk : k < 2) {Y J : Subgroup (Equiv.Perm (Fin 1755))}
    (hPY : pairP pairData titsS ≤ Y) (hYM : Y ≤ pairSide pairData titsS (k + 2)) (hJY : J ≤ Y)
    (hJ1 : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J Y) :
    J = pairSide pairData titsS k := by
  have hc : titsThreeCheck () = true := Certificates.certificate465005
  obtain ⟨hpair, hmem, -⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, hP, -, -, hSide, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  set L := pairSide pairData titsS k with hL
  have hLsimple : IsSimpleGroup ↥L := (isSimpleGroup_pairSide hc hk).1
  have hcardL : Nat.card ↥L = 5616 :=
    (card_pairSide hS hSide (k := k) (by simp [pairData]; omega)).trans (sideOrder_getD hk).1
  have hcardM : Nat.card ↥(pairSide pairData titsS (k + 2)) = 11232 :=
    (card_pairSide hS hSide (k := k + 2) (by simp [pairData]; omega)).trans (sideOrder_getD hk).2
  have hcard2 : Nat.card ↥(pairSide pairData titsS (k + 2)) = 2 * Nat.card ↥L := by
    rw [hcardM, hcardL]
  have hJL : J ≤ L :=
    le_of_perfect_of_card_eq_two_mul (pairSide_le_pairSide hk) hcard2 (hJY.trans hYM) hJp
  have hPL : pairP pairData titsS ≤ L := pairP_le_pairSide hpair hmem hk
  have hLY : L ≤ Y := by
    by_contra hLY
    have hlt : Y ⊓ L < L := lt_of_le_of_ne inf_le_right fun h => hLY (h ▸ inf_le_left)
    have h27 : 27 ∣ Nat.card ↥(Y ⊓ L) := by
      have h := Subgroup.card_dvd_of_le (le_inf hPY hPL)
      rwa [card_pairP hS hP] at h
    have hsol := CFSG.StandardType.SimpleOrderFiveSixOneSix.isSolvable_of_lt_simple_card_5616
      hLsimple hcardL hlt h27
    exact hJ1 (eq_bot_of_perfect_of_le_isSolvable (le_inf hJY hJL) hsol hJp)
  exact eq_of_perfect_of_isSubnormal_of_card_eq_two_mul hLY hYM hcard2 hLsimple hJY hJ1 hJp hJs

private def PerfectSubnormalL33 {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ J : Subgroup G, J ≤ H → J ≠ ⊥ → ⁅J, J⁆ = J → IsSubnormal J H →
    Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie threeFourTwoL33Index).Group)

private theorem perfectSubnormalL33_of_map_conj {G : Type*} [Group G] (g : G) (H : Subgroup G)
    (h : PerfectSubnormalL33 (H.map (MulAut.conj g).toMonoidHom)) : PerfectSubnormalL33 H := by
  intro J hJH hJ1 hJp hJs
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  obtain ⟨e⟩ := h (J.map (MulAut.conj g).toMonoidHom) (Subgroup.map_mono hJH)
    (fun hb => hJ1 ((Subgroup.map_eq_bot_iff_of_injective J hinj).mp hb))
    (by rw [← Subgroup.map_commutator, hJp]) (hJs.map _)
  exact ⟨(J.equivMapOfInjective _ hinj).trans e⟩

theorem nonempty_mulEquiv_catL33_of_le_of_not_dvd_index
    {H J : Subgroup ↥titsD}
    (hH : H ≠ ⊤) (h3 : ¬ 3 ∣ H.index) (hJH : J ≤ H) (hJ1 : J ≠ ⊥) (hJp : ⁅J, J⁆ = J)
    (hJs : IsSubnormal J H) :
    Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie threeFourTwoL33Index).Group) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : titsThreeCheck () = true := Certificates.certificate465005
  obtain ⟨hpair, -, -⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, hP, -, -, -, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  have hPG : pairP pairData titsS ≤ titsD := hG ▸ pairP_le_pairG
  have hP27 : Nat.card ↥(pairP pairData titsS) = 3 ^ 3 := by
    rw [card_pairP hS hP]
    rfl
  have hD : Nat.card ↥titsD = 3 ^ 3 * 665600 := by
    rw [CFSG.Sporadic.Schreier.Tits.card_titsD]
    norm_num
  let S : Sylow 3 ↥titsD := Sylow.ofCard ((pairP pairData titsS).subgroupOf titsD) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hP27]
    exact CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization hD (by norm_num))
  have hSdef : (S : Subgroup ↥titsD) = (pairP pairData titsS).subgroupOf titsD :=
    Sylow.coe_ofCard _ _
  refine CFSG.StandardType.SylowOvergroup.forall_of_sylow_le S PerfectSubnormalL33
    perfectSubnormalL33_of_map_conj ?_ hH h3 J hJH hJ1 hJp hJs
  intro Y hSY hYtop J hJY hJ1 hJp hJs
  have hinj := titsD.subtype_injective
  have hPY : pairP pairData titsS ≤ Y.map titsD.subtype := fun x hx =>
    ⟨⟨x, hPG hx⟩, hSY (by rw [hSdef]; exact hx), rfl⟩
  have hYne : Y.map titsD.subtype ≠ titsD := by
    intro heq
    apply hYtop
    have htop : (⊤ : Subgroup ↥titsD).map titsD.subtype = titsD := by
      rw [Subgroup.map_top titsD.subtype, Subgroup.range_subtype]
    exact (Subgroup.map_subtype_inj (H := titsD)).mp (heq.trans htop.symm)
  obtain ⟨k, hk, hYM⟩ := le_pairSide_of_pairP_le hPY (Subgroup.map_subtype_le Y) hYne
  have hJeq := eq_pairSide_of_le hk hPY hYM (Subgroup.map_mono hJY)
    (fun hb => hJ1 ((Subgroup.map_eq_bot_iff_of_injective J hinj).mp hb))
    (by rw [← Subgroup.map_commutator, hJp]) (hJs.map _)
  obtain ⟨e⟩ := nonempty_pairSide_mulEquiv_catL33 hk
  exact ⟨((J.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hJeq)).trans e⟩

theorem threeFourTwoAt_titsD
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits)
    (e₀ : (TauCeti.CFSGIndex.lie d).Group ≃* ↥titsD) : ThreeFourTwoAt 3 ↥titsD := by
  haveI : IsSimpleGroup ↥titsD := CFSG.Sporadic.Schreier.Tits.titsD_simple
  have hnab : ∃ a b : ↥titsD, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥titsD := { (inferInstance : Group ↥titsD) with mul_comm := hc }
    have hq : (Nat.card ↥titsD).Prime := IsSimpleGroup.prime_card
    rw [CFSG.Sporadic.Schreier.Tits.card_titsD] at hq
    norm_num at hq
  have hout : Group.IsSolvable (Outer ↥titsD) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 (Outer ↥titsD) :=
      IsPGroup.of_card (n := 1) (by rw [CFSG.Sporadic.Schreier.Tits.card_outer_titsD, pow_one])
    haveI : Finite (Outer ↥titsD) := Nat.finite_of_card_ne_zero (by
      rw [CFSG.Sporadic.Schreier.Tits.card_outer_titsD]; norm_num)
    haveI := h2.isNilpotent
    infer_instance
  refine threeFourTwoAt_of_forall_model inferInstance hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn e hrk hC hcomp hER hE hEc hcore hRY hKY J hJ hne hJp hJs hQ
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup ↥titsD := (Y₀.subgroupOf K).map e.toMonoidHom with hHdef
  have hH : H ≠ ⊤ := by
    intro htop
    apply hKY
    have h1 : Y₀.subgroupOf K = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [← hHdef, htop, Subgroup.map_top_of_surjective _ e.surjective]
    intro k hk
    exact Subgroup.mem_subgroupOf.mp (h1 ▸ Subgroup.mem_top (⟨k, hk⟩ : K))
  have h3 : ¬ 3 ∣ H.index := by
    obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
    have hTY : (T : Subgroup K) ≤ Y₀.subgroupOf K := fun t ht => by
      have h := (hT ▸ Subgroup.mem_map_of_mem K.subtype ht : (t : Y) ∈ (R : Subgroup Y) ⊓ K)
      exact Subgroup.mem_subgroupOf.mpr (hRY h.1)
    rw [hHdef, Subgroup.index_map_of_bijective e.bijective]
    exact fun h => T.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hTY))
  obtain ⟨g⟩ := nonempty_mulEquiv_catL33_of_le_of_not_dvd_index hH h3 hJ hne hJp hJs
  obtain ⟨dv, hv⟩ := d
  have hd' : dv = .tits := hd
  subst hd'
  refine ⟨.lie ⟨.tits, hv⟩, .lie threeFourTwoL33Index, ?_, ⟨e.trans e₀.symm⟩,
    g.toMonoidHom, g.surjective⟩
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, threeFourTwoQThree, rfl, rfl, ⟨.tits, hv⟩,
    threeFourTwoL33Index, rfl, rfl, rfl, rfl⟩)))

theorem threeFourTwoAt_tits3 :
    ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      ThreeFourTwoAt 3 (TauCeti.CFSGIndex.lie d).Group := by
  intro d hd
  obtain ⟨dv, hv⟩ := d
  have hd' : dv = .tits := hd
  subst hd'
  obtain ⟨e₀⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩)
  exact ThreeFourTwoAt.of_mulEquiv e₀.symm (threeFourTwoAt_titsD ⟨.tits, hv⟩ rfl e₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
