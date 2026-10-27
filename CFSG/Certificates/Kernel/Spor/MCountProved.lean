module

public import CFSG.Certificates.Kernel.Spor.PK.MCnt
public import CFSG.Certificates.Kernel.Spor.M11Sound
public import CFSG.Certificates.Kernel.SporSch.ChainKZTot
public import CFSG.Certificates.Kernel.SporSch.ChainKRepsL
public import CFSG.Certificates.Kernel.Spor.PK.MBase

public section

namespace CFSG.KS.MEnum

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS.M11 CFSG.KS.PK CFSG.KS.SporSch.MOC CFSG.Sporadic.Th CFSG.KS
open CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.ClsSpec

private theorem sum_ite_eq_countP {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p] :
    (L.map fun x => if p x then 1 else 0).sum = L.countP fun x => decide (p x) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a <;> simp [h, Nat.add_comm]

private theorem szOK_of {n w : Nat} (h1 : n < 2 ^ 24) (h2 : n + 1 < 2 ^ w) : szOK n w = true := by
  unfold szOK
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq]
  refine ⟨by simpa using h1, ?_⟩
  change n + 1 < 1 <<< w
  rw [Nat.one_shiftLeft]
  exact h2

theorem mCntZ_sound_proved {n w k : ℕ} {gA gB : Equiv.Perm (Fin n)} {words : List (List Int)}
    {hn : 1 ≤ n} {bv : Vector (Fin n) k} {hbs : bv.toList.Nodup}
    {tA tB : List ℕ} {W : List (List Int)} {bs sz : List ℕ} {NW ky r s cap sub : ℕ}
    {CS : List ℕ} {CL : List ClassDatum} {Rs : List (ℕ × ℕ)}
    (hA : tA = imageList gA) (hB : tB = imageList gB)
    (hW : W = [[1], [2]] ++ words.map (List.map shiftLabel))
    (hbsv : bs = bv.toList.map Fin.val) (hNW : NW = words.length + 2)
    (hbase : mBase n w bs sz NW tA tB W = true) (h5 : sz.length = 5)
    (hsub : 0 < sub ∧ sz.getD 1 0 % sub = 0) (hsz : sz.tail.prod < 2 ^ 20)
    (hky : ky = 3 ∨ ky = 4) (hr : r.Prime) (hs : s = 6)
    (hCS : CS.length = sz.headD 0 * sub)
    (hc : ∀ i < sz.headD 0 * sub, mCntZ n w bs NW tA tB W sub i ky r Rs = CS.getD i 0)
    (hRs : Rs = CL.map fun d => (d.2.2.1, pinvS n w (mask w) d.2.2.1))
    (hmem : ∀ j < CL.length, cntSum CS (3 + 2 * j) = 1)
    (hoA : ordC n w (mask w) (packL w tA) = 2) (hoB : ordC n w (mask w) (packL w tB) = ky)
    (hpair : pairOKG n w (mask w) r s (packL w tA) (pinvS n w (mask w) (packL w tA))
      (packL w tB) (pinvS n w (mask w) (packL w tB)) = true)
    (hcls : allC (clsOneR n w tA tB 2 cap) CL = true) (hdisj : clsDisj n w CL = true)
    (hsum : clsSize CL = cntSum CS 0) (hn16 : n < 2 ^ 16) (hcap : cap ≤ 2 ^ 32) :
    let Q := certificate hn [gA, gB] words bv hbs
    Q.check = true ∧ ordTest n 2 (toTable gA) = true ∧ ordTest n ky (toTable gB) = true ∧
      pairTest n r s 2 ky (toTable gA) (toTable gB) = true ∧
      (orderTables Q 2).length = cntSum CS 0 ∧
      (orderTables Q ky).length = cntSum CS 1 ∧
      classOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2) cap = true ∧
      classTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2)
        (orderTables Q ky) cap r s 2 ky = clsTotR CL CS := by
  classical
  intro Q
  obtain ⟨hn24, hw, hbsl⟩ := mBase_facts hbase
  obtain ⟨hQ, hperm, hszs, hL⟩ := mBase_chain (sh := shiftLabel) (fun _ => rfl) hA hB hW hbsv
    hNW hn16 hbase
  have hn32 : n < 2 ^ 32 := by
    have : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hwn : n < 2 ^ w := by omega
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp at hw
    · exact h
  set F := mbF n w tA tB W
  set NL := NW + NW
  set sS : Nat → CFSG.KS.PK.BS := mbS n F NL bs
  set c : Nat → Nat := fun i => (sS i).pts.length with hcdef
  set E := enumeration Q
  have hV : ValidSchreier Q := hQ
  have hk : k = 5 := by
    have := congrArg List.length hszs
    simpa [h5] using this
  subst hk
  have hsz5 : sz = [c 0, c 1, c 2, c 3, c 4] := hszs.symm
  have hbl : bs.length = 5 := by rw [hbsv]; simp
  have hgood : ∀ i, GoodBS n F (sS i) := fun i => by
    refine goodBS_run ?_ (fun l hl => hL l (lvAt_sub _ _ _ _ l hl))
    by_cases hi : i < bs.length
    · exact hbsl _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact hn
  set V : Nat → Nat := fun i => levMaskAt n w (mLT n w tA tB W) NL bs i
  have hmc : ∀ i, mCntZ n w bs NW tA tB W sub i ky r Rs =
      sliceZ n w (mask w) (n * w) (mask (n * w)) ky r Rs (recBS n w F (sS 0) (V 0))
        (recBS n w F (sS 1) (V 1)) (recBS n w F (sS 2) (V 2)) (recBS n w F (sS 3) (V 3))
        (recBS n w F (sS 4) (V 4)) sub i := by
    intro i
    unfold mCntZ
    simp only [CFSG.KS.PK.strictN_eq, Nat.mul_eq, Nat.add_eq]
    rw [levN_eq hn16 hw hL hbsl, levPairs_eq, List.map_map, hbl]
    rfl
  have hsub' : 0 < sub ∧ (sS 1).pts.length % sub = 0 := by
    rw [hsz5] at hsub
    exact hsub
  have hsz' : (sS 1).pts.length * (sS 2).pts.length * (sS 3).pts.length * (sS 4).pts.length <
      2 ^ 20 := by
    rw [hsz5] at hsz
    simpa [Nat.mul_assoc] using hsz
  have hCS' : CS.length = (sS 0).pts.length * sub := by
    rw [hsz5] at hCS
    exact hCS
  have hc' : ∀ i < (sS 0).pts.length * sub, sliceZ n w (mask w) (n * w) (mask (n * w)) ky r Rs
      (recBS n w F (sS 0) (V 0)) (recBS n w F (sS 1) (V 1)) (recBS n w F (sS 2) (V 2))
      (recBS n w F (sS 3) (V 3)) (recBS n w F (sS 4) (V 4)) sub i = CS.getD i 0 := by
    intro i hi
    rw [← hmc i]
    refine hc i ?_
    rw [hsz5]
    exact hi
  have hT : (List.range 5).map (fun i => (List.range (sS i).pts.length).map (tau n F sS i)) =
      (List.range 5).map fun i => (List.range (mbS n (mbF n w tA tB W) (NW + NW) bs i).pts.length).map
        fun j => permOf n (BS.trans (mbF n w tA tB W) (mbS n (mbF n w tA tB W) (NW + NW) bs i) j) :=
    rfl
  have hsumE : ∀ φ : Equiv.Perm (Fin n) → Nat, ((products ((List.range 5).map fun i =>
      (List.range (sS i).pts.length).map (tau n F sS i))).map φ).sum = (E.map φ).sum := by
    intro φ
    rw [hT]
    exact ((hperm.map φ).sum_eq).symm
  have hlenRs : Rs.length = CL.length := by rw [hRs, List.length_map]
  set d0 : ClassDatum := (0, 0, 0, [], [], [], [])
  have hrAt : ∀ j < CL.length, rAt Rs j =
      ((CL.getD j d0).2.2.1, pinvS n w (mask w) (CL.getD j d0).2.2.1) := by
    intro j hj
    rw [rAt, hRs, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj]
  have hfmem : ∀ j < CL.length, (E.map fun σ => if orderOf σ = 2 ∧
      ∀ x : Fin n, (σ x : Nat) = pg w (mask w) (rAt Rs j).1 x then 1 else 0).sum = 1 := by
    intro j hj
    have h1 := hmem j hj
    rw [cntSum_five hn16 hw hgood ky r Rs hsub' hsz' hCS' hc'
      (P := fun f => f = 0 ∨ f = 1 ∨ (3 ≤ f ∧ f % 2 = 1))
      (fun f hf g g' h hg => cfld_congr_mem hf h hg) (by rw [hlenRs]; omega)
      (Or.inr (Or.inr ⟨by omega, by omega⟩)), hsumE] at h1
    refine Eq.trans ?_ h1
    exact congrArg List.sum (List.map_congr_left fun σ _ => (cfld_mem_cfn σ j).symm)
  have hex : ∀ j, ∃ ρ : Equiv.Perm (Fin n), j < CL.length → ρ ∈ E ∧ orderOf ρ = 2 ∧
      PRep n w (CL.getD j d0).2.2.1 ρ := by
    intro j
    by_cases hj : j < CL.length
    · have h1 := hfmem j hj
      rw [sum_ite_eq_countP] at h1
      obtain ⟨ρ, hρ, hp⟩ := List.countP_pos_iff.1 (lt_of_lt_of_eq Nat.one_pos h1.symm)
      rw [decide_eq_true_eq] at hp
      refine ⟨ρ, fun _ => ⟨hρ, hp.1, fun x => ?_⟩⟩
      rw [hp.2 x, hrAt j hj]
    · exact ⟨1, fun h => absurd h hj⟩
  choose ρ hρ using hex
  have pRi : ∀ j < CL.length, PRep n w (pinvS n w (mask w) (CL.getD j d0).2.2.1) (ρ j)⁻¹ :=
    fun j hj => (prep_pinvS hwn (hρ j hj).2.2).1
  have hRval : ∀ j, ∀ x < n, pg w (mask w) (rAt Rs j).1 x < n ∧
      pg w (mask w) (rAt Rs j).2 x < n := by
    intro j x hx
    by_cases hj : j < CL.length
    · rw [hrAt j hj]
      exact ⟨by rw [(hρ j hj).2.2 ⟨x, hx⟩]; exact (ρ j ⟨x, hx⟩).isLt,
        by rw [pRi j hj ⟨x, hx⟩]; exact ((ρ j)⁻¹ ⟨x, hx⟩).isLt⟩
    · have : rAt Rs j = (0, 0) := by
        rw [rAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [this, CFSG.KS.PK.pg_eq]
      simp only [Nat.zero_div, Nat.zero_mod]
      exact ⟨hn, hn⟩
  have hfld : ∀ f < 2 + 2 * Rs.length, cntSum CS f =
      (E.map fun σ => cfld n w (mask w) ky r Rs (cfn σ) f).sum := by
    intro f hf
    rw [cntSum_five hn16 hw hgood ky r Rs hsub' hsz' hCS' hc' (P := fun _ => True)
      (fun f _ g g' h hg => cfld_congr hRval f h hg) hf trivial, hsumE]
  have hord : ∀ m, 0 < m → (orderTables Q m).length = E.countP fun σ => decide (orderOf σ = m) :=
    fun m hm => by
      rw [(forall₂_orderTables hn32 Q hm).length_eq, List.length_reverse,
        List.countP_eq_length_filter]
  have hky0 : 0 < ky := by omega
  have hX : (orderTables Q 2).length = cntSum CS 0 := by
    rw [hfld 0 (by omega), hord 2 (by decide), ← sum_ite_eq_countP]
    exact congrArg List.sum (List.map_congr_left fun σ _ => (cfld_zero_cfn σ).symm)
  have hY : (orderTables Q ky).length = cntSum CS 1 := by
    rw [hfld 1 (by omega), hord ky hky0, ← sum_ite_eq_countP]
    exact congrArg List.sum (List.map_congr_left fun σ _ => (cfld_one_cfn hky σ).symm)
  have hpart : ∀ j < CL.length, cntSum CS (2 + 2 * j) = partners E ky r 6 (ρ j) := by
    intro j hj
    rw [hfld (2 + 2 * j) (by rw [hlenRs]; omega)]
    rw [show (E.map fun σ => cfld n w (mask w) ky r Rs (cfn σ) (2 + 2 * j)) =
        E.map fun σ => if orderOf σ = ky ∧ orderOf (ρ j * σ) = r ∧
          orderOf (ρ j * σ * (ρ j)⁻¹ * σ⁻¹) = 6 then 1 else 0 from
      List.map_congr_left fun σ _ => cfld_part_cfn hky hr σ (ρ j) j (hrAt j hj) (hρ j hj).2.2
        (pRi j hj)]
    rw [sum_ite_eq_countP, partners, List.countP_filter]
    congr 1
    funext y
    refine Bool.eq_iff_iff.2 ?_
    simp only [decide_eq_true_iff, Bool.and_eq_true]
    simp only [PartnerRel]
    tauto
  have pA : PRep n w (packL w tA) gA := by subst hA; exact (prep_packL hw).1
  have pB : PRep n w (packL w tB) gB := by subst hB; exact (prep_packL hw).1
  have pAi := (prep_pinvS hwn pA).1
  have pBi := (prep_pinvS hwn pB).1
  have hoA' : orderOf gA = 2 := (orderOf_of_ordC pA).trans hoA
  have hoB' : orderOf gB = ky := (orderOf_of_ordC pB).trans hoB
  have hpair' : orderOf (gA * gB) = r ∧ orderOf (gA * gB * gA⁻¹ * gB⁻¹) = s := by
    unfold pairOKG at hpair
    simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hpair
    refine ⟨(orderOf_of_ordC (prep_pcomp hn32 pA pB)).trans hpair.1, ?_⟩
    have := (orderOf_of_ordC (prep_pcomp hn32 pA (prep_pcomp hn32 pB
      (prep_pcomp hn32 pAi pBi)))).trans hpair.2
    simpa [mul_assoc] using this
  set G := Q.originalSubgroup
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  have hGK : G = K := orig_pair hn hbs
  have hab : gA ∈ G ∧ gB ∈ G := by
    rw [hGK]
    exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
  have hmemE : ∀ g, g ∈ E ↔ g ∈ G := mem_enumeration_iff Q hV
  have hndE : E.Nodup := enumeration_nodup Q hV
  have hszOK := szOK_of (by simpa using hn24) hw
  rw [allC_iff] at hcls
  have hCLmem : ∀ j < CL.length, CL.getD j d0 ∈ CL := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  set S : Nat → List Nat := fun j => (CL.getD j d0).2.2.2.2.2.2
  have hF := fun j (hj : j < CL.length) (hpos : 0 < (S j).length) =>
    datum_facts hA hB hszOK (hcls _ (hCLmem j hj)) hpos (hρ j hj).2.2
  set XG := E.filter fun h => decide (orderOf h = 2)
  set XF := XG.toFinset
  have hmemX : ∀ g, g ∈ XF ↔ g ∈ G ∧ orderOf g = 2 := fun g => by
    simp only [XF, XG, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, hmemE]
  have hXF : XF.card = (CL.map fun d => d.2.2.2.2.2.2.length).sum := by
    rw [List.toFinset_card_of_nodup (hndE.filter _), ← clsSize_eq, hsum, ← hX,
      hord 2 (by decide), List.countP_eq_length_filter]
  set C : Nat → Finset (Equiv.Perm (Fin n)) := fun j =>
    if 0 < (S j).length then XF.filter fun g => g ∈ CFSG.Sporadic.SmallOddCore.conjClass K (ρ j) else ∅
  have hclG : ∀ j < CL.length, ∀ g ∈ CFSG.Sporadic.SmallOddCore.conjClass K (ρ j), g ∈ XF := by
    intro j hj g hg
    rw [hmemX]
    obtain ⟨c, hc, rfl⟩ := hg
    rw [← hGK] at hc
    have hρG : ρ j ∈ G := (hmemE _).1 (hρ j hj).1
    refine ⟨G.mul_mem (G.mul_mem hc hρG) (G.inv_mem hc), ?_⟩
    rw [← (hρ j hj).2.1]
    exact (MulAut.conj c).orderOf_eq (ρ j)
  have hCcard : ∀ j < CL.length, (C j).card = (S j).length := by
    intro j hj
    by_cases hpos : 0 < (S j).length
    · simp only [C, if_pos hpos]
      rw [← (hF j hj hpos).1, ← Set.ncard_coe_finset]
      congr 1
      ext g
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hclG j hj g h, h⟩⟩
    · simp only [C, if_neg hpos, Finset.card_empty]
      omega
  have hdisjC : ∀ i < CL.length, ∀ j < CL.length, i < j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    by_cases hpi : 0 < (S i).length
    · by_cases hpj : 0 < (S j).length
      · rw [Finset.disjoint_left]
        intro g hgi hgj
        simp only [C, if_pos hpi, if_pos hpj, Finset.mem_filter] at hgi hgj
        have hrj : ρ j ∈ CFSG.Sporadic.SmallOddCore.conjClass K (ρ i) :=
          conjClass_trans (conjClass_symm hgj.2) hgi.2
        obtain ⟨-, hci, -, hmi, hinci, hSi, -⟩ := hF i hi hpi
        obtain ⟨-, -, -, -, -, -, hRlt⟩ := hF j hj hpj
        obtain ⟨k', hk', pk⟩ := (hmi _).1 hrj
        have hdj := clsDisj_spec n w CL hdisj i j hi hj hij
        rw [← List.getD_eq_getElem _ d0 hi, ← List.getD_eq_getElem _ d0 hj, lenN_eq'] at hdj
        refine bmem_complete (hci.trans hcap) (fun a b hab hb => ?_) hdj k' hk' ?_
        · rw [blk_packL hSi, blk_packL hSi]
          exact hinci a b hab hb
        · rw [blk_packL hSi]
          exact PF.eq_of_fields hw0 (shr_of_lt (getD_lt hSi k')) (shr_of_lt hRlt) fun t ht => by
            rw [pk ⟨t, ht⟩, (hρ j hj).2.2 ⟨t, ht⟩]
      · simp [C, if_neg hpj]
    · simp [C, if_neg hpi]
  have hpd : ∀ i ∈ Finset.range CL.length, ∀ j ∈ Finset.range CL.length, i ≠ j →
      Disjoint (C i) (C j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hdisjC i hi j hj h
    · exact (hdisjC j hj i hi h).symm
  have hsumC : ((CL.map fun d => d.2.2.2.2.2.2.length).sum) =
      ∑ j ∈ Finset.range CL.length, (C j).card := by
    rw [← range_map_getD (d0 := d0) (fun d : ClassDatum => d.2.2.2.2.2.2.length) rfl,
      sum_range_list]
    exact Finset.sum_congr rfl fun j hj => (hCcard j (Finset.mem_range.1 hj)).symm
  have hU : (Finset.range CL.length).biUnion C = XF := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.1 hg
      by_cases hpos : 0 < (S j).length
      · simp only [C, if_pos hpos] at hgj
        exact (Finset.mem_filter.1 hgj).1
      · simp [C, if_neg hpos] at hgj
    · rw [Finset.card_biUnion hpd, hXF, hsumC]
  have hcov : ∀ y ∈ XF, ∃ j < CL.length, 0 < (S j).length ∧
      y ∈ CFSG.Sporadic.SmallOddCore.conjClass K (ρ j) := by
    intro y hy
    rw [← hU] at hy
    obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
    by_cases hpos : 0 < (S j).length
    · simp only [C, if_pos hpos, Finset.mem_filter] at hyj
      exact ⟨j, Finset.mem_range.1 hj, hpos, hyj.2⟩
    · simp [C, if_neg hpos] at hyj
  have hXf := forall₂_orderTables hn32 Q (m := 2) (by decide)
  have hg := rep_pair hn32 gA gB
  have hgK := genK_pair gA gB
  have hok : classOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2) cap = true := by
    refine CFSG.KS.SporSch.ClsSpec.classOK_of_closed hg hXf (fun y hy => ?_)
      (List.nodup_reverse.2 (hndE.filter _)) (fun y hy z hz => ?_)
    · rw [hgK]
      have hyF : y ∈ XF := by
        rw [List.mem_toFinset]
        exact List.mem_reverse.1 hy
      obtain ⟨j, hj, hpos, hyj⟩ := hcov y hyF
      have e : CFSG.Sporadic.SmallOddCore.conjClass K y = CFSG.Sporadic.SmallOddCore.conjClass K (ρ j) := by
        ext z
        exact ⟨fun h => conjClass_trans h hyj, fun h => conjClass_trans h (conjClass_symm hyj)⟩
      rw [e, (hF j hj hpos).1]
      exact (hF j hj hpos).2.1
    · rw [hgK] at hz
      rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, hmemE] at hy ⊢
      obtain ⟨c, hc, rfl⟩ := hz
      replace hc : c ∈ G := by rw [hGK]; exact hc
      exact ⟨G.mul_mem (G.mul_mem hc hy.1) (G.inv_mem hc),
        ((MulAut.conj c).orderOf_eq y).trans hy.2⟩
  have hs0 : 0 < s := by omega
  have hr0 : 0 < r := hr.pos
  have htot : classTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2)
      (orderTables Q ky) cap r s 2 ky = clsTotR CL CS := by
    rw [← card_image_pairs_eq_classTotal₂ hn32 Q hV (by decide) hky0 hr0 hs0 hab.1 hab.2 cap hok]
    have hcoe : ∀ p : G × G, (orderOf p.1 = 2 ∧ orderOf p.2 = ky ∧ orderOf (p.1 * p.2) = r ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s) ↔
        (orderOf (p.1 : Equiv.Perm (Fin n)) = 2 ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = ky ∧
          PartnerRel r s (p.1 : Equiv.Perm (Fin n)) p.2) := fun p => by
      simp only [PartnerRel, ← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
      card_pairs_eq_sum G E hndE hmemE (fun h => orderOf h = 2) (fun h => orderOf h = ky)
        (PartnerRel r s)]
    subst hs
    have hXG : (XG.map fun x => partners E ky r 6 x).sum = ∑ x ∈ XF, partners E ky r 6 x :=
      (List.sum_toFinset _ (hndE.filter _)).symm
    change (XG.map fun x => partners E ky r 6 x).sum = _
    rw [hXG, ← hU, Finset.sum_biUnion hpd]
    unfold clsTotR
    rw [sum_range_list]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    by_cases hpos : 0 < (S j).length
    · have hconst : ∀ x ∈ C j, partners E ky r 6 x = partners E ky r 6 (ρ j) := by
        intro x hx
        simp only [C, if_pos hpos, Finset.mem_filter] at hx
        obtain ⟨c', hc', rfl⟩ := hx.2
        rw [← hGK] at hc'
        exact partners_conj G E hndE hmemE ky r 6 hc' (ρ j)
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, hCcard j hj', hpart j hj']
    · have h0 : (S j).length = 0 := by omega
      simp only [C, if_neg hpos, Finset.sum_empty]
      change 0 = (S j).length * _
      rw [h0, Nat.zero_mul]
  exact ⟨hQ, (ordTest_iff perm_faithful (rep_toTable hn32 gA) (by decide)).2 hoA',
    (ordTest_iff perm_faithful (rep_toTable hn32 gB) hky0).2 hoB',
    (pairTest_iff perm_faithful (rep_toTable hn32 gA) (rep_toTable hn32 gB) hr0 hs0 hoA' hoB'
      (by decide) hky0).2 hpair', hX, hY, hok, htot⟩

end CFSG.KS.MEnum

end
