module

public import CFSG.Certificates.Kernel.Spor.MCountBProved
public import CFSG.Certificates.Kernel.Spor.PK.MCentChain

public section

namespace CFSG.KS.MCent

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS.M11 CFSG.KS.PK CFSG.KS.MEnum CFSG.KS CFSG.KS.SporSch.MOC
open CFSG.KS.Raw.Orb (PRep prep_pcomp prep_pidn)
open CFSG.KS.SporSch.ClsSpec (conjClass_trans conjClass_symm)

theorem cntCM_card {n w k : ℕ} {gA gB : Equiv.Perm (Fin n)} {words : List (List Int)}
    {hn : 1 ≤ n} {bv : Vector (Fin n) k} {hbs : bv.toList.Nodup}
    {tA tB : List ℕ} {W : List (List Int)} {bs sz : List ℕ} {NW : ℕ}
    (hA : tA = imageList gA) (hB : tB = imageList gB)
    (hW : W = [[1], [2]] ++ words.map (List.map shiftLabel))
    (hbsv : bs = bv.toList.map Fin.val) (hNW : NW = words.length + 2) (hn16 : n < 2 ^ 16)
    (hbase : mBase n w bs sz NW tA tB W = true) (g g' : Equiv.Perm (Fin n))
    {D : List (List (ℕ × ℕ × ℕ))} (hok : trOKC w (mask w) (enc w (cfn g) n) bs D = true) :
    cntCM n w bs NW tA tB W (enc w (cfn g) n) (enc w (cfn g') n) D =
      Nat.card {h : Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) //
        (h : Equiv.Perm (Fin n)) * g = g' * h} := by
  obtain ⟨-, hw, hbsl⟩ := mBase_facts hbase
  obtain ⟨hQ, hperm, -, hL⟩ := mBase_chain (sh := shiftLabel) (fun _ => rfl) hA hB hW hbsv
    hNW hn16 hbase
  have hV : ValidSchreier (certificate hn [gA, gB] words bv hbs) := hQ
  have hk : bs.length = k := by rw [hbsv]; simp
  have hbs' : ∀ i, bs.getD i 0 < n := fun i => by
    by_cases hi : i < bs.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hbsl _ (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact hn
  rw [cntCM_eq hn16 hw hL hbsl, hk]
  have hGK : (certificate hn [gA, gB] words bv hbs).originalSubgroup =
      Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) :=
    CFSG.KS.SporSch.MOC.orig_pair hn hbs
  rw [← hGK]
  exact cSrch_card hn16 hw hbs' (fun i l hl => hL l (lvAt_sub _ _ _ _ l hl)) _
    (enumeration_nodup _ hV) (mem_enumeration_iff _ hV) hperm g g' hok

theorem card_cent_eq {M : Type*} [Group M] (K : Subgroup M) (r : K) :
    Nat.card (Subgroup.centralizer {r}) = Nat.card {h : K // (h : M) * r = r * h} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    Subgroup.mem_centralizer_singleton_iff.trans Subtype.ext_iff)

theorem not_isConj_of_cnt0 {M : Type*} [Group M] [Finite M] {K : Subgroup M} (r s : K)
    (h0 : Nat.card {h : K // (h : M) * r = s * h} = 0) : ¬ IsConj r s := by
  rintro ⟨c, hc⟩
  have hc' : ((c : K) : M) * r = s * (c : K) := congrArg Subtype.val hc
  have : Nonempty {h : K // (h : M) * r = s * h} := ⟨⟨c, hc'⟩⟩
  have := Nat.card_pos (α := {h : K // (h : M) * r = s * h})
  omega

@[expose] def wdM {M : Type*} [Monoid M] (a b : M) (l : List ℕ) : M :=
  (l.map fun c => if c = 0 then a else b).prod

theorem wdM_mem {M : Type*} [Group M] (a b : M) (l : List ℕ) :
    wdM a b l ∈ Subgroup.closure ({a, b} : Set M) := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem orderOf_conjM {M : Type*} [Group M] (c x : M) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply]
  exact MulEquiv.orderOf_eq _ x

theorem orderOf_isConjK {M : Type*} [Group M] {K : Subgroup M} {x y : K} (h : IsConj x y) :
    orderOf (x : M) = orderOf (y : M) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
  rw [← e, orderOf_conjM]

theorem partnerRel_conj {n r s : ℕ} (c x y : Equiv.Perm (Fin n)) :
    PartnerRel r s (c * x * c⁻¹) (c * y * c⁻¹) ↔ PartnerRel r s x y := by
  have e1 : c * x * c⁻¹ * (c * y * c⁻¹) = c * (x * y) * c⁻¹ := by group
  have e2 : c * (x * y) * c⁻¹ * (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ =
      c * (x * y * x⁻¹ * y⁻¹) * c⁻¹ := by group
  unfold PartnerRel
  rw [e1, e2, orderOf_conjM, orderOf_conjM]

theorem enc_of_prep {n w P : ℕ} {g : Equiv.Perm (Fin n)} (h : PRep n w P g)
    (hlt : P < 2 ^ (n * w)) : P = enc w (cfn g) n := by
  rw [Nat.mul_comm] at hlt
  rw [← enc_fd hlt]
  refine enc_congr fun i hi => ?_
  have e : fd w P i = pg w (mask w) P i := (pg_eq w P i).symm
  exact e.trans ((h ⟨i, hi⟩).trans (cfn_apply g ⟨i, hi⟩).symm)

theorem lt_of_shrM {P k : ℕ} (h : P >>> k = 0) : P < 2 ^ k := by
  by_contra hc
  have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos k)
  rw [Nat.shiftRight_eq_div_pow] at h
  omega

theorem prep_wdP {n w A B : ℕ} {a b : Equiv.Perm (Fin n)} (hn : n < 2 ^ 24) (hw : n + 1 < 2 ^ w)
    (hA : PRep n w A a) (hB : PRep n w B b) :
    ∀ l, PRep n w (wdP n w (mask w) A B l) (wdM a b l)
  | [] => by
    have h := prep_pidn (n := n) (Nat.lt_of_lt_of_le hn (by norm_num)) hw
    simpa [wdP, wdM] using h
  | c :: l => by
    have h := prep_wdP hn hw hA hB l
    have hn32 : n < 2 ^ 32 := Nat.lt_trans hn (by norm_num)
    rw [wdP, strictN_eq]
    rcases c with _ | c
    · have e : wdM a b (0 :: l) = a * wdM a b l := by simp [wdM]
      rw [e]
      exact prep_pcomp hn32 hA h
    · have e : wdM a b ((c + 1) :: l) = b * wdM a b l := by simp [wdM]
      have e' : Nat.beq (c + 1) 0 = false := rfl
      rw [e, e']
      exact prep_pcomp hn32 hB h

theorem wdP_enc {n w A B : ℕ} {a b : Equiv.Perm (Fin n)} (hn : n < 2 ^ 24) (hw : n + 1 < 2 ^ w)
    (hA : PRep n w A a) (hB : PRep n w B b) (l : List ℕ) :
    wdP n w (mask w) A B l = enc w (cfn (wdM a b l)) n := by
  have hn32 : n < 2 ^ 32 := Nat.lt_trans hn (by norm_num)
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h
      simp at hw
    · exact h
  rcases l with _ | ⟨c, l⟩
  · rw [wdP, pidn_eq (by omega) (by omega)]
    exact enc_congr fun x hx => by simp [cfn, hx, wdM]
  · refine enc_of_prep (prep_wdP hn hw hA hB _) (lt_of_shrM ?_)
    rw [wdP, strictN_eq]
    exact PF.pcomp_shr _ _ hn32 hw0

theorem pcolC_eq (n w m r s Y Yi : ℕ) (S : List ℕ) :
    pcolC n w m r s Y Yi S = S.countP fun x => MEnum.pairOKG n w m r s x x Y Yi := by
  induction S with
  | nil => rfl
  | cons x S ih =>
    change strictN (pcolC n w m r s Y Yi S) (fun c =>
      nIf(MEnum.pairOKG n w m r s x x Y Yi, Nat.succ c, c)) = _
    rw [strictN_eq, nIf_eq, List.countP_cons, ih]
    split <;> simp_all

theorem pairOKG_iff {n w X Xi Y Yi r s : ℕ} {x y : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hX : PRep n w X x) (hXi : PRep n w Xi x⁻¹) (hY : PRep n w Y y) (hYi : PRep n w Yi y⁻¹) :
    MEnum.pairOKG n w (mask w) r s X Xi Y Yi = true ↔ PartnerRel r s x y := by
  unfold MEnum.pairOKG
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq]
  rw [← orderOf_of_ordC (prep_pcomp hn hX hY),
    ← orderOf_of_ordC (prep_pcomp hn hX (prep_pcomp hn hY (prep_pcomp hn hXi hYi)))]
  simp only [PartnerRel, mul_assoc]

theorem centJobsOK_sound {n w k : ℕ} {gA gB : Equiv.Perm (Fin n)} {words : List (List Int)}
    {hn : 1 ≤ n} {bv : Vector (Fin n) k} {hbs : bv.toList.Nodup}
    {tA tB : List ℕ} {W : List (List Int)} {bs sz : List ℕ} {NW : ℕ}
    (hA : tA = imageList gA) (hB : tB = imageList gB)
    (hW : W = [[1], [2]] ++ words.map (List.map shiftLabel))
    (hbsv : bs = bv.toList.map Fin.val) (hNW : NW = words.length + 2) (hn16 : n < 2 ^ 16)
    (hbase : mBase n w bs sz NW tA tB W = true) {RW : List (List ℕ)}
    {JB : List (ℕ × ℕ × List (List (ℕ × ℕ × ℕ)) × ℕ)}
    (hok : centJobsOK n w bs NW tA tB W RW JB = true) :
    ∀ j ∈ JB, Nat.card {h : Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) //
      (h : Equiv.Perm (Fin n)) * wdM gA gB (RW.getD j.1 []) = wdM gA gB (RW.getD j.2.1 []) * h} =
        j.2.2.2 := by
  obtain ⟨hn24, hw, hbsl⟩ := mBase_facts hbase
  obtain ⟨-, -, -, hL⟩ := mBase_chain (hn := hn) (hbs := hbs) (sh := shiftLabel) (fun _ => rfl)
    hA hB hW hbsv hNW hn16 hbase
  have pA : PRep n w (packL w tA) gA := by subst hA; exact (prep_packL hw).1
  have pB : PRep n w (packL w tB) gB := by subst hB; exact (prep_packL hw).1
  unfold centJobsOK at hok
  simp only [strictN_eq, Nat.mul_eq, Nat.add_eq] at hok
  rw [levN_eq hn16 hw hL hbsl] at hok
  simp only [nIf_eq] at hok
  split_ifs at hok with hall
  · intro j hj
    have h1 := List.all_eq_true.1 hall j hj
    simp only [jobC, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h1
    obtain ⟨htr, hcnt⟩ := h1
    rw [wdP_enc hn24 hw pA pB] at htr hcnt
    rw [wdP_enc hn24 hw pA pB, levPairs_eq, List.map_map] at hcnt
    rw [← cntCM_card (hn := hn) (hbs := hbs) hA hB hW hbsv hNW hn16 hbase _ _ htr,
      cntCM_eq hn16 hw hL hbsl]
    exact hcnt

theorem repOrdPairOK_sound {n w r s ky : ℕ} {gA gB : Equiv.Perm (Fin n)} {tA tB : List ℕ}
    {RW : List (List ℕ)} {OR PC S : List ℕ} (hn : n < 2 ^ 24) (hw : n + 1 < 2 ^ w)
    (hA : tA = imageList gA) (hB : tB = imageList gB)
    (hok : repOrdPairOK n w r s ky tA tB RW OR PC S = true) :
    ∀ i < RW.length, orderOf (wdM gA gB (RW.getD i [])) = OR.getD i 0 ∧
      (OR.getD i 0 = ky → pcolC n w (mask w) r s (wdP n w (mask w) (packL w tA) (packL w tB)
        (RW.getD i [])) (pinvS n w (mask w) (wdP n w (mask w) (packL w tA) (packL w tB)
          (RW.getD i []))) S = PC.getD i 0) := by
  have pA : PRep n w (packL w tA) gA := by subst hA; exact (prep_packL hw).1
  have pB : PRep n w (packL w tB) gB := by subst hB; exact (prep_packL hw).1
  intro i hi
  unfold repOrdPairOK at hok
  simp only [strictB_eq, List.all_eq_true, List.mem_range] at hok
  have h1 := hok i hi
  rw [bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨ho, hp⟩ := h1
  have e := orderOf_of_ordC (prep_wdP hn hw pA pB (RW.getD i []))
  rw [Nat.beq_eq] at ho
  refine ⟨e.trans ho, fun hk => ?_⟩
  have hb : Nat.beq (M11.ordC n w (mask w) (wdP n w (mask w) (packL w tA) (packL w tB)
      (RW.getD i []))) ky = true := by
    rw [Nat.beq_eq, ho, hk]
  rw [hb] at hp
  exact Nat.eq_of_beq_eq_true hp

theorem mCent_sound {n w k : ℕ} {gA gB : Equiv.Perm (Fin n)} {words : List (List Int)}
    {hn : 1 ≤ n} {bv : Vector (Fin n) k} {hbs : bv.toList.Nodup}
    {tA tB : List ℕ} {W : List (List Int)} {bs sz : List ℕ} {NW ky r s cap : ℕ}
    {RW : List (List ℕ)} {JB : List (ℕ × ℕ × List (List (ℕ × ℕ × ℕ)) × ℕ)}
    {CB OR PC RX : List ℕ} {d : ClassDatum}
    (hA : tA = imageList gA) (hB : tB = imageList gB)
    (hW : W = [[1], [2]] ++ words.map (List.map shiftLabel))
    (hbsv : bs = bv.toList.map Fin.val) (hNW : NW = words.length + 2) (hn16 : n < 2 ^ 16)
    (hbase : mBase n w bs sz NW tA tB W = true)
    (hjob : centJobsOK n w bs NW tA tB W RW JB = true)
    (hrep : repOrdPairOK n w r s ky tA tB RW OR PC d.2.2.2.2.2.2 = true)
    (hcj : ∀ i < RW.length, CB.getD i 0 = sz.prod ∨
      (JB.any fun j => j.1 == i && j.2.1 == i && j.2.2.2 == CB.getD i 0) = true)
    (hnc : ∀ i < RW.length, ∀ j < RW.length, i < j → OR.getD i 0 ≠ OR.getD j 0 ∨
      (JB.any fun t => t.1 == i && t.2.1 == j && t.2.2.2 == 0) = true)
    (hsum : ((List.range RW.length).map fun i => sz.prod / CB.getD i 0).sum = sz.prod)
    (h2 : ∀ i < RW.length, ∀ j < RW.length, OR.getD i 0 = 2 → OR.getD j 0 = 2 → i = j)
    (hRX : wdP n w (mask w) (packL w tA) (packL w tB) RX = d.2.2.1)
    (hcls : ∀ ρ : Equiv.Perm (Fin n), PRep n w d.2.2.1 ρ →
      (CFSG.Sporadic.SmallOddCore.conjClass
        (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) ρ).ncard =
          d.2.2.2.2.2.2.length ∧ d.2.2.2.2.2.2.length ≤ cap ∧ orderOf ρ = 2 ∧
      (∀ z, z ∈ CFSG.Sporadic.SmallOddCore.conjClass
        (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) ρ ↔
          ∃ k < d.2.2.2.2.2.2.length, PRep n w (d.2.2.2.2.2.2.getD k 0) z) ∧
      (∀ i j, i < j → j < d.2.2.2.2.2.2.length →
        d.2.2.2.2.2.2.getD i 0 < d.2.2.2.2.2.2.getD j 0) ∧
      (∀ x ∈ d.2.2.2.2.2.2, x < 2 ^ (n * w)) ∧ d.2.2.1 < 2 ^ (n * w))
    (hoA : ordC n w (mask w) (packL w tA) = 2) (hoB : ordC n w (mask w) (packL w tB) = ky)
    (hpair : pairOKG n w (mask w) r s (packL w tA) (pinvS n w (mask w) (packL w tA))
      (packL w tB) (pinvS n w (mask w) (packL w tB)) = true)
    (hr : 0 < r) (hs : 0 < s) (hky : 0 < ky) :
    let Q := certificate hn [gA, gB] words bv hbs
    Q.check = true ∧ ordTest n 2 (toTable gA) = true ∧ ordTest n ky (toTable gB) = true ∧
      pairTest n r s 2 ky (toTable gA) (toTable gB) = true ∧
      (orderTables Q 2).length = ((List.range RW.length).map fun i =>
        if OR.getD i 0 = 2 then sz.prod / CB.getD i 0 else 0).sum ∧
      (orderTables Q ky).length = ((List.range RW.length).map fun i =>
        if OR.getD i 0 = ky then sz.prod / CB.getD i 0 else 0).sum ∧
      classOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2) cap = true ∧
      classTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2)
        (orderTables Q ky) cap r s 2 ky = ((List.range RW.length).map fun i =>
          if OR.getD i 0 = ky then sz.prod / CB.getD i 0 * PC.getD i 0 else 0).sum := by
  classical
  intro Q
  obtain ⟨hn24, hw, -⟩ := mBase_facts hbase
  obtain ⟨hQ, hperm, hszs, -⟩ := mBase_chain (hn := hn) (hbs := hbs) (sh := shiftLabel)
    (fun _ => rfl) hA hB hW hbsv hNW hn16 hbase
  have hn32 : n < 2 ^ 32 := Nat.lt_trans hn24 (by norm_num)
  have hwn : n < 2 ^ w := by omega
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  set S := d.2.2.2.2.2.2
  set N := RW.length
  set E := enumeration Q
  have hV : ValidSchreier Q := hQ
  have hGK : Q.originalSubgroup = K := CFSG.KS.SporSch.MOC.orig_pair hn hbs
  have hmemE : ∀ g, g ∈ E ↔ g ∈ K := fun g => by
    rw [← hGK]
    exact mem_enumeration_iff Q hV g
  have hndE : E.Nodup := enumeration_nodup Q hV
  have hEl : E.length = sz.prod := by
    rw [hperm.length_eq, length_products, List.map_map, ← hszs]
    congr 1
    exact List.map_congr_left fun i _ => by simp
  have hcardK : Nat.card K = sz.prod := by
    have h := card_subtype_eq_countP K E hndE hmemE (fun _ => True)
    have e : Nat.card {x : K // True} = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    rw [← e, h, ← hEl]
    simp
  have pA : PRep n w (packL w tA) gA := by subst hA; exact (prep_packL hw).1
  have pB : PRep n w (packL w tB) gB := by subst hB; exact (prep_packL hw).1
  have pAi := (prep_pinvS hwn pA).1
  have pBi := (prep_pinvS hwn pB).1
  have hoA' : orderOf gA = 2 := (orderOf_of_ordC pA).trans hoA
  have hoB' : orderOf gB = ky := (orderOf_of_ordC pB).trans hoB
  have hpair' : orderOf (gA * gB) = r ∧ orderOf (gA * gB * gA⁻¹ * gB⁻¹) = s :=
    (pairOKG_iff hn32 pA pAi pB pBi).1 hpair
  have hPW := prep_wdP hn24 hw pA pB
  set rp : ℕ → K := fun i => ⟨wdM gA gB (RW.getD i []), wdM_mem gA gB _⟩ with hrp
  have hrpv : ∀ i, ((rp i : K) : Equiv.Perm (Fin n)) = wdM gA gB (RW.getD i []) := fun _ => rfl
  have hR := repOrdPairOK_sound hn24 hw hA hB hrep
  have hJ := centJobsOK_sound (hn := hn) (hbs := hbs) hA hB hW hbsv hNW hn16 hbase hjob
  have hc : ∀ i < N, Nat.card (Subgroup.centralizer {rp i}) ≤ CB.getD i 0 := by
    intro i hi
    rw [card_cent_eq K (rp i)]
    rcases hcj i hi with h | h
    · rw [h, ← hcardK]
      exact Finite.card_subtype_le _
    · obtain ⟨j, hj, hjj⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, beq_iff_eq] at hjj
      obtain ⟨⟨e1, e2⟩, e3⟩ := hjj
      have := hJ j hj
      rw [e1, e2, e3] at this
      exact this.le
  have hnc' : ∀ i < N, ∀ j < N, i < j → ¬ IsConj (rp i) (rp j) := by
    intro i hi j hj hij hcon
    rcases hnc i hi j hj hij with h | h
    · apply h
      rw [← (hR i hi).1, ← (hR j hj).1]
      exact orderOf_isConjK hcon
    · obtain ⟨t, ht, htt⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, beq_iff_eq] at htt
      obtain ⟨⟨e1, e2⟩, e3⟩ := htt
      have := hJ t ht
      rw [e1, e2, e3] at this
      exact not_isConj_of_cnt0 (rp i) (rp j) this hcon
  have hsum' : ∑ i ∈ Finset.range N, Nat.card K / CB.getD i 0 = Nat.card K := by
    rw [hcardK, ← sum_range_list]
    exact hsum
  cases nonempty_fintype K
  have hCS := classEq_sum rp (fun i => CB.getD i 0) hc hnc' hsum'
  obtain ⟨hcov, -⟩ := classEq_cover rp (fun i => CB.getD i 0) hc hnc' hsum'
  have hcnt : ∀ m, E.countP (fun σ => decide (orderOf σ = m)) = ((List.range N).map fun i =>
      if OR.getD i 0 = m then sz.prod / CB.getD i 0 else 0).sum := by
    intro m
    rw [← card_subtype_eq_countP K E hndE hmemE, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_filter, hCS (fun x => if orderOf (x : Equiv.Perm (Fin n)) = m then 1 else 0)
        (fun x y hxy => by simp only [orderOf_isConjK hxy]), sum_range_list, hcardK]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hrpv, (hR i (Finset.mem_range.1 hi)).1]
    split_ifs <;> simp
  have hOT : ∀ m, 0 < m → (orderTables Q m).length = E.countP fun σ => decide (orderOf σ = m) :=
    fun m hm => by
      rw [(forall₂_orderTables hn32 Q hm).length_eq, List.length_reverse,
        List.countP_eq_length_filter]
  set ρ := wdM gA gB RX
  have pR : PRep n w d.2.2.1 ρ := hRX ▸ hPW RX
  obtain ⟨hρcard, hρcap, hρ2, hρmem, hρinc, hSlt, -⟩ := hcls ρ pR
  have hρK : ρ ∈ K := wdM_mem gA gB RX
  have hinv : ∀ y ∈ K, orderOf y = 2 → y ∈ CFSG.Sporadic.SmallOddCore.conjClass K ρ := by
    intro y hy hy2
    obtain ⟨i, hi, hyi⟩ := hcov ⟨y, hy⟩
    obtain ⟨j, hj, hρj⟩ := hcov ⟨ρ, hρK⟩
    have hi2 : OR.getD i 0 = 2 := by
      rw [← (hR i hi).1, ← hrpv, ← orderOf_isConjK hyi]
      exact hy2
    have hj2 : OR.getD j 0 = 2 := by
      rw [← (hR j hj).1, ← hrpv, ← orderOf_isConjK hρj]
      exact hρ2
    obtain rfl := h2 i hi j hj hi2 hj2
    obtain ⟨c, hc⟩ := isConj_iff.1 (hρj.trans hyi.symm)
    have e := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    simp only [CFSG.Sporadic.SmallOddCore.conjClass, Set.mem_ofPred_eq]
    exact ⟨c, c.2, e.symm⟩
  have hcls2 : ∀ z ∈ CFSG.Sporadic.SmallOddCore.conjClass K ρ, z ∈ K ∧ orderOf z = 2 := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := hz
    exact ⟨K.mul_mem (K.mul_mem hc hρK) (K.inv_mem hc), (orderOf_conjM c ρ).trans hρ2⟩
  have hXf := forall₂_orderTables hn32 Q (m := 2) (by decide)
  have hg := rep_pair hn32 gA gB
  have hgK := genK_pair gA gB
  have hok : classOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2) cap = true := by
    refine CFSG.KS.SporSch.ClsSpec.classOK_of_closed hg hXf (fun y hy => ?_)
      (List.nodup_reverse.2 (hndE.filter _)) (fun y hy z hz => ?_)
    · rw [hgK]
      rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, hmemE] at hy
      have hyρ := hinv y hy.1 hy.2
      have e : CFSG.Sporadic.SmallOddCore.conjClass K y =
          CFSG.Sporadic.SmallOddCore.conjClass K ρ := by
        ext z
        exact ⟨fun h => conjClass_trans h hyρ, fun h => conjClass_trans h (conjClass_symm hyρ)⟩
      rw [e, hρcard]
      exact hρcap
    · rw [hgK] at hz
      rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, hmemE] at hy ⊢
      obtain ⟨c, hc, rfl⟩ := hz
      exact ⟨K.mul_mem (K.mul_mem hc hy.1) (K.inv_mem hc), (orderOf_conjM c y).trans hy.2⟩
  have hSnd : S.Nodup := by
    have hP : S.Pairwise (· < ·) := List.pairwise_iff_getElem.2 fun i j hi hj hij => by
      have := hρinc i j hij hj
      rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at this
    exact hP.imp ne_of_lt
  set T : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter fun z => z ∈ CFSG.Sporadic.SmallOddCore.conjClass K ρ
  set φ : Equiv.Perm (Fin n) → ℕ := fun z => enc w (cfn z) n
  have hφP : ∀ z, PRep n w (φ z) z := fun z x => pg_cfn hwn z x
  have hφi : Function.Injective φ := fun z1 z2 h => Equiv.ext fun x => by
    have e1 := hφP z1 x
    rw [h, hφP z2 x] at e1
    exact Fin.ext e1.symm
  have hTS : T.image φ = S.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun X hX => ?_) ?_
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨k, hk, pk⟩ := (hρmem z).1 (Finset.mem_filter.1 hz).2
      have hkm : S.getD k 0 ∈ S := by
        rw [List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      rw [List.mem_toFinset]
      change enc w (cfn z) n ∈ S
      rw [← enc_of_prep pk (hSlt _ hkm)]
      exact hkm
    · rw [Finset.card_image_of_injective _ hφi, List.toFinset_card_of_nodup hSnd, ← hρcard,
        ← Set.ncard_coe_finset]
      refine le_of_eq (congrArg Set.ncard ?_)
      ext z
      simp [T]
  have hpc : ∀ (y : Equiv.Perm (Fin n)) (Y Yi : ℕ), PRep n w Y y → PRep n w Yi y⁻¹ →
      (∑ x : K, if orderOf (x : Equiv.Perm (Fin n)) = 2 ∧ PartnerRel r s (x : Equiv.Perm (Fin n)) y
        then 1 else 0) = pcolC n w (mask w) r s Y Yi S := by
    intro y Y Yi pY pYi
    rw [pcolC_eq, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hSnd.filter _),
      List.toFinset_filter, ← hTS, Finset.filter_image, Finset.card_image_of_injective _ hφi,
      ← Finset.card_filter]
    rw [← Finset.card_map (Function.Embedding.subtype (· ∈ K))]
    congr 1
    ext z
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, T]
    constructor
    · rintro ⟨x, ⟨hx2, hxy⟩, rfl⟩
      have hzc := hinv x x.2 hx2
      refine ⟨hzc, ?_⟩
      have hinv' : (x : Equiv.Perm (Fin n))⁻¹ = x := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← sq, ← hx2, pow_orderOf_eq_one]
      have pXi : PRep n w (φ x) (x : Equiv.Perm (Fin n))⁻¹ := by
        rw [hinv']
        exact hφP _
      rw [pairOKG_iff hn32 (hφP _) pXi pY pYi]
      exact hxy
    · rintro ⟨hzc, hp⟩
      obtain ⟨hzK, hz2⟩ := hcls2 z hzc
      have hinv' : z⁻¹ = z := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← sq, ← hz2, pow_orderOf_eq_one]
      have pZi : PRep n w (φ z) z⁻¹ := by
        rw [hinv']
        exact hφP _
      rw [pairOKG_iff hn32 (hφP _) pZi pY pYi] at hp
      exact ⟨⟨z, hzK⟩, ⟨hz2, hp⟩, rfl⟩
  set f : K → ℕ := fun y => if orderOf (y : Equiv.Perm (Fin n)) = ky then
    ∑ x : K, (if orderOf (x : Equiv.Perm (Fin n)) = 2 ∧
      PartnerRel r s (x : Equiv.Perm (Fin n)) y then 1 else 0) else 0 with hfdef
  have hkey : ∀ x c : K, f x = f (c * x * c⁻¹) := by
    intro x c
    have e1 : ((c * x * c⁻¹ : K) : Equiv.Perm (Fin n)) =
        (c : Equiv.Perm (Fin n)) * x * (c : Equiv.Perm (Fin n))⁻¹ := by simp
    simp only [f, e1, orderOf_conjM]
    congr 1
    refine Fintype.sum_equiv (MulAut.conj c).toEquiv _ _ fun z => ?_
    have e3 : (((MulAut.conj c).toEquiv z : K) : Equiv.Perm (Fin n)) =
        (c : Equiv.Perm (Fin n)) * z * (c : Equiv.Perm (Fin n))⁻¹ := by simp
    simp only [e3, orderOf_conjM, partnerRel_conj]
  have hdc : (∑ p : K × K, if orderOf (p.1 : Equiv.Perm (Fin n)) = 2 ∧
      orderOf (p.2 : Equiv.Perm (Fin n)) = ky ∧
        PartnerRel r s (p.1 : Equiv.Perm (Fin n)) p.2 then 1 else 0) = ∑ y : K, f y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hfdef]
    dsimp only
    by_cases hy : orderOf (y : Equiv.Perm (Fin n)) = ky
    · rw [ite_eq_left hy]
      exact Finset.sum_congr rfl fun x _ =>
        if_congr ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hy, h.2⟩⟩ rfl rfl
    · rw [ite_eq_right hy]
      exact Finset.sum_eq_zero fun x _ => ite_eq_right fun h => hy h.2.1
  have hab : gA ∈ Q.originalSubgroup ∧ gB ∈ Q.originalSubgroup := by
    rw [hGK]
    exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
  have htot : classTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (orderTables Q 2)
      (orderTables Q ky) cap r s 2 ky = ((List.range N).map fun i =>
        if OR.getD i 0 = ky then sz.prod / CB.getD i 0 * PC.getD i 0 else 0).sum := by
    rw [← card_image_pairs_eq_classTotal₂ hn32 Q hV (by decide) hky hr hs hab.1 hab.2 cap hok, hGK]
    have hcoe : ∀ p : K × K, (orderOf p.1 = 2 ∧ orderOf p.2 = ky ∧ orderOf (p.1 * p.2) = r ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s) ↔
        (orderOf (p.1 : Equiv.Perm (Fin n)) = 2 ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = ky ∧
          PartnerRel r s (p.1 : Equiv.Perm (Fin n)) p.2) := fun p => by
      simp only [PartnerRel, ← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe), Nat.card_eq_fintype_card,
      Fintype.card_subtype, Finset.card_filter, hdc,
      hCS f fun x y hxy => by
        obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
        exact hkey x c,
      sum_range_list, hcardK]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    simp only [f, hrpv, (hR i hi').1]
    split_ifs with hk
    · rw [hpc _ _ _ (hPW _) (prep_pinvS hwn (hPW _)).1, (hR i hi').2 hk]
    · simp
  exact ⟨hQ, (ordTest_iff perm_faithful (rep_toTable hn32 gA) (by decide)).2 hoA',
    (ordTest_iff perm_faithful (rep_toTable hn32 gB) hky).2 hoB',
    (pairTest_iff perm_faithful (rep_toTable hn32 gA) (rep_toTable hn32 gB) hr hs hoA' hoB'
      (by decide) hky).2 hpair', by rw [hOT 2 (by decide), hcnt 2],
    by rw [hOT ky hky, hcnt ky], hok, htot⟩

end CFSG.KS.MCent

end
