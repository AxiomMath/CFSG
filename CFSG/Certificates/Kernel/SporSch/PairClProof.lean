module

public import CFSG.Certificates.Kernel.SporSch.PairClDefs
public import CFSG.Certificates.Kernel.SporSch.ConjClosReplay
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KS.SporSch.ClP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Raw.Dec CFSG.KS.NKey
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.KS.SporSch

theorem keyL_eq (n : Nat) (f : Nat → Nat) : ∀ bs : List Nat, keyL n f bs = imgKey n (bs.map f)
  | [] => rfl
  | b :: bs => by
    change strictN (keyL n f bs) (fun r => Nat.add (f b) (Nat.mul n r)) = _
    rw [strictN_eq, keyL_eq n f bs]
    rfl

theorem range_of_canonL {n w : Nat} : ∀ {Ws : List Nat}, canonL n w Ws = true →
    ∀ W ∈ Ws, ∀ q < n, pg w (mask w) W q < n
  | [], _, W, hW => by simp at hW
  | V :: Ws, h, W, hW => by
    change bAnd(CFSG.KS.Prim.canonK n w (mask w) (Nat.mul n w) V, canonL n w Ws) = true at h
    rw [bAnd_iff] at h
    rcases List.mem_cons.1 hW with rfl | hW
    · intro q hq
      have := allN_spec (CFSG.KS.Raw.range_of_canonK h.1) q hq
      simpa using this
    · exact range_of_canonL h.2 W hW

theorem evRK_eq {n w : Nat} : ∀ {Ws : List Nat}, (∀ W ∈ Ws, ∀ q < n, pg w (mask w) W q < n) →
    ∀ p < n, evRK w Ws p = evR (Ws.map (unpack n w)) p ∧ evRK w Ws p < n
  | [], _, p, hp => ⟨rfl, hp⟩
  | W :: Ws, hW, p, hp => by
    have h1 := hW W List.mem_cons_self p hp
    have ih := evRK_eq (Ws := Ws) (fun V hV => hW V (List.mem_cons_of_mem _ hV)) _ h1
    change strictN (pg w (mask w) W p) (evRK w Ws) = _ ∧
      strictN (pg w (mask w) W p) (evRK w Ws) < n
    rw [strictN_eq]
    refine ⟨?_, ih.2⟩
    rw [ih.1, List.map_cons, evR_cons, unpack_get hp]

@[expose] noncomputable def nfArr (nb NF : Nat) : Array Nat :=
  Array.ofFn (n := nb) fun t => Nat.land (Nat.shiftRight NF (Nat.mul (nat_lit 16) t.val))
    (nat_lit 65535)

theorem nfArr_size (nb NF : Nat) : (nfArr nb NF).size = nb := Array.size_ofFn

theorem nfArr_get {nb NF t : Nat} (ht : t < nb) :
    (nfArr nb NF)[t]! = Nat.land (Nat.shiftRight NF (Nat.mul (nat_lit 16) t)) (nat_lit 65535) := by
  rw [nfArr, getElem!_ofFn_nat _ ht]

theorem fld_nfX {nb x t : Nat} (ht : t < nb) :
    Nat.land (Nat.shiftRight (nfX nb x) (Nat.mul (nat_lit 16) t)) (nat_lit 65535) =
      Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 16) t)) (nat_lit 65535) := by
  have e16 : (nat_lit 65535) = mask 16 := rfl
  unfold nfX
  have shr : ∀ a b : Nat, Nat.shiftRight a b = a / 2 ^ b := fun a b => Nat.shiftRight_eq_div_pow a b
  rw [e16, land_mask, land_mask, land_mask, shr, shr]
  have hp : 2 ^ (Nat.mul 16 nb) = 2 ^ (Nat.mul 16 t) * 2 ^ (16 * (nb - t)) := by
    rw [← Nat.pow_add]
    congr 1
    change 16 * nb = 16 * t + 16 * (nb - t)
    rw [← Nat.mul_add, Nat.add_sub_cancel' (Nat.le_of_lt ht)]
  rw [hp, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  have : 1 ≤ nb - t := by omega
  exact Nat.pow_dvd_pow 2 (by omega)

theorem nfPt_succ (n w : Nat) (LR TR : Nat → Nat) (j NF x : Nat) :
    nfPt n w LR TR (j + 1) NF x = nfPt n w LR TR j NF (pg w (mask w)
      (trK n (Nat.mul n w) LR TR j (Nat.land (Nat.shiftRight NF (Nat.mul (nat_lit 16) j))
        (nat_lit 65535))) x) :=
  strictN_eq _ _

section Levels

variable {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
include hb hp hl

theorem lev_tr {i k : Nat} (hi : i < nb) (hk : k < rcnt (LR i)) :
    (rawLevels n S base)[i]!.pts.size = rcnt (LR i) ∧
      ∀ x < n, ((rawLevels n S base)[i]!.tr[k]!)[x]! = pg w (mask w) (trK n (Nat.mul n w) LR TR i k) x := by
  have hbl := base_lt_of_levels hb hl
  obtain ⟨A, P⟩ := agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  have hk' : k < (CFSG.Certificates.ChainArrays.lev n S base i).pts.size := by rw [← A.cnt]; exact hk
  refine ⟨A.cnt.symm, fun x hx => ?_⟩
  have h1 := (A.tr k hk').1 ⟨x, hx⟩
  have h2 := (P k hk).1 ⟨x, hx⟩
  exact h1.trans h2.symm

theorem nfPt_eq {NF : Nat}
    (hv : ∀ t < nb, Nat.land (Nat.shiftRight NF (Nat.mul (nat_lit 16) t)) (nat_lit 65535) <
      rcnt (LR t)) :
    ∀ j ≤ nb, ∀ x < n, nfPt n w LR TR j NF x =
      evR (hw (rawLevels n S base) (nfArr nb NF) j) x := by
  have hL := lvOK_rawLevels hb hp (base_lt_of_levels hb hl)
  have hsz : (rawLevels n S base).size = nb := by
    rw [rawLevels, Array.size_ofFn, hb.2.2.2.2.2.1]
  intro j
  induction j with
  | zero => intro _ x _; rfl
  | succ j ih =>
    intro hj x hx
    obtain ⟨hc, ht⟩ := lev_tr hb hp hl (by omega : j < nb) (hv j (by omega))
    have hlt := hL.trlt j (by omega) _ (by rw [hc]; exact hv j (by omega)) x hx
    rw [nfPt_succ, evR_hw_succ, nfArr_get (by omega : j < nb), ← ht x hx]
    exact ih (by omega) _ hlt

theorem nfOK_nfArr {NF : Nat}
    (hv : ∀ t < nb, Nat.land (Nat.shiftRight NF (Nat.mul (nat_lit 16) t)) (nat_lit 65535) <
      rcnt (LR t)) :
    nfOK (rawLevels n S base) (nfArr nb NF) = true := by
  have hsz : (rawLevels n S base).size = nb := by
    rw [rawLevels, Array.size_ofFn, hb.2.2.2.2.2.1]
  unfold nfOK
  rw [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨by rw [nfArr_size, hsz], fun i hi => decide_eq_true ?_⟩
  rw [nfArr_size] at hi
  rw [nfArr_get hi, (lev_tr hb hp hl hi (hv i hi)).1]
  exact hv i hi

omit hp in
theorem base_mem_lt {b : Nat} (hm : b ∈ base.toList) : b < n := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hm
  have ht' : t < base.size := by simpa using ht
  have := base_lt_of_levels hb hl t (by rw [← hb.2.2.2.2.2.1]; exact ht')
  rw [Array.getElem_toList]
  rwa [getElem!_pos base t ht'] at this

theorem nfKey_eq {NF : Nat}
    (hv : ∀ t < nb, Nat.land (Nat.shiftRight NF (Nat.mul (nat_lit 16) t)) (nat_lit 65535) <
      rcnt (LR t)) :
    nfKey n w LR TR nb base.toList NF =
      imgKey n (baseImgs base.toList (nfWord (rawLevels n S base) (nfArr nb NF))) := by
  unfold nfKey baseImgs
  rw [keyL_eq]
  congr 1
  refine List.map_congr_left fun b hm => ?_
  rw [nfWord_eq_hw, nfArr_size]
  exact nfPt_eq hb hp hl hv nb (Nat.le_refl nb) b (base_mem_lt hb hl hm)

theorem conjKey_eq {NF G GI : Nat} {g gi : Array Nat}
    (hv : ∀ t < nb, Nat.land (Nat.shiftRight NF (Nat.mul (nat_lit 16) t)) (nat_lit 65535) <
      rcnt (LR t))
    (hg : g = unpack n w G) (hgi : gi = unpack n w GI)
    (hG : permOK n w (mask w) (n * w) G GI = true) :
    conjKey n w LR TR nb base.toList G GI NF =
      imgKey n (conjImgs base.toList g gi (nfWord (rawLevels n S base) (nfArr nb NF))) := by
  have hL := lvOK_rawLevels hb hp (base_lt_of_levels hb hl)
  have hnf := nfOK_nfArr hb hp hl hv
  obtain ⟨R1, R2⟩ := rep_permOfArr (isInvA_unpack hG)
  unfold conjKey conjImgs
  rw [keyL_eq]
  congr 1
  refine List.map_congr_left fun b hm => ?_
  have hbn := base_mem_lt hb hl hm
  have hy : gi[b]! < n := by rw [hgi]; exact R2.lt hbn
  have hy' : gi[b]! = pg w (mask w) GI b := by rw [hgi, unpack_get hbn]
  have hz := evR_hw_lt hL hnf nb (by rw [nfArr_size]) _ hy
  rw [nfWord_eq_hw, nfArr_size, ← hy', nfPt_eq hb hp hl hv nb (Nat.le_refl nb) _ hy, hg,
    unpack_get hz]

end Levels

theorem wordKey_eq {n w : Nat} {bs RP : List Nat} (hRP : canonL n w RP = true)
    (hbs : ∀ b ∈ bs, b < n) :
    wordKey n w bs RP = imgKey n (baseImgs bs (RP.map (unpack n w))) := by
  unfold wordKey baseImgs
  rw [keyL_eq]
  congr 1
  exact List.map_congr_left fun b hm => (evRK_eq (range_of_canonL hRP) b (hbs b hm)).1

@[expose] noncomputable def posW (W : Nat → Nat) (h l : Nat) : Nat :=
  Nat.land (Nat.shiftRight (W h) (Nat.mul (nat_lit 20) l)) (nat_lit 1048575)

theorem posW_eq (W : Nat → Nat) (h l : Nat) :
    Nat.land (Nat.shiftRight (W h) (Nat.mul (nat_lit 20) l)) (nat_lit 1048575) = posW W h l := rfl

theorem brec_ite (b : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t b = if b = true then t else e := by
  cases b <;> rfl

theorem failC_eq : failC = 1099511627776 := rfl

section Step

variable {n w : Nat} {LR TR TRI : Nat → Nat} {nb : Nat} {bs : List Nat} {G GI X W : Nat → Nat}
  {c h l cur : Nat}

theorem stepNF_spec (hne : stepNF n w LR TR TRI nb bs G GI X W c h l cur ≠ failC) :
    (h < cur ∧ posW W h l < cur ∧ nfKey n w LR TR nb bs (nfX nb (X (posW W h l))) =
        conjKey n w LR TR nb bs (G l) (GI l) (nfX nb (X h)) ∧
        stepNF n w LR TR TRI nb bs G GI X W c h l cur = cur) ∨
      (h < cur ∧ posW W h l = cur ∧ nfKey n w LR TR nb bs (nfX nb (X (posW W h l))) =
        conjKey n w LR TR nb bs (G l) (GI l) (nfX nb (X h)) ∧
        parNF nb (X (posW W h l)) = h ∧ labNF nb (X (posW W h l)) = l ∧
        stepNF n w LR TR TRI nb bs G GI X W c h l cur = cur + 1) ∨
      (cur ≤ h ∧ cur = c ∧ stepNF n w LR TR TRI nb bs G GI X W c h l cur = cur) := by
  unfold stepNF at hne ⊢
  simp only [strictN_eq, bAnd_eq, posW_eq, brec_ite, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.succ_eq_add_one] at hne ⊢
  split_ifs at hne ⊢ with h1 h2 h3 h4
  all_goals first
    | exact absurd rfl hne
    | exact Or.inl ⟨h1, h2.1, h2.2, rfl⟩
    | exact Or.inr (Or.inl ⟨h1, h3.1, h3.1 ▸ h3.2.1, h3.1 ▸ h3.2.2.2.1, h3.1 ▸ h3.2.2.2.2, rfl⟩)
    | exact Or.inr (Or.inl ⟨h1, h3.1, h3.2.1, h3.2.2.2.1, h3.2.2.2.2, rfl⟩)
    | exact Or.inr (Or.inr ⟨Nat.le_of_not_lt h1, h2, rfl⟩)
    | exact Or.inr (Or.inr ⟨Nat.le_of_not_lt h1, h3, rfl⟩)
    | exact Or.inr (Or.inr ⟨Nat.le_of_not_lt h1, h4, rfl⟩)

theorem stepNF_fail : stepNF n w LR TR TRI nb bs G GI X W c h l failC = failC := by
  have hj : posW W h l ≤ 1048575 := Nat.and_le_right
  unfold stepNF
  simp only [strictN_eq, bAnd_eq, posW_eq, brec_ite, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.succ_eq_add_one]
  generalize posW W h l = j at hj ⊢
  have hf := failC_eq
  split_ifs with h1 h2 h3 h4 <;> first | rfl | omega

end Step

theorem closNF_proved {n w kS nb BP kg c cap nS R H nB B : Nat}
    {PS PSI LR TR TRI G GI X W C : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs RP : List Nat}
    {gens gensInv : Array (Array Nat)} {rep : List (Array Nat)}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hbs : base.toList = bs)
    (hg : gens.size = kg ∧ gensInv.size = kg ∧
      ∀ l < kg, gens[l]! = unpack n w (G l) ∧ gensInv[l]! = unpack n w (GI l))
    (hrep : rep = RP.map (unpack n w))
    (h : ClosNFOK n w kS nb BP PS PSI LR TR TRI bs kg G GI RP c cap nS R H nB B X W C)
    (hD : ((List.range c).map fun i => nfKey n w LR TR nb bs (nfX nb (X i))).Nodup) :
    closureOK (rawLevels n S base) bs gens gensInv rep
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.2 = true ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.size = c ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.toList.map
          (fun nf => imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf))) =
        (List.range c).map fun i => nfKey n w LR TR nb bs (nfX nb (X i)) := by
  subst hbs hrep
  obtain ⟨hgs, hgis, hgl⟩ := hg
  subst hgs
  obtain ⟨hc0, hcap, hcS, hcB, hc20, -, -, hG, hRP, -, hst, hk0, hnf, hC0, hCN, hrun⟩ := h
  have hbl := base_lt_of_levels hb hl
  have hLv := lvOK_rawLevels hb hp hbl
  have hbn : ∀ b ∈ base.toList, b < n := fun b hm => base_mem_lt hb hl hm
  have hv : ∀ i < c, ∀ t < nb,
      Nat.land (Nat.shiftRight (nfX nb (X i)) (Nat.mul (nat_lit 16) t)) (nat_lit 65535) <
        rcnt (LR t) := by
    intro i hi t ht
    have h1 := all_of_blocks hcB hnf i hi
    unfold nfOKAt at h1
    rw [blt_true hi] at h1
    have h2 : strictB (X i) (fun x => allN nb (fun t =>
        Nat.blt (Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 16) t)) (nat_lit 65535))
          (rcnt (LR t)))) = true := h1
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h2
    rw [fld_nfX ht]
    exact Nat.blt_eq.mp (allN_spec h2 t ht)
  have hTok : ∀ i < c, nfOK (rawLevels n S base) (nfArr nb (nfX nb (X i))) = true :=
    fun i hi => nfOK_nfArr hb hp hl (hv i hi)
  have hκ : ∀ i < c, imgKey n (baseImgs base.toList (nfWord (rawLevels n S base)
      (nfArr nb (nfX nb (X i))))) = nfKey n w LR TR nb base.toList (nfX nb (X i)) :=
    fun i hi => (nfKey_eq hb hp hl (hv i hi)).symm
  have hsk : ∀ i < c, ∀ l < gens.size, imgKey n (conjImgs base.toList gens[l]! gensInv[l]!
      (nfWord (rawLevels n S base) (nfArr nb (nfX nb (X i))))) =
        conjKey n w LR TR nb base.toList (G l) (GI l) (nfX nb (X i)) :=
    fun i hi l hl' => (conjKey_eq hb hp hl (hv i hi) (hgl l hl').1 (hgl l hl').2 (hG l hl')).symm
  have hgr : ∀ l < gens.size, ∀ y < n, (gens[l]!)[y]! < n ∧ (gensInv[l]!)[y]! < n := by
    intro l hl' y hy
    obtain ⟨R1, R2⟩ := rep_permOfArr (isInvA_unpack (hG l hl'))
    rw [(hgl l hl').1, (hgl l hl').2]
    exact ⟨R1.lt hy, R2.lt hy⟩
  have hRI : ∀ x ∈ baseImgs base.toList (RP.map (unpack n w)), x < n := by
    intro x hx
    obtain ⟨b, hm, rfl⟩ := List.mem_map.1 hx
    have := (evRK_eq (range_of_canonL hRP) b (hbn b hm))
    rw [← this.1]
    exact this.2
  have hkr : imgKey n (baseImgs base.toList (RP.map (unpack n w))) =
      nfKey n w LR TR nb base.toList (nfX nb (X 0)) := by
    rw [← wordKey_eq hRP hbn]
    exact (Nat.eq_of_beq_eq_true hk0).symm
  have hP0 : parNF nb (X 0) = 0 ∧ labNF nb (X 0) = 0 := by
    unfold startNF at hst
    rw [bAnd_iff, bAnd_iff, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at hst
    exact hst.2
  exact ClR.closure_replay (T := fun i => nfArr nb (nfX nb (X i)))
    (P := fun i => parNF nb (X i)) (Lb := fun i => labNF nb (X i))
    (K := fun i => nfKey n w LR TR nb base.toList (nfX nb (X i)))
    (KS := fun h l => conjKey n w LR TR nb base.toList (G l) (GI l) (nfX nb (X h)))
    (pos := posW W) (f := fun h l cur => stepNF n w LR TR TRI nb base.toList G GI X W c h l cur)
    (fl := failC) (M := nS * R) (H := H) (C := C)
    hLv hbn hgr hRI hc0 hcap hcS (by rw [failC_eq]; omega) hC0 hCN (slices_of_groups hrun)
    (fun h l _ => stepNF_fail) hTok hκ hsk
    (fun a ha b hb' e => List.inj_on_of_nodup_map hD (List.mem_range.2 ha) (List.mem_range.2 hb') e)
    hkr hP0.1 hP0.2 (fun h l cur _ hne => stepNF_spec hne)

end CFSG.KS.SporSch.ClP

end
