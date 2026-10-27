module

public import Certificates.Data.Kernel.SporSch.MCountC
public import CFSG.Certificates.Kernel.Spor.M11Sound
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Sporadic.Schreier.CountSpec
import CFSG.Certificates.Kernel.Spor.PK.MCnt
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Spor.PK.MBase

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.Raw CFSG.KS.Prim

section McHelpers

open CFSG.KS.PK

private theorem mcc_sum_ite_eq_countP {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p] :
    (L.map fun x => if p x then 1 else 0).sum = L.countP fun x => decide (p x) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a <;> simp [h, Nat.add_comm]

private theorem mcc_products_nil {M : Type*} [Monoid M] :
    products ([] : List (List M)) = [1] := rfl

private theorem mcc_ite_succ (c : Prop) [Decidable c] (s : ℕ) :
    (if c then Nat.succ s else s) = s + (if c then 1 else 0) := by
  by_cases hc : c <;> simp [hc]

private theorem mcc_commC_iff {n w : ℕ} {D : ℕ → ℕ} {k : ℕ} (g : ℕ → ℕ) :
    commC n w (mask w) D k g = true ↔
      ∀ j < k, ∀ x < n, Nat.beq (g (pg w (mask w) (D j) x)) (pg w (mask w) (D j) (g x)) = true := by
  unfold commC
  rw [allFrom_iff]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  simp only [strictB_eq]
  rw [allFrom_iff]
  simp

private theorem mcc_commC_congr {n w m : ℕ} {D : ℕ → ℕ} {k : ℕ} {g g' : ℕ → ℕ}
    (hD : ∀ j < k, ∀ x < n, pg w m (D j) x < n) (h : ∀ y < n, g y = g' y) :
    commC n w m D k g = commC n w m D k g' := by
  unfold commC
  refine allFrom_congr fun j hj => ?_
  simp only [strictB_eq]
  refine allFrom_congr fun x hx => ?_
  rw [h _ (hD j hj x hx), h x hx]

private theorem mcc_pg_lt {n w p : ℕ} (h : canonK n w (mask w) (n * w) p = true) {x : ℕ}
    (hx : x < n) : pg w (mask w) p x < n := by
  unfold canonK at h
  simp only [bAnd_eq, Bool.and_eq_true, allN_iff, Nat.blt_eq, decide_eq_true_eq] at h
  exact h.2.2 x hx

private theorem mcc_idx_cfn {n : ℕ} (g : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) :
    CFSG.Sporadic.Th.idx n g i = cfn g i := by
  rw [CFSG.Sporadic.Th.idx_of_lt g hi]
  unfold cfn
  rw [dif_pos hi]
  rfl

private theorem mcc_ap_compT {n : ℕ} (P Q : CFSG.Sporadic.Th.Native.Table) {i : ℕ} (hi : i < n) :
    CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.Th.Native.compT n P Q) i =
      CFSG.Sporadic.Th.Native.ap P (CFSG.Sporadic.Th.Native.ap Q i) := by
  unfold CFSG.Sporadic.Th.Native.compT
  rw [CFSG.Sporadic.Th.ap_ofFn _ hi]
  rfl

private theorem mcc_ap_packed {n w P i : ℕ} (hn : n < 2 ^ 16) (hi : i < n)
    (hlt : pg w (mask w) P i < n) :
    CFSG.Sporadic.Th.Native.ap ((unpack n w P).map UInt32.ofNat) i = pg w (mask w) P i := by
  have hsz : i < ((unpack n w P).map UInt32.ofNat).size := by simpa [unpack] using hi
  have hlt' : pg w (mask w) P i < UInt32.size := by
    unfold UInt32.size
    have : (2 : ℕ) ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  unfold CFSG.Sporadic.Th.Native.ap
  rw [getElem!_pos ((unpack n w P).map UInt32.ofNat) i hsz, Array.getElem_map]
  unfold unpack
  rw [Array.getElem_ofFn, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt']

private theorem mcc_lastC_eq (n w m nw pm : ℕ) (D : ℕ → ℕ) (k L3 L4 h s : ℕ) :
    lastC n w m nw pm D k L3 L4 h s = s + ((List.range (lcnt L3)).map fun k3 =>
      ((List.range (lcnt L4)).map fun k4 => if commC n w m D k
        (raw3 w m h (ltr nw pm L3 k3) (ltr nw pm L4 k4)) = true then 1 else 0).sum).sum := by
  unfold lastC
  simp only [strictN_eq, nIf_eq]
  rw [foldUp_add]
  · refine congrArg (s + ·) (congrArg List.sum (List.map_congr_left fun k3 _ => ?_))
    rw [foldUp_add, Nat.zero_add]
    · rfl
    · intro k4 s'
      exact mcc_ite_succ _ s'
  · intro k3 s'
    rw [foldUp_add, foldUp_add, Nat.zero_add]
    · intro k4 s''
      exact mcc_ite_succ _ s''
    · intro k4 s''
      exact mcc_ite_succ _ s''

private theorem mcc_sliceC_eq (n w m nw pm : ℕ) (D : ℕ → ℕ) (k L0 L1 L2 L3 L4 sub i : ℕ) :
    sliceC n w m nw pm D k L0 L1 L2 L3 L4 sub i =
      ((List.range (lcnt L1 / sub)).map fun j => ((List.range (lcnt L2)).map fun k2 =>
        lastC n w m nw pm D k L3 L4 (pcomp n w m (pcomp n w m (ltr nw pm L0 (i / sub))
          (ltr nw pm L1 (lcnt L1 / sub * (i % sub) + j))) (ltr nw pm L2 k2)) 0).sum).sum := by
  have hl : ∀ h s, lastC n w m nw pm D k L3 L4 h s = s + lastC n w m nw pm D k L3 L4 h 0 :=
    fun h s => by
      rw [mcc_lastC_eq n w m nw pm D k L3 L4 h s, mcc_lastC_eq n w m nw pm D k L3 L4 h 0,
        Nat.zero_add]
  unfold sliceC
  simp only [strictN_eq]
  rw [foldUp_add, Nat.zero_add]
  · refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [foldUp_add, Nat.zero_add]
    · rfl
    · intro k2 s
      exact hl _ s
  · intro j s
    rw [foldUp_add, foldUp_add, Nat.zero_add]
    · intro k2 s
      exact hl _ s
    · intro k2 s
      exact hl _ s

private theorem mcc_sliceC_five {n w : ℕ} {F : ℕ → ℕ → ℕ} {s : ℕ → BS} {V : ℕ → ℕ}
    (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hg : ∀ i, GoodBS n F (s i)) (D : ℕ → ℕ)
    (k sub i : ℕ) :
    sliceC n w (mask w) (n * w) (mask (n * w)) D k (recBS n w F (s 0) (V 0))
        (recBS n w F (s 1) (V 1)) (recBS n w F (s 2) (V 2)) (recBS n w F (s 3) (V 3))
        (recBS n w F (s 4) (V 4)) sub i =
      rsum ((s 1).pts.length / sub) fun j => rsum (s 2).pts.length fun k2 =>
        rsum (s 3).pts.length fun k3 => rsum (s 4).pts.length fun k4 =>
          if commC n w (mask w) D k (raw5 n w F s V (i / sub)
            ((s 1).pts.length / sub * (i % sub) + j) k2 k3 k4) = true then 1 else 0 := by
  rw [mcc_sliceC_eq]
  simp only [mcc_lastC_eq, Nat.zero_add, lcnt_recBS hn16 hw (hg _)]
  rfl

private theorem mcc_allLt_iff {n : ℕ} {p : ℕ → Bool} :
    CFSG.Monster.B.Co2.Native.allLt n p = true ↔ ∀ i < n, p i = true :=
  CFSG.Monster.B.Co2.allLt_iff

private theorem mcc_test_iff {n w K : ℕ} (hn16 : n < 2 ^ 16) {D : ℕ → ℕ}
    {Ds : Array (Array ℕ)} (hDs : Ds.size = K ∧ ∀ j < K, Ds[j]! = unpack n w (D j))
    (hD : ∀ j < K, canonK n w (mask w) (n * w) (D j) = true)
    (T : CFSG.Sporadic.Th.Native.Table) (g : Equiv.Perm (Fin n))
    (hT : CFSG.Sporadic.Th.Rep n T g) :
    (CFSG.Monster.B.Co2.Native.allLt K fun j => CFSG.Monster.B.Co2.Native.allLt n fun i =>
      CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.Th.Native.compT n T (Ds[j]!.map UInt32.ofNat)) i ==
        CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.Th.Native.compT n (Ds[j]!.map UInt32.ofNat) T)
          i) = true ↔ commC n w (mask w) D K (cfn g) = true := by
  rw [mcc_commC_iff]
  have hpt : ∀ j < K, ∀ i < n,
      (CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.Th.Native.compT n T (Ds[j]!.map UInt32.ofNat)) i ==
        CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.Th.Native.compT n (Ds[j]!.map UInt32.ofNat) T)
          i) = true ↔
        Nat.beq (cfn g (pg w (mask w) (D j) i)) (pg w (mask w) (D j) (cfn g i)) = true := by
    intro j hj i hi
    have hd := mcc_pg_lt (hD j hj) hi
    have hgi := cfn_lt g hi
    have hdi := mcc_pg_lt (hD j hj) hgi
    rw [mcc_ap_compT _ _ hi, mcc_ap_compT _ _ hi, hDs.2 j hj, mcc_ap_packed hn16 hi hd,
      hT _ hd, mcc_idx_cfn g hd, hT i hi, mcc_idx_cfn g hi, mcc_ap_packed hn16 hgi hdi]
    simp
  simp only [mcc_allLt_iff]
  exact ⟨fun h j hj i hi => (hpt j hj i hi).1 (h j hj i hi),
    fun h j hj i hi => (hpt j hj i hi).2 (h j hj i hi)⟩

private theorem mcc_chain_sum {n w K sub : ℕ} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    {D : ℕ → ℕ} (hD : ∀ j < K, ∀ x < n, pg w (mask w) (D j) x < n)
    {F : ℕ → ℕ → ℕ} {s : ℕ → BS} {V : ℕ → ℕ}
    (hg : ∀ i, GoodBS n F (s i)) (hsub : 0 < sub ∧ (s 1).pts.length % sub = 0)
    {E : List (Equiv.Perm (Fin n))}
    (hperm : E.Perm (products ((List.range 5).map fun i =>
      (List.range (s i).pts.length).map (tau n F s i))))
    {CS : List ℕ} (hCS : CS.length = (s 0).pts.length * sub)
    (hc : ∀ i < (s 0).pts.length * sub, sliceC n w (mask w) (n * w) (mask (n * w)) D K
      (recBS n w F (s 0) (V 0)) (recBS n w F (s 1) (V 1)) (recBS n w F (s 2) (V 2))
      (recBS n w F (s 3) (V 3)) (recBS n w F (s 4) (V 4)) sub i = CS.getD i 0) :
    (E.map fun σ => if commC n w (mask w) D K (cfn σ) = true then 1 else 0).sum = CS.sum := by
  have hq : (s 1).pts.length / sub * sub = (s 1).pts.length :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hsub.2)
  have hsC : ∀ i < (s 0).pts.length * sub, CS.getD i 0 =
      rsum ((s 1).pts.length / sub) fun j => rsum (s 2).pts.length fun k2 =>
        rsum (s 3).pts.length fun k3 => rsum (s 4).pts.length fun k4 =>
          if commC n w (mask w) D K (raw5 n w F s V (i / sub)
            ((s 1).pts.length / sub * (i % sub) + j) k2 k3 k4) = true then 1 else 0 :=
    fun i hi => (hc i hi).symm.trans (mcc_sliceC_five hn16 hw hg D K sub i)
  have hCSsum : CS.sum = rsum ((s 0).pts.length * sub) fun i => CS.getD i 0 := by
    rw [← hCS]
    simpa using sum_map_eq_rsum CS (fun x => x) 0
  have hL5 : (List.range 5).map (fun i => (List.range (s i).pts.length).map (tau n F s i)) =
      [(List.range (s 0).pts.length).map (tau n F s 0),
        (List.range (s 1).pts.length).map (tau n F s 1),
        (List.range (s 2).pts.length).map (tau n F s 2),
        (List.range (s 3).pts.length).map (tau n F s 3),
        (List.range (s 4).pts.length).map (tau n F s 4)] := rfl
  rw [(hperm.map fun σ => if commC n w (mask w) D K (cfn σ) = true then 1 else 0).sum_eq,
    hCSsum, rsum_congr hsC, rsum_slices ((s 0).pts.length) sub ((s 1).pts.length / sub)
      (fun k0 k1 => rsum (s 2).pts.length fun k2 => rsum (s 3).pts.length fun k3 =>
        rsum (s 4).pts.length fun k4 =>
          if commC n w (mask w) D K (raw5 n w F s V k0 k1 k2 k3 k4) = true then 1 else 0),
    hq, hL5]
  simp only [sum_products_cons, mcc_products_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  refine rsum_congr fun k0 h0 => rsum_congr fun k1 h1 => rsum_congr fun k2 h2 =>
    rsum_congr fun k3 h3 => rsum_congr fun k4 h4 => ?_
  rw [mcc_commC_congr hD (fun y hy => (raw5_eq hn16 hw hg h0 h1 h2 h3 h4 y hy).symm)]

end McHelpers

theorem mCntC_sound {n w k K : ℕ} {gA gB : Equiv.Perm (Fin n)} {words : List (List Int)}
    {hn : 1 ≤ n} {bv : Vector (Fin n) k} {hbs : bv.toList.Nodup}
    {tA tB : List ℕ} {W : List (List Int)} {bs sz : List ℕ} {NW sub : ℕ}
    {D : ℕ → ℕ} {Ds : Array (Array ℕ)} {CS : List ℕ}
    (hA : tA = imageList gA) (hB : tB = imageList gB)
    (hW : W = [[1], [2]] ++ words.map (List.map shiftLabel))
    (hbsv : bs = bv.toList.map Fin.val) (hNW : NW = words.length + 2) (hn16 : n < 2 ^ 16)
    (hbase : mBase n w bs sz NW tA tB W = true) (h5 : sz.length = 5)
    (hsub : 0 < sub ∧ sz.getD 1 0 % sub = 0)
    (hDs : Ds.size = K ∧ ∀ j < K, Ds[j]! = unpack n w (D j))
    (hD : ∀ j < K, canonK n w (mask w) (n * w) (D j) = true)
    (hCS : CS.length = sz.headD 0 * sub)
    (hc : ∀ i < sz.headD 0 * sub, mCntC n w bs NW tA tB W sub i D K = CS.getD i 0) :
    countProducts n (fun T => CFSG.Monster.B.Co2.Native.allLt K fun j =>
        CFSG.Monster.B.Co2.Native.allLt n fun i =>
        ap (compT n T (Ds[j]!.map UInt32.ofNat)) i == ap (compT n (Ds[j]!.map UInt32.ofNat) T) i)
      (levelTables (certificate hn [gA, gB] words bv hbs)) (idT n) = CS.sum := by
  obtain ⟨hn24, hw, hbsl⟩ := CFSG.KS.PK.mBase_facts hbase
  obtain ⟨-, hperm, hszs, hL⟩ := CFSG.KS.PK.mBase_chain (sh := shiftLabel) (hn := hn)
    (bv := bv) (hbs := hbs) (fun _ => rfl) hA hB hW hbsv hNW hn16 hbase
  have hn32 : n < 2 ^ 32 := by
    have : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  set F := CFSG.KS.PK.mbF n w tA tB W with hFdef
  set NL := NW + NW with hNLdef
  set sS : Nat → CFSG.KS.PK.BS := CFSG.KS.PK.mbS n F NL bs with hsSdef
  set V : Nat → Nat := fun i => CFSG.KS.PK.levMaskAt n w (CFSG.KS.MEnum.mLT n w tA tB W) NL bs i
    with hVdef
  have hk : k = 5 := by
    have := congrArg List.length hszs
    simpa [h5] using this
  subst hk
  have hsz5 : sz = [(sS 0).pts.length, (sS 1).pts.length, (sS 2).pts.length,
      (sS 3).pts.length, (sS 4).pts.length] := hszs.symm
  have hbl : bs.length = 5 := by rw [hbsv]; simp
  have hgood : ∀ i, CFSG.KS.PK.GoodBS n F (sS i) := fun i => by
    refine CFSG.KS.PK.goodBS_run ?_ (fun l hl => hL l (CFSG.KS.PK.lvAt_sub _ _ _ _ l hl))
    by_cases hi : i < bs.length
    · exact hbsl _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact hn
  have hmc : ∀ i, mCntC n w bs NW tA tB W sub i D K =
      sliceC n w (mask w) (n * w) (mask (n * w)) D K
        (CFSG.KS.PK.recBS n w F (sS 0) (V 0)) (CFSG.KS.PK.recBS n w F (sS 1) (V 1))
        (CFSG.KS.PK.recBS n w F (sS 2) (V 2)) (CFSG.KS.PK.recBS n w F (sS 3) (V 3))
        (CFSG.KS.PK.recBS n w F (sS 4) (V 4)) sub i := by
    intro i
    unfold mCntC
    simp only [CFSG.KS.PK.strictN_eq, Nat.mul_eq, Nat.add_eq]
    rw [CFSG.KS.PK.levN_eq hn16 hw hL hbsl, CFSG.KS.PK.levPairs_eq, List.map_map, hbl]
    rfl
  have hc' : ∀ i < (sS 0).pts.length * sub,
      sliceC n w (mask w) (n * w) (mask (n * w)) D K
        (CFSG.KS.PK.recBS n w F (sS 0) (V 0)) (CFSG.KS.PK.recBS n w F (sS 1) (V 1))
        (CFSG.KS.PK.recBS n w F (sS 2) (V 2)) (CFSG.KS.PK.recBS n w F (sS 3) (V 3))
        (CFSG.KS.PK.recBS n w F (sS 4) (V 4)) sub i = CS.getD i 0 := by
    intro i hi
    rw [← hmc i]
    exact hc i (by rw [hsz5]; exact hi)
  have hsub' : 0 < sub ∧ (sS 1).pts.length % sub = 0 := by
    rw [hsz5] at hsub
    exact hsub
  have hCS' : CS.length = (sS 0).pts.length * sub := by
    rw [hsz5] at hCS
    exact hCS
  have hid : CFSG.Sporadic.Th.Rep n (idT n) (1 : Equiv.Perm (Fin n)) :=
    CFSG.Sporadic.Th.Rep.idT hn32
  rw [countProducts_spec (fun T g hT => mcc_test_iff hn16 hDs hD T g hT)
    (forall₂_levelTables hn32 (certificate hn [gA, gB] words bv hbs)) hid]
  simp only [one_mul, List.map_id']
  rw [← mcc_sum_ite_eq_countP]
  exact mcc_chain_sum hn16 hw (fun j hj x hx => mcc_pg_lt (hD j hj) hx) hgood hsub' hperm hCS' hc'

end CFSG.KS.SporSch

end
