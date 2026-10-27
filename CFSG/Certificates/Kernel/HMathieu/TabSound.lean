module

public import Certificates.Data.Kernel.HMathieu.Tab
public import CFSG.Certificates.Kernel.HMathieu.BfsSound
public import CFSG.Certificates.Kernel.HMathieu.GreedySound
public import CFSG.Quasithin.Background.HMathieuMask
import CFSG.Certificates.Kernel.Spor.PinvSSound

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

structure Packed (T : PT 24) (E : List Nat) : Prop where
  elems : T.elems = (E.map unpk).toArray
  one : T.one = 0
  vp : ∀ p ∈ E, vpK p = true

variable {T : PT 24} [hT : Fact (T.check = true)] {E : List Nat}

@[expose] def pk (E : List Nat) (p : T.Elem) : Nat := E.getD p.idx 0

theorem n_eq (H : Packed T E) : T.n = E.length := by
  rw [← PT.size_elems (T := T), H.elems]
  simp

theorem idx_lt (H : Packed T E) (p : T.Elem) : p.idx < E.length := by
  rw [← n_eq H]
  exact p.lt

theorem pk_eq (H : Packed T E) (p : T.Elem) : pk E p = E[p.idx]'(idx_lt H p) := by
  simp [pk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (idx_lt H p)]

theorem vp_pk (H : Packed T E) (p : T.Elem) : vpK (pk E p) = true := by
  rw [pk_eq H]
  exact H.vp _ (List.getElem_mem _)

theorem elems_get (H : Packed T E) {k : Nat} (hk : k < E.length) :
    T.elems[k]! = unpk (E.getD k 0) := by
  have : T.elems[k]! = (E.map unpk)[k]! := by rw [H.elems]; simp
  rw [this]
  simp [List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD, hk]

theorem arr_eq (H : Packed T E) (p : T.Elem) : T.arr p = unpk (pk E p) :=
  elems_get H (idx_lt H p)

theorem pg_pk (H : Packed T E) (p : T.Elem) {i : Nat} (hi : i < 24) :
    (T.arr p)[i]! = pg 5 (mask 5) (pk E p) i := by
  rw [arr_eq H, unpk_get _ hi]

theorem eq_of_pk (H : Packed T E) {p q : T.Elem} (h : pk E p = pk E q) : p = q := by
  by_contra hpq
  have hne : p.idx ≠ q.idx := fun e => hpq (PT.Elem.ext' e)
  obtain ⟨i, hi, hd⟩ := (PT.check_spec hT.out).2.2.2.2.2 _ p.lt _ q.lt hne
  apply hd
  have e1 : T.elems[p.idx]! = T.arr p := rfl
  have e2 : T.elems[q.idx]! = T.arr q := rfl
  rw [e1, e2, pg_pk H p hi, pg_pk H q hi, h]

theorem eq_iff (H : Packed T E) (p q : T.Elem) : p = q ↔ pk E p = pk E q :=
  ⟨fun h => h ▸ rfl, eq_of_pk H⟩

theorem pk_mul (H : Packed T E) (p q : T.Elem) : pk E (p * q) = pc24 (pk E p) (pk E q) := by
  refine eq_of_pg (vp_pk H _) (vpK_pc24 (vp_pk H p) (vp_pk H q)) fun i hi => ?_
  have hq : (T.arr q)[i]! < 24 := by
    rw [pg_pk H q hi]
    exact (vpK_spec (vp_pk H q)).2 i hi
  rw [pg_pc24 _ _ hi, ← pg_pk H _ hi, ← pg_pk H q hi, ← pg_pk H p hq]
  exact (PT.check_spec hT.out).2.2.2.2.1 _ p.lt _ q.lt _ hi

theorem pk_one (H : Packed T E) : pk E (1 : T.Elem) = E.getD 0 0 := by
  unfold pk
  rw [PT.idx_one, H.one]

theorem mul_iff (H : Packed T E) (p q r : T.Elem) :
    p * q = r ↔ pc24 (pk E p) (pk E q) = pk E r := by
  rw [eq_iff H, pk_mul H]

theorem pk_inv (H : Packed T E) (hid : E.getD 0 0 = pidn 24 5) (g : T.Elem) :
    pk E g⁻¹ = pinvS 24 5 (mask 5) (pk E g) := by
  have h1 : pc24 (pk E g) (pk E g⁻¹) = pidn 24 5 := by
    rw [← pk_mul H, mul_inv_cancel, pk_one H, hid]
  have h2 : pc24 (pk E g⁻¹) (pk E g) = pidn 24 5 := by
    rw [← pk_mul H, inv_mul_cancel, pk_one H, hid]
  have hg := vpK_spec (vp_pk H g)
  have hinj : CFSG.KS.PinvS.InjK 24 5 (pk E g) := by
    refine ⟨hg.2, fun a ha b hb e => ?_⟩
    have ea := pg_pc24 (pk E g⁻¹) (pk E g) ha
    have eb := pg_pc24 (pk E g⁻¹) (pk E g) hb
    rw [h2, pg_id ha] at ea
    rw [h2, pg_id hb] at eb
    rw [ea, eb, e]
  have hw : (24 : Nat) < 2 ^ 5 := by norm_num
  refine eq_of_pg (vp_pk H _) (vpK_of (CFSG.KS.PinvS.pinvS_shr hw hg.2)
    (CFSG.KS.PinvS.pinvS_lt hw hinj)) fun i hi => ?_
  have hj := (vpK_spec (vp_pk H g⁻¹)).2 i hi
  have e := pg_pc24 (pk E g) (pk E g⁻¹) hi
  rw [h1, pg_id hi] at e
  conv_rhs => rw [e]
  rw [CFSG.KS.PinvS.pg_pinvS hw hinj hj]

theorem map_elems_get (H : Packed T E) {β : Type} [Inhabited β] (f : Array Nat → β)
    (p : T.Elem) : (T.elems.map f)[p.idx]! = f (unpk (pk E p)) := by
  have hs : p.idx < T.elems.size := by rw [PT.size_elems]; exact p.lt
  rw [getElem!_pos _ p.idx (by simpa using hs), Array.getElem_map, ← arr_eq H p, PT.arr,
    getElem!_pos T.elems p.idx hs]

theorem permCols_unpk (p : Nat) :
    permCols (unpk p) = (List.range 24).map fun j => 2 ^ pg 5 (mask 5) p j := by
  unfold permCols
  refine List.map_congr_left fun j hj => ?_
  rw [unpk_get p (List.mem_range.1 hj)]

theorem actM_unpk (cc lift : List Nat) (p m : Nat) :
    actM cc (permM (unpk p) (actM lift m)) = actP cc lift p m := by
  unfold actP permP permM
  rw [permCols_unpk]

theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) {n : Nat} (hn : n < l.length)
    (d : β) (d' : α) : (l.map f).getD n d = f (l.getD n d') := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hn]

theorem invFrom_eq (e0 : Nat) : ∀ (L : List Nat) (i : Nat), invFrom e0 L i =
    ((List.range' i L.length).filter fun k =>
      !(Nat.beq k 0) && Nat.beq (pc24 (L.getD (k - i) 0) (L.getD (k - i) 0)) e0) := by
  intro L
  induction L with
  | nil => intro i; rfl
  | cons e L ih =>
    intro i
    rw [invFrom, List.length_cons, List.range'_succ, List.filter_cons, Nat.sub_self,
      List.getD_cons_zero, ih (i + 1)]
    have hf : ((List.range' (i + 1) L.length).filter fun k =>
        !(Nat.beq k 0) && Nat.beq (pc24 (L.getD (k - (i + 1)) 0) (L.getD (k - (i + 1)) 0)) e0) =
        ((List.range' (i + 1) L.length).filter fun k =>
        !(Nat.beq k 0) && Nat.beq (pc24 ((e :: L).getD (k - i) 0) ((e :: L).getD (k - i) 0)) e0) := by
      refine List.filter_congr fun k hk => ?_
      rw [List.mem_range'_1] at hk
      have : k - i = (k - (i + 1)) + 1 := by omega
      rw [this, List.getD_cons_succ]
    rw [hf]

theorem invols_idx (H : Packed T E) :
    T.invols.map (·.idx) = invFrom (E.getD 0 0) E 0 := by
  rw [invFrom_eq]
  simp only [Nat.sub_zero]
  rw [← List.range_eq_range', ← n_eq H]
  unfold PT.invols
  have hr : List.range T.n = ((List.finRange T.n).map T.elemEquiv.symm).map (·.idx) := by
    rw [List.map_map]
    have hm : ((fun x : T.Elem => x.idx) ∘ T.elemEquiv.symm) = fun i : Fin T.n => i.val := rfl
    rw [hm, List.map_coe_finRange_eq_range]
  rw [hr]
  conv_rhs => rw [List.filter_map]
  congr 1
  refine List.filter_congr fun p _ => ?_
  simp only [Function.comp_apply]
  have h1 : decide (p ≠ 1) = !(Nat.beq p.idx 0) := by
    have : p = 1 ↔ p.idx = 0 := by
      rw [← H.one, ← PT.idx_one]
      exact ⟨fun h => h ▸ rfl, fun h => PT.Elem.ext' h⟩
    cases h : Nat.beq p.idx 0
    · have : p.idx ≠ 0 := fun e => by rw [e] at h; exact absurd h (by decide)
      simp_all
    · have := Nat.eq_of_beq_eq_true h
      simp_all
  have h2 : (p * p == 1) = Nat.beq (pc24 (E.getD p.idx 0) (E.getD p.idx 0)) (E.getD 0 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, mul_iff H, pk_one H, Nat.beq_eq]
    rfl
  rw [h1, h2]

structure InvData (T : PT 24) [Fact (T.check = true)] (E invL P : List Nat) : Prop where
  idx : T.invols.map (·.idx) = invL
  pks : P = invL.map (fun i => E.getD i 0) ++ [E.getD 0 0]

theorem length_invols {invL P : List Nat} (I : InvData T E invL P) :
    T.invols.length = invL.length := by
  rw [← I.idx, List.length_map]

theorem pk_el (H : Packed T E) {invL P : List Nat} (I : InvData T E invL P) {k : Nat}
    (hk : k ≤ T.invols.length) : pk E (el T.invols k) = P.getD k 0 := by
  rw [I.pks]
  rcases Nat.lt_or_ge k T.invols.length with h | h
  · rw [el_of_lt h, List.getD_append _ _ _ _ (by simpa [← length_invols I] using h)]
    unfold pk
    have e : (T.invols[k]).idx = invL[k]'(by rw [← length_invols I]; exact h) := by
      simp [← I.idx]
    simp [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← length_invols I]; exact h)]
  · have hk' : k = T.invols.length := by omega
    rw [el_of_le h, pk_one H, hk', length_invols I, List.getD_append_right _ _ _ _ (by simp)]
    simp

theorem nodup_invols (T : PT 24) [Fact (T.check = true)] : T.invols.Nodup := by
  unfold PT.invols
  refine List.Nodup.filter _ (List.Nodup.map (fun a b h => ?_) (List.nodup_finRange _))
  exact T.elemEquiv.symm.injective h

theorem mem_invols_iff {x : T.Elem} : x ∈ T.invols ↔ x ≠ 1 ∧ x * x = 1 := by
  constructor
  · intro hx
    unfold PT.invols at hx
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
    exact hx.2
  · intro h
    exact PT.mem_invols h.1 h.2

theorem gtabs_of (H : Packed T E) {invL P : List Nat} (I : InvData T E invL P)
    {D : List (Nat × Nat)} (hK : tabsK invL.length P D = true) :
    GTabs T.invols (cmD D) (mkD D) := by
  have hm := length_invols I
  have hpair : ∀ i < T.invols.length, ∀ j < T.invols.length,
      pairK invL.length P (P.getD i 0) (P.getD j 0) (cmD D i) (mkD D i) j = true := by
    intro i hi j hj
    unfold tabsK at hK
    rw [List.all_eq_true] at hK
    have := hK i (List.mem_range.2 (by omega))
    rw [List.all_eq_true] at this
    exact this j (List.mem_range.2 (by omega))
  have hcomm : ∀ i < T.invols.length, ∀ j < T.invols.length,
      (el T.invols i * el T.invols j = el T.invols j * el T.invols i) ↔
        pc24 (P.getD i 0) (P.getD j 0) = pc24 (P.getD j 0) (P.getD i 0) := by
    intro i hi j hj
    rw [mul_iff H, pk_mul H, pk_el H I hi.le, pk_el H I hj.le]
  refine ⟨nodup_invols T, fun x hx => mem_invols_iff.1 hx, fun x h1 h2 => mem_invols_iff.2 ⟨h1, h2⟩,
    fun i hi j hj => ?_, fun i hi j hj hc => ?_⟩
  · have hp := hpair i hi j hj
    unfold pairK at hp
    rw [Bool.and_eq_true, beq_iff_eq] at hp
    rw [← hp.1, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, hcomm i hi j hj]
  · have hp := hpair i hi j hj
    unfold pairK at hp
    rw [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    have hb : (cmD D i).testBit j = true := by
      rw [← h1, beq_iff_eq]
      exact (hcomm i hi j hj).1 hc
    rw [hb, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at h2
    have hmk : mkF (mkD D) T.invols.length i j = Nat.land (Nat.shiftRight (mkD D i) (8 * j)) 255 := by
      rw [mkF, if_neg (Nat.ne_of_lt hi), if_neg (Nat.ne_of_lt hj)]
    rw [hmk, hm]
    refine ⟨h2.1, ?_⟩
    rw [eq_comm, mul_iff H, pk_el H I hi.le, pk_el H I hj.le, pk_el H I (by rw [hm]; exact h2.1), h2.2]

end CFSG.KC.HMathieu

end
