module

public import CFSG.Quasithin.Vol2.KGFactC31FrameSound
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermKit

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native
open scoped Matrix

variable {n : ℕ}

@[expose] def rowBit (rows : List ℕ) (i p : ℕ) : ZMod 2 := if (rows.getD i 0).testBit p then 1 else 0

@[expose] def mbit (m i : ℕ) : ZMod 2 := ((m / 2 ^ i % 2 : ℕ) : ZMod 2)

@[expose] def vmask3 (v : Fin 3 → ZMod 2) : ℕ := (v 0).val + 2 * (v 1).val + 4 * (v 2).val

theorem ind_xor (a b : Bool) :
    (if xor a b then (1 : ZMod 2) else 0) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem ind_bsum : ∀ (rows : List ℕ) (m p : ℕ),
    (if bsum rows m p then (1 : ZMod 2) else 0) =
      ∑ i ∈ Finset.range rows.length, mbit m i * rowBit rows i p
  | [], m, p => by simp [bsum]
  | r :: rs, m, p => by
    rw [bsum, ind_xor, ind_bsum rs (m / 2) p, List.length_cons, Finset.sum_range_succ', add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [mbit, rowBit, List.getD_cons_succ, pow_succ, Nat.div_div_eq_div_mul]
      rw [mul_comm (2 ^ i) 2]
    · simp only [mbit, rowBit, pow_zero, Nat.div_one, List.getD_cons_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> cases r.testBit p <;> simp [h]

theorem sum_maskVec_eq_ind_bsum {rows : List ℕ} {k : ℕ} (hrows : rows.length = k) (m p : ℕ) :
    ∑ i : Fin k, maskVec k m i * rowBit rows i p = if bsum rows m p then (1 : ZMod 2) else 0 := by
  rw [ind_bsum, hrows]
  exact Fin.sum_univ_eq_sum_range (fun i => mbit m i * rowBit rows i p) k

theorem dot3_spec {d q : ℕ} (hd : d < 8) (hq : q < 8) :
    (maskVec 3 d 0 * maskVec 3 q 0 + maskVec 3 d 1 * maskVec 3 q 1 +
      maskVec 3 d 2 * maskVec 3 q 2).val = if dot3 d q then 1 else 0 := by
  interval_cases d <;> interval_cases q <;> decide

theorem mtp_spec {d : Fin 3 → ℕ} (hd : ∀ k, d k < 8) {q : ℕ} (hq : q < 8) :
    vmask3 ((Matrix.of fun r k => maskVec 3 (d k) r)ᵀ *ᵥ maskVec 3 q) =
      mtp (d 0) (d 1) (d 2) q := by
  simp only [vmask3, mtp, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
    Matrix.of_apply]
  rw [dot3_spec (hd 0) hq, dot3_spec (hd 1) hq, dot3_spec (hd 2) hq]
  split_ifs <;> rfl

theorem rep_getD_of_forall₂ {k : ℕ} {v : Fin k → Perm (Fin n)} {bs : List Table}
    (h : List.Forall₂ (Rep n) bs (List.ofFn v)) (i : Fin k) : Rep n (bs.getD i #[]) (v i) := by
  have hlen : bs.length = k := by rw [h.length_eq, List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.2)]
  have h1 := (List.forall₂_iff_get.mp h).2 i (by rw [hlen]; exact i.2) (by simp)
  simpa using h1

theorem getD_spanTabs {bs : List Table} {m : ℕ} (hm : m < 2 ^ bs.length) :
    (spanTabs n bs).getD m #[] = maskProd n bs m := by
  rw [spanTabs, List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map,
    List.getElem_range]

theorem length_spanTabs (bs : List Table) : (spanTabs n bs).length = 2 ^ bs.length := by
  simp [spanTabs]

theorem exists_col_mask (hn : n < 2 ^ 32) {H : Subgroup (Perm (Fin n))} {k : ℕ} {v : Fin k → H}
    (hv : EBasis v) {bs : List Table}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn fun i => (v i : Perm (Fin n)))) {T : Table} {g : H}
    (hT : Rep n T (g : Perm (Fin n))) (hgv : g ∈ eNorm hv) (r : Fin k) :
    ∃ d < 2 ^ k, maskVec k d = (fun s => eMat hv ⟨g, hgv⟩ s r) ∧
      compEqN n T (bs.getD r #[]) ((spanTabs n bs).getD d #[]) = true := by
  obtain ⟨d, hd, hdc⟩ := exists_maskVec (fun s => eMat hv ⟨g, hgv⟩ s r)
  refine ⟨d, hd, hdc, ?_⟩
  have hbl : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  rw [getD_spanTabs (by rw [hbl]; exact hd)]
  show compEq n T (bs.getD r #[]) (maskProd n bs d) = true
  rw [compEq_iff hT (rep_getD_of_forall₂ hbs r) (rep_maskProd hn _ bs hbs d)]
  have h1 : eElt v (maskVec k d) = g * v r * g⁻¹ := by
    rw [hdc]
    have h2 : (fun s => eMat hv ⟨g, hgv⟩ s r) = eCo hv ⟨g, hgv⟩ (Pi.single r 1) := rfl
    rw [h2, eElt_eCo, eElt_single]
  have h3 := congrArg H.subtype h1
  rw [map_eElt] at h3
  rw [show (fun i => H.subtype (v i)) = fun i => (v i : Perm (Fin n)) from rfl] at h3
  rw [h3]
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]

theorem fano_entry_of_ok (hn : n < 2 ^ 32) {H : Subgroup (Perm (Fin n))} {k : ℕ}
    {w : Fin k → H} {a : Fin 3 → H} (hw : EBasis w) (ha : EBasis a) {ws as : List Table}
    (hws : List.Forall₂ (Rep n) ws (List.ofFn fun i => (w i : Perm (Fin n))))
    (has : List.Forall₂ (Rep n) as (List.ofFn fun i => (a i : Perm (Fin n))))
    {rows : List ℕ} (hrows : rows.length = k) {T : Table} {g : H}
    (hT : Rep n T (g : Perm (Fin n))) (hgW : g ∈ eNorm hw) (hgA : g ∈ eNorm ha)
    (hok : fanoEqOK n ws (spanTabs n ws) as (spanTabs n as) rows T = true)
    (j : Fin k) {q : ℕ} (hq1 : 1 ≤ q) (hq8 : q < 8) :
    ∑ i : Fin k, eMat hw ⟨g, hgW⟩ i j * rowBit rows i q =
      rowBit rows j (vmask3 ((eMat ha ⟨g, hgA⟩)ᵀ *ᵥ maskVec 3 q)) := by
  have hwl : ws.length = k := by rw [hws.length_eq, List.length_ofFn]
  have hal : as.length = 3 := by rw [has.length_eq, List.length_ofFn]
  obtain ⟨d0, hd0, hd0c, hc0⟩ := exists_col_mask hn ha has hT hgA 0
  obtain ⟨d1, hd1, hd1c, hc1⟩ := exists_col_mask hn ha has hT hgA 1
  obtain ⟨d2, hd2, hd2c, hc2⟩ := exists_col_mask hn ha has hT hgA 2
  obtain ⟨m, hm, hmc, hcm⟩ := exists_col_mask hn hw hws hT hgW j
  have hb : ∀ {b c : Bool}, (!b || c) = true → b = true → c = true := by
    intro b c h hb'
    simpa [hb'] using h
  unfold fanoEqOK at hok
  rw [allIn_eq_true] at hok
  have h0 := hb (hok d0 (Nat.zero_le _) (by rw [length_spanTabs, hal]; exact hd0)) hc0
  rw [allIn_eq_true] at h0
  have h1 := hb (h0 d1 (Nat.zero_le _) (by rw [length_spanTabs, hal]; exact hd1)) hc1
  rw [allIn_eq_true] at h1
  have h2 := hb (h1 d2 (Nat.zero_le _) (by rw [length_spanTabs, hal]; exact hd2)) hc2
  rw [allIn_eq_true] at h2
  have h3 := h2 j (Nat.zero_le _) (by rw [hwl]; exact j.2)
  rw [allIn_eq_true] at h3
  have h4 := hb (h3 m (Nat.zero_le _) (by rw [length_spanTabs, hwl]; exact hm)) hcm
  rw [allIn_eq_true] at h4
  have h5 := h4 q hq1 hq8
  rw [beq_iff_eq] at h5
  have hM : eMat ha ⟨g, hgA⟩ = Matrix.of fun r s => maskVec 3 (![d0, d1, d2] s) r := by
    ext r s
    fin_cases s
    · exact (congrFun hd0c r).symm
    · exact (congrFun hd1c r).symm
    · exact (congrFun hd2c r).symm
  have hcol : ∀ i, eMat hw ⟨g, hgW⟩ i j = maskVec k m i := fun i => (congrFun hmc i).symm
  simp only [hcol]
  rw [sum_maskVec_eq_ind_bsum hrows, hM,
    mtp_spec (d := ![d0, d1, d2]) (fun s => by fin_cases s <;> assumption) hq8]
  simp only [rowBit, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [h5]

theorem eq_or_eq_of_irrOK (hn : n < 2 ^ 32) {H : Subgroup (Perm (Fin n))} {k l : ℕ}
    {u : Fin k → H} {w : Fin l → H} (hu : EBasis u) (hw : EBasis w) {us ws : List Table}
    (hus : List.Forall₂ (Rep n) us (List.ofFn fun i => (u i : Perm (Fin n))))
    (hws : List.Forall₂ (Rep n) ws (List.ofFn fun i => (w i : Perm (Fin n))))
    {m : ℕ} {xT xiT : Table} {x : H} (hx : Rep n xT (x : Perm (Fin n)))
    (hxi : Rep n xiT (x : Perm (Fin n))⁻¹) (hirr : irrOK n m xT xiT us ws = true)
    {V : Subgroup H} (hUV : eSub hu ≤ V) (hVW : V ≤ eSub hw)
    (hxV : x ∈ Subgroup.normalizer (V : Set H)) : V = eSub hu ∨ V = eSub hw := by
  by_cases hle : V ≤ eSub hu
  · exact Or.inl (le_antisymm hle hUV)
  right
  obtain ⟨v, hvV, hvU⟩ := SetLike.not_le_iff_exists.mp hle
  refine le_antisymm hVW ?_
  obtain ⟨c, hc⟩ := (mem_eSub_iff hw v).mp (hVW hvV)
  obtain ⟨mask, hmask, rfl⟩ := exists_maskVec c
  have hwl : ws.length = l := by rw [hws.length_eq, List.length_ofFn]
  have hT : Rep n (maskProd n ws mask) (v : Perm (Fin n)) := by
    have h1 := rep_maskProd hn _ ws hws mask
    have h2 := congrArg H.subtype hc
    rw [map_eElt] at h2
    rw [show (fun i => H.subtype (w i)) = fun i => (w i : Perm (Fin n)) from rfl] at h2
    rwa [h2] at h1
  unfold irrOK at hirr
  rw [List.all_eq_true] at hirr
  have h1 := hirr _ (List.mem_map.mpr ⟨mask, List.mem_range.mpr (by rw [hwl]; exact hmask), rfl⟩)
  have hnot : inSp n (spanTabs n us) (maskProd n ws mask) = false := by
    by_contra hne
    rw [Bool.not_eq_false] at hne
    obtain ⟨c', hc'⟩ := (mem_spanTabs_iff hn hus (f := fun U => tblEq n U (maskProd n ws mask))
      (P := fun g => g = (v : Perm (Fin n)))
      (fun U g hU => tblEq_iff_eq hU hT)).mp hne
    apply hvU
    have h2 : H.subtype (eElt u c') = v := by
      rw [map_eElt]
      exact hc'
    rw [← (Subtype.val_injective h2 : eElt u c' = v)]
    exact eElt_mem hu c'
  rw [hnot, Bool.false_or, List.all_eq_true] at h1
  rw [eSub_eq_closure hw, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hL := forall₂_frame (m := m) hn hx hxi hT hus
  set gl := (List.ofFn fun i => (u i : Perm (Fin n))) ++ orbList m (x : Perm (Fin n)) v
    with hgl
  have hL' : List.Forall₂ (Rep n) (us ++ orbTabs n m xT xiT (maskProd n ws mask))
      (List.ofFn gl.get) := by rwa [List.ofFn_get]
  have hwi := rep_getD_of_forall₂ hws i
  have h2 := h1 (ws.getD i #[]) (by
    rw [List.getD_eq_getElem _ _ (by rw [hwl]; exact i.2)]
    exact List.getElem_mem _)
  obtain ⟨c', hc'⟩ := (mem_spanTabs_iff hn hL' (f := fun U => tblEq n U (ws.getD i #[]))
    (P := fun g => g = (w i : Perm (Fin n))) (fun U g hU => tblEq_iff_eq hU hwi)).mp h2
  have hmem : eElt gl.get c' ∈ V.map H.subtype := by
    refine eElt_mem_of_forall _ c' _ fun j => ?_
    have hj : gl.get j ∈ (List.ofFn fun i => (u i : Perm (Fin n))) ++
        orbList m (x : Perm (Fin n)) v := List.get_mem gl j
    rw [List.mem_append] at hj
    rcases hj with hj | hj
    · obtain ⟨i', hi'⟩ := List.mem_ofFn.mp hj
      rw [← hi']
      exact ⟨u i', hUV (mem_eSub hu i'), rfl⟩
    · unfold orbList at hj
      obtain ⟨e, -, he⟩ := List.mem_map.mp hj
      rw [← he]
      refine ⟨x ^ e * v * x⁻¹ ^ e, ?_, by simp⟩
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxV e) v).mp hvV
  rw [hc'] at hmem
  obtain ⟨y, hy, hyw⟩ := hmem
  rwa [Subtype.val_injective hyw] at hy

theorem sum_map_le_of_forall₂ {α β : Type*} {S : α → β → Prop} {u : α → ℕ} {v : β → ℕ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ S l m → (∀ a b, S a b → v b ≤ u a) →
      (m.map v).sum ≤ (l.map u).sum
  | [], [], .nil, _ => le_rfl
  | a :: l, b :: m, .cons hab hlm, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a b hab) (sum_map_le_of_forall₂ hlm h)

theorem countP_le_countProducts {f : Table → Bool} {P : Perm (Fin n) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep n T g → P g → f T = true) :
    ∀ {Tss : List (List Table)} {Gss : List (List (Perm (Fin n)))},
      List.Forall₂ (List.Forall₂ (Rep n)) Tss Gss → ∀ {gT : Table} {g : Perm (Fin n)},
        Rep n gT g →
          ((products Gss).map (g * ·)).countP (fun h => decide (P h)) ≤ countProducts n f Tss gT
  | [], [], .nil, gT, g, hg => by
    simp only [countProducts, products, List.map_cons, List.map_nil, mul_one]
    by_cases hP : P g
    · simp [hP, hfP gT g hg hP]
    · simp [hP]
  | T :: Ts, Gs :: Gss, .cons hT hTs, gT, g, hg => by
    rw [countProducts, foldl_add_eq_sum, zero_add, products_map_mul, List.countP_flatMap]
    exact sum_map_le_of_forall₂ hT fun t x htx => countP_le_countProducts hfP hTs (Rep.compT hg htx)

theorem forall_of_countProducts_eq_zero' (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hfP : ∀ T g, Rep n T g → P g → f T = true)
    (h : countProducts n f (levelTables Q) (idT n) = 0) : ∀ x : Q.originalSubgroup, ¬ P x := by
  classical
  intro x hx
  have h1 := countP_le_countProducts hfP (forall₂_levelTables hn Q) (Rep.idT hn)
  rw [h, Nat.le_zero, List.countP_eq_zero] at h1
  have hmem : (x : Perm (Fin n)) ∈ (products ((List.finRange Q.baseCount).map
      (levelTransversals Q))).map ((1 : Perm (Fin n)) * ·) := by
    simp only [one_mul, List.map_id']
    exact (mem_enumeration_iff Q hQ x).mpr x.2
  exact h1 _ hmem (decide_eq_true hx)

theorem forall_of_tests_count' (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {tests : List (Table → Bool)}
    (h : countProducts n (anyTest tests) (levelTables Q) (idT n) = 0)
    {t : Table → Bool} (ht : t ∈ tests) {P : Perm (Fin n) → Prop}
    (htP : ∀ T g, Rep n T g → P g → t T = true) : ∀ x : Q.originalSubgroup, ¬ P x :=
  forall_of_countProducts_eq_zero' hn Q hQ (f := anyTest tests)
    (fun T g hT hP => List.any_eq_true.mpr ⟨t, ht, htP T g hT hP⟩) h

@[expose] noncomputable def permBk (n k : ℕ) (bs : List Table) : Fin k → Perm (Fin n) :=
  fun i => tabPerm n (bs.getD i #[])

theorem forall₂_permBk {bs : List Table} (h : tabsOK n bs = true) {k : ℕ} (hk : bs.length = k) :
    List.Forall₂ (Rep n) bs (List.ofFn (permBk n k bs)) := by
  subst hk
  have h1 : permBk n bs.length bs = permB n bs := funext fun i => by
    unfold permBk permB
    rw [List.getD_eq_getElem _ _ i.2]
    rfl
  rw [h1]
  exact forall₂_permB h

theorem ebasis_permBk (hn : n < 2 ^ 32) {bs : List Table} (h1 : tabsOK n bs = true)
    (h2 : ebasisOK n bs = true) {k : ℕ} (hk : bs.length = k) : EBasis (permBk n k bs) :=
  ebasis_of_ebasisOK hn (forall₂_permBk h1 hk) h2

theorem closure_map_tabPerm_k {bs : List Table} {k : ℕ} (hk : bs.length = k)
    (hb : EBasis (permBk n k bs)) :
    Subgroup.closure {g | g ∈ bs.map (tabPerm n)} = eSub hb := by
  subst hk
  rw [eSub_eq_closure hb]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    exact ⟨⟨i, hi⟩, by unfold permBk; rw [List.getD_eq_getElem _ _ hi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.getElem_mem i.2, by unfold permBk; rw [List.getD_eq_getElem _ _ i.2]⟩

theorem eq_eSub_of_map_eq_closure' {H : Subgroup (Perm (Fin n))} {U : Subgroup H} {k : ℕ}
    {v : Fin k → Perm (Fin n)} (hv : EBasis v) {S : Set (Perm (Fin n))}
    (hcl : Subgroup.closure S = eSub hv) (h : U.map H.subtype = Subgroup.closure S) :
    ∃ hvH : ∀ i, v i ∈ H, U = eSub (liftB_basis hvH hv) := by
  rw [hcl] at h
  have hvH : ∀ i, v i ∈ H := fun i => by
    have h1 : v i ∈ U.map H.subtype := by rw [h]; exact mem_eSub hv i
    obtain ⟨x, -, hx⟩ := h1
    rw [← hx]
    exact x.2
  refine ⟨hvH, Subgroup.map_injective H.subtype_injective ?_⟩
  rw [h, eSub_liftB_map hvH hv]

end CFSG.SectionRank.QTK.Insp443.PermKit

end
