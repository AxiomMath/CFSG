module

public import CFSG.Certificates.Kernel.Misc.YamakiLbarSound

public section

namespace CFSG.KC.YamakiLbar

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiLbar
  CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KC.Misc.Spec Matrix
  CFSG.KD.YamakiA0
open CFSG.KD.Sp62 (MULF ONE)
open CFSG.KC.Sp62 (MULF_lt pkMat_MULF pkMat_inj)

@[expose] noncomputable def phiA (Q : ℕ → ℕ) (N : ℕ) : Array ℕ :=
  Array.ofFn (n := 64) fun k => psc Q (MULF (crd Q k) N)

variable {R Q : ℕ → ℕ}

theorem phiA_get (N : ℕ) {k : ℕ} (hk : k < 64) : (phiA Q N)[k]! = psc Q (MULF (crd Q k) N) :=
  getElem!_ofFn_nat _ hk

theorem size_phiA (N : ℕ) : (phiA Q N).size = 64 := Array.size_ofFn

theorem lt36 {c : ℕ} (hc : c < 64) : c < 2 ^ 36 := lt_of_lt_of_le hc (by norm_num)

section A0

variable (hA : a0TabK R 64 = true) (hc : coordK R Q = true)

include hA hc in
theorem compA_phiA (M M' : ℕ) : compA (phiA Q M) (phiA Q M') = phiA Q (MULF M' M) := by
  refine ext64 (size_compA _ _) (size_phiA _) fun k hk => ?_
  have h1 := vec_lt (crd_lt hA hc hk) M'
  rw [compA_get _ _ hk, phiA_get _ hk, phiA_get _ (psc_lt hA hc h1), crd_psc hA hc h1,
    phiA_get _ hk, mulF_assoc]

include hA hc in
theorem phiA_one : phiA Q ONE = idA () := by
  refine ext64 (size_phiA _) size_idA fun k hk => ?_
  rw [phiA_get _ hk, mulF_one (lt36 (crd_lt hA hc hk)), psc_crd hA hc hk, idA_get hk]

include hA hc in
theorem phiA_inj {N N' : ℕ} (hN : N < 2 ^ 36) (hN' : N' < 2 ^ 36) (h : phiA Q N = phiA Q N') :
    N = N' := by
  refine rows_ext hN hN' fun j hj => ?_
  have hp := pow_lt64 hj
  have hk := psc_lt hA hc hp
  have e : (phiA Q N)[psc Q (2 ^ j)]! = (phiA Q N')[psc Q (2 ^ j)]! := by rw [h]
  rw [phiA_get _ hk, phiA_get _ hk, crd_psc hA hc hp] at e
  have := congrArg (crd Q) e
  rwa [crd_psc hA hc (vec_lt hp _), crd_psc hA hc (vec_lt hp _)] at this

include hA hc in
theorem decide_phiA {N N' : ℕ} (hN : N < 2 ^ 36) (hN' : N' < 2 ^ 36) :
    decide (phiA Q N = phiA Q N') = Nat.beq N N' := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_eq, Nat.beq_eq]
  exact ⟨phiA_inj hA hc hN hN', fun h => by rw [h]⟩

include hA hc in
theorem phiA_zero (N : ℕ) : (phiA Q N)[0]! = 0 := by
  rw [phiA_get _ (by norm_num), (coord_facts hc).1, zero_mulF, psc_zero hA hc]

include hA hc in
theorem phiA_psc (N : ℕ) {x : ℕ} (hx : x < 64) : (phiA Q N)[psc Q x]! = psc Q (MULF x N) := by
  rw [phiA_get _ (psc_lt hA hc hx), crd_psc hA hc hx]

end A0

section Gl

variable (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hA : a0TabK R 64 = true)
  (hc : coordK R Q = true)

include hG hA hc in
theorem z6Pos_recX {k : ℕ} (hk : k < 64) : z6Pos (enumA0 ()) (arrN (recX R 12 k)) = k := by
  obtain ⟨hE, -⟩ := enumA0_inv hG hA
  have := lookup_of_inv hE hk
  unfold z6Pos enumA0
  rw [this]
  rfl

include hG hA hc in
theorem enumA0_get {k : ℕ} (hk : k < 64) : (enumA0 ()).elems[k]! = arrN (recX R 12 k) :=
  (enumA0_inv hG hA).1.2.2.2.1 k hk

include hG hA hc in
theorem z6Gl_eq (hg : glK R Q = true) {i : ℕ} (hi : i < 11) : z6Gl i = phiA Q (Q i) := by
  have hlt := (enumA0_inv hG hA).2.2.2.2
  refine ext64 Array.size_ofFn (size_phiA _) fun k hk => ?_
  unfold z6Gl
  simp only
  have hx := vec_lt (crd_lt hA hc hk) (Q i)
  have hp := psc_lt hA hc hx
  have e : MULF (MULF (R i) (recX R 12 k)) (R i) = recX R 12 (psc Q (MULF (crd Q k) (Q i))) :=
    pkMat_inj (MULF_lt _ _) (hlt _ hp) (by rw [pkMat_MULF, pkMat_MULF, conjX hA hc hg hi k hk])
  rw [getElem!_ofFn_nat _ hk, phiA_get _ hk, enumA0_get hG hA hc hk, genA_eq12 hG (by omega),
    arrN_mul, arrN_mul, e, z6Pos_recX hG hA hc hp]

include hG hA hc in
theorem z6MulTab_get {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    ((z6MulTab ())[i]!)[j]! = psc Q (crd Q i ^^^ crd Q j) := by
  have hlt := (enumA0_inv hG hA).2.2.2.2
  have hx := xor_lt64 (crd_lt hA hc hi) (crd_lt hA hc hj)
  have hp := psc_lt hA hc hx
  have e : MULF (recX R 12 i) (recX R 12 j) = recX R 12 (psc Q (crd Q i ^^^ crd Q j)) :=
    pkMat_inj (MULF_lt _ _) (hlt _ hp) (by rw [pkMat_MULF]; exact mulX hA hc j hj i hi)
  unfold z6MulTab
  simp only
  rw [getElem!_ofFn_nat _ hi, getElem!_ofFn_nat _ hj, enumA0_get hG hA hc hi,
    enumA0_get hG hA hc hj, arrN_mul, e, z6Pos_recX hG hA hc hp]

include hG hA hc in
theorem z6MulTab_psc {x y : ℕ} (hx : x < 64) (hy : y < 64) :
    ((z6MulTab ())[psc Q x]!)[psc Q y]! = psc Q (x ^^^ y) := by
  rw [z6MulTab_get hG hA hc (psc_lt hA hc hx) (psc_lt hA hc hy), crd_psc hA hc hx,
    crd_psc hA hc hy]

end Gl

theorem lb_facts (h : lbTabK Q = true) :
    lbL Q 0 = ONE ∧ Q 11 = MULF (Q 10) (Q 9) ∧
      (∀ i < 167, recF Q 140 0 i ≤ i ∧ recF Q 140 1 i < 2 ∧
        lbL Q (i + 1) = stL Q (lbL Q (recF Q 140 0 i)) (recF Q 140 1 i)) ∧
      recC Q 140 2 0 = 1 ∧ recC Q 140 2 (168 * 2) = 168 ∧
      (∀ i < 168 * 2, i / 2 < recC Q 140 2 i ∧ recPOS Q 140 2 i ≤ recC Q 140 2 i ∧
        recPOS Q 140 2 i < 168 ∧ lbL Q (recPOS Q 140 2 i) = stL Q (lbL Q (i / 2)) (i % 2) ∧
        (recPOS Q 140 2 i = recC Q 140 2 i → recC Q 140 2 (i + 1) = recC Q 140 2 i + 1 ∧
          recF Q 140 0 (recC Q 140 2 i - 1) = i / 2 ∧ recF Q 140 1 (recC Q 140 2 i - 1) = i % 2) ∧
        (recPOS Q 140 2 i ≠ recC Q 140 2 i → recC Q 140 2 (i + 1) = recC Q 140 2 i)) ∧
      ∀ t < 168, ∀ t' < 168, lbL Q t = lbL Q t' → t = t' := by
  unfold lbTabK tableKk at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h0, h11⟩, ⟨hB, hS⟩, hT⟩ := h
  have hBi := CFSG.KC.BfsK.buildG_at hB (by norm_num)
  obtain ⟨hC0, hCn, hSi⟩ := CFSG.KC.BfsK.stepG_facts hS (by norm_num)
  exact ⟨h0, h11, hBi, hC0, hCn, hSi, CFSG.KC.G2Three.sort_inj hT (by norm_num)⟩

theorem lbL_lt (h : lbTabK Q = true) : ∀ t < 168, lbL Q t < 2 ^ 36 := by
  obtain ⟨h0, -, hB, -⟩ := lb_facts h
  intro t ht
  cases t with
  | zero => rw [h0]; exact ONE_lt
  | succ t =>
    rw [(hB t (by omega)).2.2]
    exact MULF_lt _ _

theorem lbL_step (h : lbTabK Q = true) {u s : ℕ} (hu : u < 168) (hs : s < 2) :
    ∃ v < 168, lbL Q v = MULF (Q (s * 11)) (lbL Q u) := by
  obtain ⟨-, -, -, -, -, hS, -⟩ := lb_facts h
  have hi : u * 2 + s < 168 * 2 := by omega
  obtain ⟨-, -, p3, p4, -, -⟩ := hS _ hi
  have e1 : (u * 2 + s) / 2 = u := by omega
  have e2 : (u * 2 + s) % 2 = s := by omega
  rw [e1, e2] at p4
  exact ⟨_, p3, p4⟩

theorem lbL_mul (h : lbTabK Q = true) :
    ∀ t < 168, ∀ u < 168, ∃ v < 168, lbL Q v = MULF (lbL Q t) (lbL Q u) := by
  obtain ⟨h0, -, hB, -⟩ := lb_facts h
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht u hu
    cases t with
    | zero => exact ⟨u, hu, by rw [h0, one_mulF (lbL_lt h u hu)]⟩
    | succ i =>
      obtain ⟨p1, p2, p3⟩ := hB i (by omega)
      obtain ⟨w, hw, ew⟩ := ih (recF Q 140 0 i) (by omega) (by omega) u hu
      obtain ⟨v, hv, ev⟩ := lbL_step h hw p2
      refine ⟨v, hv, ?_⟩
      rw [ev, ew, p3, stL, mulF_assoc]
      rfl

section Lbar

variable (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hA : a0TabK R 64 = true)
  (hc : coordK R Q = true) (hg : glK R Q = true) (hl : lbTabK Q = true)

include hG hA hc hg hl in
theorem z6GsL_eq : z6GsL () = #[phiA Q (Q 0), phiA Q (Q 11)] := by
  unfold z6GsL
  rw [z6Gl_eq hG hA hc hg (by norm_num : 0 < 11), z6Gl_eq hG hA hc hg (by norm_num : 9 < 11),
    z6Gl_eq hG hA hc hg (by norm_num : 10 < 11), compA_phiA hA hc, (lb_facts hl).2.1]

theorem gsL_get {s : ℕ} (hs : s < 2) :
    (#[phiA Q (Q 0), phiA Q (Q 11)])[s]! = phiA Q (Q (Nat.mul s 11)) := by
  rw [getElem!_pos _ s (by simp; omega)]
  interval_cases s
  · rfl
  · rfl

theorem phiA_stL (hA : a0TabK R 64 = true) (hc : coordK R Q = true) (x : ℕ) {s : ℕ}
    (hs : s < 2) :
    phiA Q (stL Q x s) = compA (phiA Q x) (#[phiA Q (Q 0), phiA Q (Q 11)])[s]! := by
  rw [gsL_get hs, compA_phiA hA hc]
  unfold stL
  rfl

include hA hc hl in
theorem enumL_step (hgs : z6GsL () = #[phiA Q (Q 0), phiA Q (Q 11)]) :
    ∀ i < 168 * (z6GsL ()).size, StepE (z6GsL ()) (fun t => phiA Q (lbL Q t))
      (recF Q 140 0) (recF Q 140 1) (recC Q 140 2) (recPOS Q 140 2) 168 i := by
  obtain ⟨-, -, -, -, -, hSi, -⟩ := lb_facts hl
  have hsz : (z6GsL ()).size = 2 := by rw [hgs]; rfl
  intro i hi
  rw [hsz] at hi
  obtain ⟨a, b, c, d, e, f⟩ := hSi i hi
  unfold StepE
  rw [hsz]
  refine ⟨a, b, c, ?_, e, f⟩
  change phiA Q (lbL Q (recPOS Q 140 2 i)) = compA (phiA Q (lbL Q (i / 2))) (z6GsL ())[i % 2]!
  rw [d, hgs]
  exact phiA_stL hA hc _ (Nat.mod_lt _ (by norm_num))

include hA hc hl in
theorem enumL_tree (hgs : z6GsL () = #[phiA Q (Q 0), phiA Q (Q 11)]) :
    ∀ i < 168 - 1, recF Q 140 0 i ≤ i ∧ recF Q 140 1 i < (z6GsL ()).size ∧
      phiA Q (lbL Q (i + 1)) =
        compA (phiA Q (lbL Q (recF Q 140 0 i))) (z6GsL ())[recF Q 140 1 i]! := by
  obtain ⟨-, -, hB, -⟩ := lb_facts hl
  have hsz : (z6GsL ()).size = 2 := by rw [hgs]; rfl
  intro i hi
  obtain ⟨a, b, c⟩ := hB i hi
  refine ⟨a, by rw [hsz]; exact b, ?_⟩
  rw [c, hgs]
  exact phiA_stL hA hc _ b

include hG hA hc hg hl in
theorem enumL_inv :
    BInvE (fun t => phiA Q (lbL Q t)) (recF Q 140 0) (recF Q 140 1) 168 (z6EnumL ()) ∧
      enumOK (z6EnumL ()) (z6GsL ()) = true := by
  obtain ⟨h0, -, -, hC0, hCn, -, hX⟩ := lb_facts hl
  have hlt := lbL_lt hl
  have hgs := z6GsL_eq hG hA hc hg hl
  have hsz : (z6GsL ()).size = 2 := by rw [hgs]; rfl
  have hk : 0 < (z6GsL ()).size := by rw [hsz]; norm_num
  have hd : ∀ t < 168, ∀ t' < 168, phiA Q (lbL Q t) = phiA Q (lbL Q t') → t = t' :=
    fun t ht t' ht' e => hX t ht t' ht' (phiA_inj hA hc (hlt t ht) (hlt t' ht') e)
  have hT0 : phiA Q (lbL Q 0) = idA () := by rw [h0, phiA_one hA hc]
  have hS' := enumL_step hA hc hl hgs
  have hB' := enumL_tree hA hc hl hgs
  have hCn' : recC Q 140 2 (168 * (z6GsL ()).size) = 168 := by rw [hsz]; exact hCn
  have r1 := bfsEnum_replay (fuel := 200) (T := fun t => phiA Q (lbL Q t)) (PA := recF Q 140 0)
    (PB := recF Q 140 1) (C := recC Q 140 2) (POS := recPOS Q 140 2) (n := 168) hk (by norm_num)
    (by norm_num) hT0 hd hC0 hCn' hS'
  have r2 := enumOK_of_replay (fuel := 200) (T := fun t => phiA Q (lbL Q t))
    (PA := recF Q 140 0) (PB := recF Q 140 1) (C := recC Q 140 2) (POS := recPOS Q 140 2)
    (n := 168) hk (by norm_num) (by norm_num) hT0 hd hC0 hCn' hS' hB'
  unfold z6EnumL
  exact ⟨r1, r2⟩

include hG hA hc hg hl in
theorem enumL_get {t : ℕ} (ht : t < 168) : (z6EnumL ()).elems[t]! = phiA Q (lbL Q t) :=
  (enumL_inv hG hA hc hg hl).1.2.2.2.1 t ht

include hG hA hc hg hl in
theorem enumL_lookup {t : ℕ} (ht : t < 168) :
    (z6EnumL ()).lookup (phiA Q (lbL Q t)) = some t := by
  have := lookup_of_inv (enumL_inv hG hA hc hg hl).1 ht
  simpa using this

include hG hA hc hg hl in
theorem z6LbarCheck_of (hm : lbMemK Q = true) : z6LbarCheck () = true := by
  obtain ⟨hE, hok⟩ := enumL_inv hG hA hc hg hl
  have hgs := z6GsL_eq hG hA hc hg hl
  unfold lbMemK at hm
  simp only [Bool.and_eq_true, Nat.beq_eq] at hm
  obtain ⟨⟨ha, hb⟩, hpos⟩ := hm
  unfold z6LbarCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨hok, hE.1⟩, fun i hi => ?_⟩, ?_⟩, ?_⟩
  · have e := CFSG.KC.G2Three.allBelow_g2 hpos (by norm_num) i hi
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
    rw [z6Gl_eq hG hA hc hg hi, ← e.2, enumL_lookup hG hA hc hg hl e.1]
    rfl
  · rw [hgs]
    change compA (phiA Q (Q 0)) (phiA Q (Q 0)) = idA ()
    rw [compA_phiA hA hc, ha, phiA_one hA hc]
  · rw [hgs]
    change compA (phiA Q (Q 11)) (compA (phiA Q (Q 11)) (phiA Q (Q 11))) = idA ()
    rw [compA_phiA hA hc, compA_phiA hA hc, hb, phiA_one hA hc]

include hG hA hc hg hl in
theorem img_fold {v : ℕ} (hv : v < 64) :
    ∀ J : List ℕ, (∀ m ∈ J, m < 168) →
      J.foldr (fun m acc => ((z6MulTab ())[((z6EnumL ()).elems[m]!)[v]!]!)[acc]!) 0 =
        psc Q (J.foldr (fun m a => Nat.xor (MULF (crd Q v) (lbL Q m)) a) 0)
  | [], _ => by
    rw [List.foldr_nil, List.foldr_nil, psc_zero hA hc]
  | m :: J, hJ => by
    have hm := hJ m List.mem_cons_self
    have ih := img_fold hv J fun x hx => hJ x (List.mem_cons_of_mem _ hx)
    have hlt : ∀ J : List ℕ, J.foldr (fun m a => Nat.xor (MULF (crd Q v) (lbL Q m)) a) 0 < 64 := by
      intro J
      induction J with
      | nil => norm_num
      | cons x J ihJ => exact xor_lt64 (vec_lt (crd_lt hA hc hv) _) ihJ
    rw [List.foldr_cons, List.foldr_cons, ih, enumL_get hG hA hc hg hl hm, phiA_get _ hv,
      z6MulTab_psc hG hA hc (vec_lt (crd_lt hA hc hv) _) (hlt J)]
    rfl

include hG hA hc hg hl in
theorem z6OrbCheck_of (ho : orbK Q = true) : z6OrbCheck () = true := by
  have hrow : rowsW (lbL Q) (crd Q 3) = [1, 2, 4, 8, 16, 32] := by
    unfold orbK at ho
    simpa using ho
  have hbp : z6BPos () = #[psc Q 1, psc Q 2, psc Q 4, psc Q 8, psc Q 16, psc Q 32] := by
    have e : ∀ j < 6, z6Pos (enumA0 ()) ((gA0 ())[j]!) = psc Q (2 ^ j) := by
      intro j hj
      have hp := psc_lt hA hc (pow_lt64 hj)
      rw [gA0_eq hG hj]
      have : arrN (R (j + 3)) = arrN (recX R 12 (psc Q (2 ^ j))) := by
        unfold arrN matN
        rw [genX hA hc hj]
      rw [this, z6Pos_recX hG hA hc hp]
    unfold z6BPos
    simp only
    refine Array.ext (by simp [size_gA0]) fun i h1 h2 => ?_
    simp only [Array.size_map, size_gA0] at h1
    rw [Array.getElem_map, ← getElem!_pos (gA0 ()) i (by rw [size_gA0]; exact h1), e i h1]
    interval_cases i <;> rfl
  have himg : z6Img (z6MulTab ()) (z6EnumL ()).elems z6Beta =
      ((rowsW (lbL Q) (crd Q 3)).map (psc Q)).toArray := by
    unfold z6Img rowsW
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun J hJ => ?_
    exact img_fold hG hA hc hg hl (v := 3) (by norm_num) J (by
      intro m hm
      simp only [z6J, List.mem_cons, List.not_mem_nil, or_false] at hJ
      rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hm <;> omega)
  unfold z6OrbCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, by decide⟩, by unfold z6Beta; norm_num⟩
  rw [himg, hrow, hbp]
  rfl

end Lbar

end CFSG.KC.YamakiLbar

end
