module

public import CFSG.Certificates.Kernel.Spor.RawOrbSize

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

@[expose] def toF {n : Nat} (hn : 0 < n) (x : Nat) : Fin n := ⟨x % n, Nat.mod_lt _ hn⟩

theorem toF_eq {n : Nat} (hn : 0 < n) {x : Nat} (hx : x < n) : toF hn x = ⟨x, hx⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hx)

structure RecOK (n root r : Nat) (st : Nat → Nat → Nat) (c : Nat) (P Q par lab : Nat → Nat) :
    Prop where
  c_pos : 0 < c
  root : P 0 = root
  pt : ∀ k < c, P k < n ∧ Q (P k) = k
  pos : ∀ z < n, Q z < c → P (Q z) = z
  par_lt : ∀ k < c, 0 < k → par k < k
  lab_lt : ∀ k < c, 0 < k → lab k < r
  edge : ∀ k < c, 0 < k → st (lab k) (P (par k)) = P k
  mono : ∀ k < c, 0 < k → k + 1 < c → LexLt (par k) (lab k) (par (k + 1)) (lab (k + 1))
  closed : ∀ h < c, ∀ j < r, Q (st j (P h)) < c ∧
    (Q (st j (P h)) = 0 ∨ ¬ LexLt h j (par (Q (st j (P h)))) (lab (Q (st j (P h)))))

theorem RecOK.congr {n root r c : Nat} {st st' : Nat → Nat → Nat} {P Q par lab : Nat → Nat}
    (hR : RecOK n root r st c P Q par lab) (e : ∀ j < r, ∀ x < n, st j x = st' j x) :
    RecOK n root r st' c P Q par lab where
  c_pos := hR.c_pos
  root := hR.root
  pt := hR.pt
  pos := hR.pos
  par_lt := hR.par_lt
  lab_lt := hR.lab_lt
  edge := fun k hk hk0 => by
    have hp := hR.par_lt k hk hk0
    rw [← e _ (hR.lab_lt k hk hk0) _ (hR.pt _ (by omega)).1]
    exact hR.edge k hk hk0
  mono := hR.mono
  closed := fun h hh j hj => by
    rw [← e j hj _ (hR.pt h hh).1]
    exact hR.closed h hh j hj

theorem bfsCert_of_recOK {n root r c : Nat} {st : Nat → Nat → Nat} {P Q par lab : Nat → Nat}
    (hn : 0 < n) (hr : root < n) (hR : RecOK n root r st c P Q par lab)
    {σ : Nat → Equiv.Perm (Fin n)} (hσ : ∀ j < r, ∀ x : Fin n, st j x = (σ j x : Nat))
    {T : Nat → Equiv.Perm (Fin n)} (hT0 : T 0 = 1)
    (hT : ∀ k < c, 0 < k → T k = σ (lab k) * T (par k)) :
    BFSCert (List.ofFn fun j : Fin r => σ j) ⟨root, hr⟩ c (fun k => toF hn (P k)) par lab T where
  pos := hR.c_pos
  root := by
    rw [toF_eq hn (hR.pt 0 hR.c_pos).1]
    exact Fin.ext hR.root
  T_zero := hT0
  inj := fun i hi j hj e => by
    have e1 := congrArg Fin.val e
    simp only [toF_eq hn (hR.pt i hi).1, toF_eq hn (hR.pt j hj).1] at e1
    rw [← (hR.pt i hi).2, ← (hR.pt j hj).2, e1]
  par_lt := fun k hk hkm => hR.par_lt k hkm hk
  lab_lt := fun k hk hkm => by
    rw [List.length_ofFn]
    exact hR.lab_lt k hkm hk
  edge := fun k hk hkm => by
    have hp := hR.par_lt k hkm hk
    have hpn := (hR.pt _ (by omega : par k < c)).1
    have e1 := hσ _ (hR.lab_lt k hkm hk) ⟨P (par k), hpn⟩
    apply Fin.ext
    simp only [List.getElem_ofFn, Fin.val_mk, toF_eq hn hpn, toF_eq hn (hR.pt k hkm).1]
    rw [← e1]
    exact hR.edge k hkm hk
  T_step := fun k hk hkm => by
    simp only [List.getElem_ofFn]
    exact hT k hkm hk
  mono := fun k hk hk1 => hR.mono k (by omega) hk hk1
  closed := fun h hh j hj => by
    rw [List.length_ofFn] at hj
    obtain ⟨hk, hle⟩ := hR.closed h hh j hj
    have hph := (hR.pt h hh).1
    have e1 := hσ j hj ⟨P h, hph⟩
    have hz : st j (P h) < n := by
      rw [e1]
      exact Fin.isLt _
    have hq : P (Q (st j (P h))) < n := by
      rw [hR.pos _ hz hk]
      exact hz
    refine ⟨Q (st j (P h)), hk, Fin.ext ?_, hle⟩
    simp only [List.getElem_ofFn, Fin.val_mk, toF_eq hn hph, toF_eq hn hq]
    rw [hR.pos _ hz hk]
    exact e1

theorem bfsCert_unique {n : Nat} {steps : List (Equiv.Perm (Fin n))} {b : Fin n} {m m' : Nat}
    {pts pts' : Nat → Fin n} {par lab par' lab' : Nat → Nat} {T T' : Nat → Equiv.Perm (Fin n)}
    (h1 : BFSCert steps b m pts par lab T) (h2 : BFSCert steps b m' pts' par' lab' T') :
    m = m' ∧ ∀ k < m, pts k = pts' k ∧ T k = T' k := by
  have e := congrArg SchreierOrbitState.entries (h1.run_initial_eq.symm.trans h2.run_initial_eq)
  have hm : m = m' := by simpa using congrArg List.length e
  refine ⟨hm, fun k hk => ?_⟩
  have hk' : k < m' := by omega
  have e2 := congrArg (fun l => l[k]?) e
  simp [hk, hk'] at e2
  exact e2

theorem rec_agree {n root r c c' : Nat} {st : Nat → Nat → Nat}
    {P Q par lab P' Q' par' lab' : Nat → Nat} (hn : 0 < n) (hr : root < n)
    (h1 : RecOK n root r st c P Q par lab) (h2 : RecOK n root r st c' P' Q' par' lab')
    {σ : Nat → Equiv.Perm (Fin n)} (hσ : ∀ j < r, ∀ x : Fin n, st j x = (σ j x : Nat))
    {T T' : Nat → Equiv.Perm (Fin n)} (hT0 : T 0 = 1)
    (hT : ∀ k < c, 0 < k → T k = σ (lab k) * T (par k)) (hT0' : T' 0 = 1)
    (hT' : ∀ k < c', 0 < k → T' k = σ (lab' k) * T' (par' k)) :
    c = c' ∧ (∀ k < c, P k = P' k ∧ T k = T' k) ∧
      ∀ z < n, (Q z < c ↔ Q' z < c') ∧ (Q z < c → Q z = Q' z) := by
  obtain ⟨hc, hk⟩ := bfsCert_unique (bfsCert_of_recOK hn hr h1 hσ hT0 hT)
    (bfsCert_of_recOK hn hr h2 hσ hT0' hT')
  have hP : ∀ k < c, P k = P' k := fun k hk' => by
    have e1 := congrArg Fin.val (hk k hk').1
    simpa only [toF_eq hn (h1.pt k hk').1, toF_eq hn (h2.pt k (by omega)).1] using e1
  refine ⟨hc, fun k hk' => ⟨hP k hk', (hk k hk').2⟩, fun z hz => ?_⟩
  have fwd : Q z < c → Q' z = Q z := fun hq => by
    have e1 := h1.pos z hz hq
    rw [hP _ hq] at e1
    calc Q' z = Q' (P' (Q z)) := by rw [e1]
      _ = Q z := (h2.pt _ (by omega)).2
  have bwd : Q' z < c' → Q z = Q' z := fun hq => by
    have e1 := h2.pos z hz hq
    rw [← hP _ (by omega)] at e1
    calc Q z = Q (P (Q' z)) := by rw [e1]
      _ = Q' z := (h1.pt _ (by omega)).2
  refine ⟨⟨fun hq => by rw [fwd hq]; omega, fun hq => by rw [bwd hq]; omega⟩,
    fun hq => (fwd hq).symm⟩

theorem recOK_native {n root : Nat} {steps : Array (Array Nat)} {L : Level}
    (F : LevelFacts n root steps L) :
    RecOK n root steps.size (fun j x => (steps[j]!)[x]!) L.pts.size (fun k => L.pts[k]!)
      (fun z => L.pos[z]!) (fun k => L.par[k]!) (fun k => L.lab[k]!) where
  c_pos := F.pos
  root := F.root
  pt := fun k hk => ⟨F.pts_lt k hk, F.pos_pts k hk⟩
  pos := F.pts_pos
  par_lt := F.par_lt
  lab_lt := F.lab_lt
  edge := F.edge
  mono := fun k hk hk0 hk1 => lexLt_iff.1 (F.mono k hk hk0 hk1)
  closed := fun h hh j hj => by
    obtain ⟨hk, hle⟩ := F.closed h hh j hj
    refine ⟨hk, hle.imp id fun hl hx => ?_⟩
    have e := lexLt_iff.2 hx
    rw [hl] at e
    exact Bool.false_ne_true e

theorem native_T {n root : Nat} {steps : Array (Array Nat)} {L : Level}
    (F : LevelFacts n root steps L) {σ : Nat → Equiv.Perm (Fin n)}
    (hσ : ∀ j < steps.size, Rep n steps[j]! (σ j)) :
    permOfArr n L.tr[0]! = 1 ∧ ∀ k < L.pts.size, 0 < k →
      permOfArr n L.tr[k]! = σ (L.lab[k]!) * permOfArr n L.tr[L.par[k]!]! := by
  have hr : ∀ k < L.pts.size, Rep n L.tr[k]! (permOfArr n L.tr[k]!) := fun k hk =>
    (rep_permOfArr (F.tr_inv k hk)).1
  refine ⟨(eqA_iff (hr 0 F.pos) rep_idA).1 F.tr_zero, fun k hk hk0 => ?_⟩
  have hp := F.par_lt k hk hk0
  exact (eqA_iff (hr k hk) (rep_compA (hσ _ (F.lab_lt k hk hk0)) (hr _ (by omega)))).1
    (F.tr_step k hk hk0)

theorem lexLtK_iff {a b c d : Nat} : lexLtK a b c d = true ↔ LexLt a b c d := by
  unfold lexLtK LexLt
  rw [bIf_eq, bAnd_eq, blt_dec, beq_dec, blt_dec]
  by_cases h : a < c
  · simp [h]
  · simp [h]

theorem beq_zero_false {k : Nat} (hk : 0 < k) : Nat.beq k (nat_lit 0) = false := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.blt_eq.mpr h

theorem pt_spec {n w m nw R k : Nat}
    (h : strictB (rpt w m R k) (fun p => bAnd(Nat.blt p n, Nat.beq (rpos w m nw R p) k)) = true) :
    rpt w m R k < n ∧ rpos w m nw R (rpt w m R k) = k := by
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem pos_spec {w m nw R c z : Nat} (h : lvPosK w m nw R c z = true)
    (hq : rpos w m nw R z < c) : rpt w m R (rpos w m nw R z) = z := by
  unfold lvPosK at h
  simp only [strictB_eq] at h
  exact Nat.eq_of_beq_eq_true (bIf_of_true (blt_true hq) h)

theorem edge_spec {n w m nw kS r R T k : Nat} {S SI : Nat → Nat}
    (h : bIf(Nat.beq k (nat_lit 0), true,
      strictB (rpar w m nw R k) (fun pa => strictB (rlab n nw R k) (fun lb =>
      bAnd(Nat.blt pa k, bAnd(Nat.blt lb r,
        Nat.beq (pg w m (letterK S SI kS (stAt T lb)) (rpt w m R pa)) (rpt w m R k)))))) = true)
    (hk : 0 < k) :
    rpar w m nw R k < k ∧ rlab n nw R k < r ∧
      pg w m (letterK S SI kS (stAt T (rlab n nw R k))) (rpt w m R (rpar w m nw R k)) =
        rpt w m R k := by
  rw [beq_zero_false hk] at h
  change strictB (rpar w m nw R k) (fun pa => strictB (rlab n nw R k) (fun lb =>
      bAnd(Nat.blt pa k, bAnd(Nat.blt lb r,
        Nat.beq (pg w m (letterK S SI kS (stAt T lb)) (rpt w m R pa)) (rpt w m R k))))) = true at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem mono_spec {w m nw n c R k : Nat}
    (h : bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.blt (Nat.succ k) c,
      lexLtK (rpar w m nw R k) (rlab n nw R k) (rpar w m nw R (Nat.succ k))
        (rlab n nw R (Nat.succ k)), true)) = true) (hk : 0 < k) (hk1 : k + 1 < c) :
    LexLt (rpar w m nw R k) (rlab n nw R k) (rpar w m nw R (k + 1)) (rlab n nw R (k + 1)) := by
  rw [beq_zero_false hk] at h
  change bIf(Nat.blt (Nat.succ k) c,
      lexLtK (rpar w m nw R k) (rlab n nw R k) (rpar w m nw R (Nat.succ k))
        (rlab n nw R (Nat.succ k)), true) = true at h
  exact lexLtK_iff.1 (bIf_of_true (blt_true hk1) h)

theorem closed_spec {n w m nw kS c r R T h : Nat} {S SI : Nat → Nat}
    (hc : strictB (rpt w m R h) (fun p => allN r (fun j =>
      strictB (rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) p)) (fun k' =>
      bAnd(Nat.blt k' c, bIf(Nat.beq k' (nat_lit 0), true,
        bIf(lexLtK h j (rpar w m nw R k') (rlab n nw R k'), false, true)))))) = true) :
    ∀ j < r, rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) (rpt w m R h)) < c ∧
      (rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) (rpt w m R h)) = 0 ∨
        ¬ LexLt h j (rpar w m nw R (rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) (rpt w m R h))))
          (rlab n nw R (rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) (rpt w m R h))))) := by
  intro j hj
  simp only [strictB_eq] at hc
  have h1 := allN_spec hc j hj
  set k' := rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) (rpt w m R h))
  obtain ⟨h1a, h2⟩ := (bAnd_iff _ _).1 h1
  refine ⟨Nat.blt_eq.mp h1a, ?_⟩
  rcases Nat.eq_zero_or_pos k' with h0 | h0
  · exact Or.inl h0
  · right
    intro hl
    rw [beq_zero_false h0] at h2
    change bIf(lexLtK h j (rpar w m nw R k') (rlab n nw R k'), false, true) = true at h2
    rw [lexLtK_iff.2 hl] at h2
    exact Bool.false_ne_true h2

theorem recOK_of_parts {n w kS root T R : Nat} {S SI : Nat → Nat}
    (hc0 : 0 < rcnt R) (hroot : rpt w (mask w) R 0 = root)
    (hpt : ∀ k < rcnt R, strictB (rpt w (mask w) R k) (fun p =>
      bAnd(Nat.blt p n, Nat.beq (rpos w (mask w) (n * w) R p) k)) = true)
    (hpos : ∀ z < n, lvPosK w (mask w) (n * w) R (rcnt R) z = true)
    (hedge : ∀ k < rcnt R, bIf(Nat.beq k (nat_lit 0), true,
      strictB (rpar w (mask w) (n * w) R k) (fun pa => strictB (rlab n (n * w) R k) (fun lb =>
      bAnd(Nat.blt pa k, bAnd(Nat.blt lb (stCnt T),
        Nat.beq (pg w (mask w) (letterK S SI kS (stAt T lb)) (rpt w (mask w) R pa))
          (rpt w (mask w) R k)))))) = true)
    (hmono : ∀ k < rcnt R, bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.blt (Nat.succ k) (rcnt R),
      lexLtK (rpar w (mask w) (n * w) R k) (rlab n (n * w) R k)
        (rpar w (mask w) (n * w) R (Nat.succ k)) (rlab n (n * w) R (Nat.succ k)), true)) = true)
    (hcl : ∀ h < rcnt R, strictB (rpt w (mask w) R h) (fun p => allN (stCnt T) (fun j =>
      strictB (rpos w (mask w) (n * w) R (pg w (mask w) (letterK S SI kS (stAt T j)) p))
        (fun k' => bAnd(Nat.blt k' (rcnt R), bIf(Nat.beq k' (nat_lit 0), true,
          bIf(lexLtK h j (rpar w (mask w) (n * w) R k') (rlab n (n * w) R k'), false,
            true)))))) = true) :
    RecOK n root (stCnt T) (fun j x => pg w (mask w) (letterK S SI kS (stAt T j)) x) (rcnt R)
      (rpt w (mask w) R) (rpos w (mask w) (n * w) R) (rpar w (mask w) (n * w) R)
      (rlab n (n * w) R) where
  c_pos := hc0
  root := hroot
  pt := fun k hk => pt_spec (hpt k hk)
  pos := fun z hz hq => pos_spec (hpos z hz) hq
  par_lt := fun k hk hk0 => (edge_spec (hedge k hk) hk0).1
  lab_lt := fun k hk hk0 => (edge_spec (hedge k hk) hk0).2.1
  edge := fun k hk hk0 => (edge_spec (hedge k hk) hk0).2.2
  mono := fun k hk hk0 hk1 => mono_spec (hmono k hk) hk0 hk1
  closed := fun h hh => closed_spec (hcl h hh)

theorem levelK_facts {n w pm idn kS root T R : Nat} {S SI TR TRI : Nat → Nat}
    (h : levelK n w (mask w) (n * w) pm idn S SI TR TRI kS root T R = true) :
    szOK n w = true ∧ kS < 128 ∧
    RecOK n root (stCnt T) (fun j x => pg w (mask w) (letterK S SI kS (stAt T j)) x) (rcnt R)
      (rpt w (mask w) R) (rpos w (mask w) (n * w) R) (rpar w (mask w) (n * w) R)
      (rlab n (n * w) R) ∧
    TR (roff n (n * w) R) = idn ∧
    (∀ k < rcnt R, 0 < k → eq2 n w (mask w) (TR (roff n (n * w) R + k))
      (letterK S SI kS (stAt T (rlab n (n * w) R k)))
      (TR (roff n (n * w) R + rpar w (mask w) (n * w) R k)) = true) ∧
    ∀ k < rcnt R, permOK n w (mask w) (n * w) (TR (roff n (n * w) R + k))
      (TRI (roff n (n * w) R + k)) = true := by
  unfold levelK at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h6, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h7, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h8, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h9, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h10, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h11, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h12, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h13, h14⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, Nat.blt_eq.mp h2, recOK_of_parts (Nat.blt_eq.mp h3) (Nat.eq_of_beq_eq_true h6)
    (allN_spec h7) (allN_spec h8) (allN_spec h9) (allN_spec h10) (allN_spec h11),
    Nat.eq_of_beq_eq_true h12, fun k hk hk0 => ?_, allN_spec h14⟩
  have e := allN_spec h13 k hk
  rw [beq_zero_false hk0] at e
  exact e

theorem treeK_facts {n w kS root T R : Nat} {S SI : Nat → Nat}
    (hh : lvHdTK n w (mask w) kS root T R = true)
    (hp : ∀ k < n, lvPtTK n w (mask w) (n * w) S SI kS T R (rcnt R) (stCnt T) k = true) :
    szOK n w = true ∧ kS < 128 ∧
    RecOK n root (stCnt T) (fun j x => pg w (mask w) (letterK S SI kS (stAt T j)) x) (rcnt R)
      (rpt w (mask w) R) (rpos w (mask w) (n * w) R) (rpar w (mask w) (n * w) R)
      (rlab n (n * w) R) := by
  unfold lvHdTK at hh
  rw [strictB_eq, strictB_eq] at hh
  obtain ⟨h1, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h2, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h3, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h4, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨_, h6⟩ := (bAnd_iff _ _).1 hh
  have hcn : rcnt R ≤ n := Nat.le_of_ble_eq_true h4
  have kk : ∀ k < rcnt R,
      lvKKT n w (mask w) (n * w) S SI kS T R (rcnt R) (stCnt T) k = true := fun k hk =>
    bIf_of_true (blt_true hk) ((bAnd_iff _ _).1 (hp k (by omega))).2
  have kp : ∀ z < n, lvPosK w (mask w) (n * w) R (rcnt R) z = true := fun z hz =>
    bIf_of_true (blt_true hz) ((bAnd_iff _ _).1 (hp z hz)).1
  have kB := fun k hk => ((bAnd_iff _ _).1 (kk k hk)).1
  have kD := fun k hk => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (kk k hk)).2).1
  have kE := fun k hk =>
    ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (kk k hk)).2).2).1
  have kF := fun k hk =>
    ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (kk k hk)).2).2).2
  exact ⟨h1, Nat.blt_eq.mp h2, recOK_of_parts (Nat.blt_eq.mp h3) (Nat.eq_of_beq_eq_true h6)
    kB kp kD kE kF⟩

theorem prep_unique {n w P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g)
    (hh : PRep n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem rep_pa {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    Rep n t (permOfArr n t) :=
  (rep_permOfArr (isInvA_of_rep h (rep_invCand h))).1

theorem prep_invLetter {n w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) {l : Nat}
    (hl : l < kS + kS) {g : Equiv.Perm (Fin n)} (h : PRep n w (letterK PS PSI kS l) g) :
    PRep n w (invLetterK PS PSI kS l) g⁻¹ := by
  unfold letterK at h
  unfold invLetterK
  rw [nIf_eq, blt_dec] at h ⊢
  by_cases hk : l < kS
  · simp only [hk, decide_true, ↓reduceIte] at h ⊢
    obtain ⟨h1, h2⟩ := prep_PS hb hp hk
    rw [prep_unique h h1]
    exact h2
  · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hk' : l - kS < kS := by omega
    obtain ⟨h1, h2⟩ := prep_PS hb hp hk'
    rw [prep_unique h h2, inv_inv]
    exact h1

@[expose] noncomputable def stp (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i j : Nat) :
    Equiv.Perm (Fin n) :=
  permOfArr n (rawSteps n S base i)[j]!

@[expose] noncomputable def treeF {n : Nat} (σ : Nat → Equiv.Perm (Fin n)) (par lab : Nat → Nat) :
    Nat → Nat → Equiv.Perm (Fin n)
  | 0, _ => 1
  | f + 1, k => if k = 0 then 1 else σ (lab k) * treeF σ par lab f (par k)

theorem treeF_zero {n : Nat} (σ : Nat → Equiv.Perm (Fin n)) (par lab : Nat → Nat) (f : Nat) :
    treeF σ par lab f 0 = 1 := by
  cases f <;> simp [treeF]

theorem treeF_stable {n c : Nat} {σ : Nat → Equiv.Perm (Fin n)} {par lab : Nat → Nat}
    (hpar : ∀ k < c, 0 < k → par k < k) :
    ∀ f g k, k < c → k ≤ f → k ≤ g → treeF σ par lab f k = treeF σ par lab g k := by
  intro f
  induction f with
  | zero =>
    intro g k _ hkf _
    have hk : k = 0 := by omega
    subst hk
    rw [treeF_zero, treeF_zero]
  | succ f ih =>
    intro g k hkc hkf hkg
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [treeF_zero, treeF_zero]
    · obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hp := hpar k hkc hk0
      simp only [treeF, show k ≠ 0 by omega, ↓reduceIte]
      rw [ih g (par k) (by omega) (by omega) (by omega)]

theorem treeF_step {n c : Nat} {σ : Nat → Equiv.Perm (Fin n)} {par lab : Nat → Nat}
    (hpar : ∀ k < c, 0 < k → par k < k) {k : Nat} (hk : k < c) (hk0 : 0 < k) :
    treeF σ par lab k k = σ (lab k) * treeF σ par lab (par k) (par k) := by
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp := hpar _ hk hk0
  simp only [treeF, show f + 1 ≠ 0 by omega, ↓reduceIte]
  rw [treeF_stable hpar f (par (f + 1)) (par (f + 1)) (by omega) (by omega) le_rfl]

structure Agree (n w R : Nat) (L : Level) (TK : Nat → Equiv.Perm (Fin n)) : Prop where
  cnt : rcnt R = L.pts.size
  pt : ∀ k < L.pts.size, rpt w (mask w) R k = L.pts[k]!
  pos : ∀ z < n, (rpos w (mask w) (n * w) R z < rcnt R ↔ L.pos[z]! < L.pts.size)
  posE : ∀ z < n, L.pos[z]! < L.pts.size → rpos w (mask w) (n * w) R z = L.pos[z]!
  tr : ∀ k < L.pts.size, Rep n L.tr[k]! (TK k) ∧ Rep n L.trInv[k]! (TK k)⁻¹

section Levels

variable {n w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
include hb hp

theorem rep_stp {i j : Nat} (hj : j < (rawSteps n S base i).size) :
    Rep n (rawSteps n S base i)[j]! (stp n S base i j) := by
  obtain ⟨g, hg⟩ := rep_of_mem_levelSteps (isInv_of hb hp)
    (by rw [getElem!_pos _ j hj]; exact Array.getElem_mem hj : (rawSteps n S base i)[j]! ∈
      levelSteps S (rawInvs n S) base i)
  exact rep_pa hg

theorem native_facts {i : Nat} (hi : i < nb) (hroot : base[i]! < n) :
    LevelFacts n base[i]! (rawSteps n S base i) (lev n S base i) := by
  have hrep : ∀ j < (rawSteps n S base i).size, ∃ g : Equiv.Perm (Fin n),
      Rep n (rawSteps n S base i)[j]! g := fun j hj => ⟨_, rep_stp hb hp hj⟩
  have hlt : ∀ j < (rawSteps n S base i).size, ∀ x < n, ((rawSteps n S base i)[j]!)[x]! < n :=
    fun j hj x hx => (rep_stp hb hp hj).lt hx
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  rw [lev, rawLevels_get (by omega : i < base.size)]
  exact levelFacts_of_levelOK (levelOK_of (levelOKT_bfs hroot hlt) (levelTrOK_bfs hrep))

theorem kernel_steps (hk : kS < 128) (hbl : ∀ t < nb, base[t]! < n) {i : Nat} (hi : i ≤ nb) :
    stCnt (stepsAt n w PS kS BP i) = (rawSteps n S base i).size ∧
      (∀ j < (rawSteps n S base i).size, ∀ x : Fin n,
        pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j)) x =
          (stp n S base i j x : Nat)) ∧
      (∀ j < (rawSteps n S base i).size,
        PRep n w (letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j)) (stp n S base i j)) ∧
      ∀ j < (rawSteps n S base i).size,
        PRep n w (invLetterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j)) (stp n S base i j)⁻¹ := by
  obtain ⟨hcnt, hstep⟩ := steps_eq hb hp hk hi hbl
  have hpr : ∀ j < (rawSteps n S base i).size, ∀ x : Fin n,
      pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j)) x =
        (stp n S base i j x : Nat) := fun j hj x => by
    rw [hstep j hj x x.2]
    exact rep_stp hb hp hj x
  refine ⟨hcnt, hpr, fun j hj => hpr j hj, fun j hj => ?_⟩
  have hk2 : kS + kS < 256 := by omega
  have hjL : j < ((List.range (kS + kS)).filter
      (tabP kS (fixMaskK w (mask w) PS kS BP i))).length := by
    rw [← stCnt_eq hk2]
    change j < stCnt (stepsAt n w PS kS BP i)
    rw [hcnt]
    exact hj
  have hl : stAt (stepsAt n w PS kS BP i) j < kS + kS := by
    unfold stepsAt
    rw [stAt_eq hk2 hjL]
    have := List.getElem_mem hjL
    rw [List.mem_filter, List.mem_range] at this
    exact this.1
  exact prep_invLetter hb hp hl (hpr j hj)

theorem agree_levelK (hbl : ∀ t < nb, base[t]! < n) {TR TRI R : Nat → Nat} {i : Nat}
    (hi : i < nb)
    (hl : levelK n w (mask w) (n * w) (mask (n * w)) (pidn n w) PS PSI TR TRI kS
      (pg w (mask w) BP i) (stepsAt n w PS kS BP i) (R i) = true) :
    Agree n w (R i) (lev n S base i)
        (fun k => permOfArr n (unpack n w (TR (roff n (n * w) (R i) + k)))) ∧
      ∀ k < rcnt (R i), PRep n w (TR (roff n (n * w) (R i) + k))
          (permOfArr n (unpack n w (TR (roff n (n * w) (R i) + k)))) ∧
        PRep n w (TRI (roff n (n * w) (R i) + k))
          (permOfArr n (unpack n w (TR (roff n (n * w) (R i) + k))))⁻¹ := by
  obtain ⟨hsz, hk, hR, h0, hst, hperm⟩ := levelK_facts hl
  unfold szOK at hsz
  rw [bAnd_iff, Nat.blt_eq, Nat.blt_eq] at hsz
  have hn24 : n < 16777216 := hsz.1
  have hw : n + 1 < 2 ^ w := by
    have := hsz.2
    rwa [shl_eq', Nat.one_mul] at this
  obtain ⟨hcnt, hpr, hlet, _⟩ := kernel_steps hb hp hk hbl hi.le
  have hroot := hbl i hi
  have hbi : base[i]! = pg w (mask w) BP i := hb.2.2.2.2.2.2 i hi
  have hn : 0 < n := hb.1
  set o := roff n (n * w) (R i)
  set TK := fun k => permOfArr n (unpack n w (TR (o + k)))
  have hTK : ∀ k < rcnt (R i), PRep n w (TR (o + k)) (TK k) ∧ PRep n w (TRI (o + k)) (TK k)⁻¹ :=
    fun k hk => by
      have hr := rep_permOfArr (isInvA_unpack (hperm k hk))
      exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩
  have F := native_facts hb hp hi hroot
  have NR := recOK_native F
  have KR := hR.congr (st' := fun j x => ((rawSteps n S base i)[j]!)[x]!) fun j hj x hx =>
    (hpr j (by omega) ⟨x, hx⟩).trans ((rep_stp hb hp (by omega)) ⟨x, hx⟩).symm
  rw [hcnt, ← hbi] at KR
  have hT0 : TK 0 = 1 := by
    have e := (hTK 0 hR.c_pos).1
    rw [Nat.add_zero, h0] at e
    exact prep_unique e (prep_pidn hn24 hw)
  have hT : ∀ k < rcnt (R i), 0 < k →
      TK k = stp n S base i (rlab n (n * w) (R i) k) * TK (rpar w (mask w) (n * w) (R i) k) := by
    intro k hk hk0
    have hpk := hR.par_lt k hk hk0
    have hlk := hR.lab_lt k hk hk0
    have e2 := hst k hk hk0
    unfold eq2 at e2
    apply Equiv.ext
    intro x
    apply Fin.ext
    have e3 := Nat.eq_of_beq_eq_true (allN_spec e2 x x.2)
    rw [← (hTK k hk).1 x, Equiv.Perm.mul_apply, e3, (hTK _ (by omega)).1 x,
      hlet _ (by omega) _]
  have hσ : ∀ j < (rawSteps n S base i).size, ∀ x : Fin n,
      ((rawSteps n S base i)[j]!)[(x : Nat)]! = (stp n S base i j x : Nat) :=
    fun j hj x => rep_stp hb hp hj x
  obtain ⟨T0N, TSN⟩ := native_T F (fun j hj => rep_stp hb hp hj)
  obtain ⟨hc, hPT, hQ⟩ := rec_agree (T := TK)
    (T' := fun k => permOfArr n (lev n S base i).tr[k]!) hn hroot KR NR hσ hT0 hT T0N TSN
  refine ⟨⟨hc, fun k hk => ((hPT k (by omega)).1), fun z hz => (hQ z hz).1, fun z hz hq => ?_,
    fun k hk => ?_⟩, hTK⟩
  · exact (hQ z hz).2 ((hQ z hz).1.2 hq)
  · have e : TK k = permOfArr n (lev n S base i).tr[k]! := (hPT k (by omega)).2
    have hr := rep_permOfArr (F.tr_inv k hk)
    exact e ▸ hr

theorem agree_treeK (hbl : ∀ t < nb, base[t]! < n) {R : Nat → Nat} {i : Nat} (hi : i < nb)
    (hh : lvHdTK n w (mask w) kS (pg w (mask w) BP i) (stepsAt n w PS kS BP i) (R i) = true)
    (hpt : ∀ k < n, lvPtTK n w (mask w) (n * w) PS PSI kS (stepsAt n w PS kS BP i) (R i)
      (rcnt (R i)) (stCnt (stepsAt n w PS kS BP i)) k = true) :
    (∀ k < rcnt (R i), 0 < k → rpar w (mask w) (n * w) (R i) k < k ∧
      rlab n (n * w) (R i) k < (rawSteps n S base i).size) ∧
    Agree n w (R i) (lev n S base i) (fun k => treeF (stp n S base i)
      (rpar w (mask w) (n * w) (R i)) (rlab n (n * w) (R i)) k k) := by
  obtain ⟨_, hk, hR⟩ := treeK_facts hh hpt
  obtain ⟨hcnt, hpr, _, _⟩ := kernel_steps hb hp hk hbl hi.le
  have hroot := hbl i hi
  have hbi : base[i]! = pg w (mask w) BP i := hb.2.2.2.2.2.2 i hi
  have hn : 0 < n := hb.1
  have F := native_facts hb hp hi hroot
  have NR := recOK_native F
  have KR := hR.congr (st' := fun j x => ((rawSteps n S base i)[j]!)[x]!) fun j hj x hx =>
    (hpr j (by omega) ⟨x, hx⟩).trans ((rep_stp hb hp (by omega)) ⟨x, hx⟩).symm
  rw [hcnt, ← hbi] at KR
  have hσ : ∀ j < (rawSteps n S base i).size, ∀ x : Fin n,
      ((rawSteps n S base i)[j]!)[(x : Nat)]! = (stp n S base i j x : Nat) :=
    fun j hj x => rep_stp hb hp hj x
  obtain ⟨T0N, TSN⟩ := native_T F (fun j hj => rep_stp hb hp hj)
  set TK := fun k => treeF (stp n S base i) (rpar w (mask w) (n * w) (R i))
    (rlab n (n * w) (R i)) k k
  have hT0 : TK 0 = 1 := treeF_zero _ _ _ _
  obtain ⟨hc, hPT, hQ⟩ := rec_agree (T := TK)
    (T' := fun k => permOfArr n (lev n S base i).tr[k]!) hn hroot KR NR hσ hT0
    (fun k hk hk0 => treeF_step KR.par_lt hk hk0) T0N TSN
  refine ⟨fun k hk hk0 => ⟨KR.par_lt k hk hk0, KR.lab_lt k hk hk0⟩,
    ⟨hc, fun k hk => ((hPT k (by omega)).1), fun z hz => (hQ z hz).1, fun z hz hq => ?_,
    fun k hk => ?_⟩⟩
  · exact (hQ z hz).2 ((hQ z hz).1.2 hq)
  · have e : TK k = permOfArr n (lev n S base i).tr[k]! := (hPT k (by omega)).2
    have hr := rep_permOfArr (F.tr_inv k hk)
    exact e ▸ hr

end Levels

end CFSG.KS.Raw.Orb

end
