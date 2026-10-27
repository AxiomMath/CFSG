module

public import Certificates.Data.Kernel.SporSch.BasePtWit
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.SporSch.TblSound
public import CFSG.Certificates.Kernel.SporSch.ChainKCount
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec

public section

namespace CFSG.KS.SporSch.BPW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PEnum CFSG.KS.MulH CFSG.Certificates
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 Certificates.Odd87F3

variable {n w : Nat}

theorem strictN_eqB (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem itP_pow {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (hf : ∀ x : Fin n, f x = g x)
    (e : Nat) (x : Fin n) : itP f e x = ((g ^ e) x : Nat) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    change strictN (itP f e x) f = _
    rw [strictN_eqB, ih, hf, pow_succ', Equiv.Perm.mul_apply]

theorem movB_true {f : Nat → Nat} : ∀ {bs : List Nat}, movB f bs = true → ∃ b ∈ bs, f b ≠ b
  | [], h => absurd h Bool.false_ne_true
  | b :: bs, h => by
    change Bool.rec (motive := fun _ => Bool) true (movB f bs) (Nat.beq (f b) b) = true at h
    cases hb : Nat.beq (f b) b
    · exact ⟨b, List.mem_cons_self, fun e => by rw [e, Nat.beq_refl] at hb; cases hb⟩
    · rw [hb] at h
      obtain ⟨c, hc, hne⟩ := movB_true h
      exact ⟨c, List.mem_cons_of_mem _ hc, hne⟩

theorem movB_of {f : Nat → Nat} : ∀ {bs : List Nat}, (∃ b ∈ bs, f b ≠ b) → movB f bs = true
  | [], ⟨_, hb, _⟩ => absurd hb List.not_mem_nil
  | b :: bs, ⟨c, hc, hne⟩ => by
    change Bool.rec (motive := fun _ => Bool) true (movB f bs) (Nat.beq (f b) b) = true
    cases hb : Nat.beq (f b) b
    · rfl
    · have e : f b = b := Nat.eq_of_beq_eq_true hb
      rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd e hne
      · exact movB_of ⟨c, hc, hne⟩

theorem fixB_of {f : Nat → Nat} {e : Nat} :
    ∀ {bs : List Nat}, (∀ b ∈ bs, itP f e b = b) → fixB f e bs = true
  | [], _ => rfl
  | b :: bs, h => by
    change Bool.rec (motive := fun _ => Bool) false (fixB f e bs) (Nat.beq (itP f e b) b) = true
    rw [h b List.mem_cons_self, Nat.beq_refl]
    exact fixB_of fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem any_true {P : Nat → Nat → Bool} : ∀ {L : List (Nat × Nat)},
    List.rec (motive := fun _ => Bool) false (fun c _ ih =>
      Prod.rec (motive := fun _ => Bool) (fun C CI => bIf(P C CI, true, ih)) c) L = true →
    ∃ c ∈ L, P c.1 c.2 = true
  | [], h => absurd h Bool.false_ne_true
  | (C, CI) :: L, h => by
    change Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false
      (fun c _ ih => Prod.rec (motive := fun _ => Bool) (fun C CI => bIf(P C CI, true, ih)) c) L)
      true (P C CI) = true at h
    cases hP : P C CI
    · rw [hP] at h
      obtain ⟨c, hc, h'⟩ := any_true h
      exact ⟨c, List.mem_cons_of_mem _ hc, h'⟩
    · exact ⟨(C, CI), List.mem_cons_self, hP⟩

theorem witB_true {U S e : Nat} {bs : List Nat} {OG : List (Nat × Nat)}
    (h : witB w U S e bs OG = true) :
    (∃ c ∈ OG, movB (itP (y1P w U S c.1 c.2) e) bs = true) ∨
      ∃ c₁ ∈ OG, ∃ c₂ ∈ OG, movB (itP (y2P w U S c₁.1 c₁.2 c₂.1 c₂.2) e) bs = true := by
  unfold witB at h
  revert h
  generalize hA : List.rec (motive := fun _ => Bool) false (fun c _ ih =>
      Prod.rec (motive := fun _ => Bool) (fun C CI =>
        bIf(movB (itP (y1P w U S C CI) e) bs, true, ih)) c) OG = A
  intro h
  cases A
  · right
    obtain ⟨c₁, hc₁, h1⟩ := any_true (P := fun C1 C1I => List.rec (motive := fun _ => Bool) false
      (fun c₂ _ ih2 => Prod.rec (motive := fun _ => Bool) (fun C2 C2I =>
        bIf(movB (itP (y2P w U S C1 C1I C2 C2I) e) bs, true, ih2)) c₂) OG) h
    obtain ⟨c₂, hc₂, h2⟩ := any_true (P := fun C2 C2I =>
      movB (itP (y2P w U S c₁.1 c₁.2 C2 C2I) e) bs) h1
    exact ⟨c₁, hc₁, c₂, hc₂, h2⟩
  · left
    exact any_true (P := fun C CI => movB (itP (y1P w U S C CI) e) bs) hA

theorem rowsB_mem {U S : Nat} {bs : List Nat} :
    ∀ {rows : List (Nat × Nat × List (Nat × Nat))}, rowsB w U S bs rows = true →
    ∀ {p e : Nat} {OG : List (Nat × Nat)}, (p, e, OG) ∈ rows →
      fixB (xP w U S) p bs = true → movB (xP w U S) bs = true → witB w U S e bs OG = true
  | [], _, _, _, _, hr, _, _ => absurd hr List.not_mem_nil
  | (p', e', OG') :: rows, h, p, e, OG, hr, hf, hm => by
    change Bool.rec (motive := fun _ => Bool) false (rowsB w U S bs rows)
      (bIf(bAnd(fixB (xP w U S) p' bs, movB (xP w U S) bs), witB w U S e' bs OG', true)) =
        true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hr with e1 | hr
    · cases e1
      rw [hf, hm] at h1
      exact h1
    · exact rowsB_mem h2 hr hf hm

theorem exists_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, ha => absurd ha List.not_mem_nil
  | _, _, .cons hab hr, _, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := exists_of_forall₂ hr ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem pow_ne_of_movB {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (hf : ∀ x : Fin n, f x = g x)
    {bs : List Nat} (hlt : ∀ b ∈ bs, b < n) {e : Nat} (h : movB (itP f e) bs = true) :
    g ^ e ≠ 1 := by
  obtain ⟨b, hb, hne⟩ := movB_true h
  intro h1
  apply hne
  have := itP_pow hf e ⟨b, hlt b hb⟩
  rw [h1] at this
  exact this

theorem rowsB_sound {Q : RawSchreierDatum n} (hQ : ValidSchreier Q) {bs : List Nat}
    (hbs : ∀ i : Fin Q.baseCount, (Q.base.get i).val ∈ bs) (hlt : ∀ b ∈ bs, b < n)
    {U S : Nat} {u s : Equiv.Perm (Fin n)} (pU : PRep n w U u) (pS : PRep n w S s)
    (hx : u * s ∈ Q.originalSubgroup) {rows : List (Nat × Nat × List (Nat × Nat))}
    (h : rowsB w U S bs rows = true) {p e : Nat} {OG : List (Nat × Nat)} (hr : (p, e, OG) ∈ rows)
    {cs : List (Equiv.Perm (Fin n))}
    (hOG : List.Forall₂ (fun P c => PRep n w P.1 c ∧ PRep n w P.2 c⁻¹) OG cs) (hp : p ≠ 1)
    (ho : orderOf (u * s) = p) :
    (∃ c ∈ cs, (u * s * c * (u * s) * c⁻¹) ^ e ≠ 1) ∨
      ∃ c₁ ∈ cs, ∃ c₂ ∈ cs, (u * s * c₁ * (u * s) * c₁⁻¹ * c₂ * (u * s) * c₂⁻¹) ^ e ≠ 1 := by
  have hxf : ∀ i : Fin n, xP w U S i = (u * s) i := fun i => by
    unfold xP
    rw [pS i, pU (s i), Equiv.Perm.mul_apply]
  have hx1 : (u * s) ^ p = 1 := by
    rw [← ho]
    exact pow_orderOf_eq_one _
  have hfix : fixB (xP w U S) p bs = true := fixB_of fun b hb => by
    have := itP_pow hxf p ⟨b, hlt b hb⟩
    rw [hx1] at this
    exact this
  have hmov : movB (xP w U S) bs = true := by
    refine movB_of ?_
    by_contra hc
    push Not at hc
    have h1 : u * s = 1 := RawSchreierDatum.eq_one_of_fixes_base Q hQ hx fun i => by
      apply Fin.ext
      rw [← hxf]
      exact hc _ (hbs i)
    rw [h1, orderOf_one] at ho
    exact hp ho.symm
  rcases witB_true (rowsB_mem h hr hfix hmov) with ⟨c, hc, hm⟩ | ⟨c₁, hc₁, c₂, hc₂, hm⟩
  · obtain ⟨g, hg, pg1, pg2⟩ := exists_of_forall₂ hOG hc
    refine Or.inl ⟨g, hg, pow_ne_of_movB (fun i => ?_) hlt hm⟩
    unfold y1P
    rw [pg2 i, hxf, pg1, hxf]
    simp only [Equiv.Perm.mul_apply]
  · obtain ⟨g₁, hg₁, p11, p12⟩ := exists_of_forall₂ hOG hc₁
    obtain ⟨g₂, hg₂, p21, p22⟩ := exists_of_forall₂ hOG hc₂
    refine Or.inr ⟨g₁, hg₁, g₂, hg₂, pow_ne_of_movB (fun i => ?_) hlt hm⟩
    unfold y2P y1P
    rw [p22 i, hxf, p21, p12, hxf, p11, hxf]
    simp only [Equiv.Perm.mul_apply]

theorem candB_spec {U : Nat} {bs : List Nat} {rows : List (Nat × Nat × List (Nat × Nat))}
    {T : Nat → Nat} {cnt b len : Nat} (h : candB w U bs rows T cnt b len = true) :
    ∀ k, b ≤ k → k < b + len → k < cnt → rowsB w U (T k) bs rows = true := by
  intro k h1 h2 h3
  have h' := allBlk_spec h (k - b) (by omega)
  have e : Nat.add b (k - b) = k := by
    change b + (k - b) = k
    omega
  rw [e] at h'
  have hb : Nat.blt k cnt = true := by
    rw [Nat.blt_eq]
    exact h3
  change Bool.rec (motive := fun _ => Bool) true (rowsB w U (T k) bs rows) (Nat.blt k cnt) =
    true at h'
  rw [hb] at h'
  exact h'

theorem penum_conj_closed (hsz : szOK n w = true) {k cnt cap X : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} {gs : Nat → Equiv.Perm (Fin n)}
    (hG : ∀ j < k, PRep n w (G j) (gs j) ∧ PRep n w (GI j) (gs j)⁻¹)
    (hh : penumHdK X cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    {r : Equiv.Perm (Fin n)} (pX : PRep n w X r) :
    ∀ h ∈ Subgroup.closure (Set.range fun j : Fin k => gs j),
      ∃ i < cnt, PRep n w (T i) (h * r * h⁻¹) := by
  have hn : n < 2 ^ 32 := by
    have := (szOK_facts hsz).1
    omega
  set S : Set (Equiv.Perm (Fin n)) := {y | ∃ i < cnt, PRep n w (T i) y} with hS
  have hgen : ∀ j < k, ∀ y ∈ S, gs j * y * (gs j)⁻¹ ∈ S := by
    rintro j hj y ⟨i, hi, py⟩
    obtain ⟨hq, hT, -⟩ := (penumPt_specH (hp i hi)).2.2.1 j hj
    refine ⟨_, hq, ?_⟩
    rw [hT]
    exact prep_pcomp hn (prep_pcomp hn (hG j hj).1 py) (hG j hj).2
  have hcl : ∀ h ∈ Subgroup.closure (Set.range fun j : Fin k => gs j),
      ∀ y ∈ S, h * y * h⁻¹ ∈ S := by
    intro h hh'
    induction hh' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hgen j j.2
    | one => simp
    | mul a b _ _ ha hb =>
      intro y hy
      have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      have hm : Set.MapsTo (fun z => a * z * a⁻¹) S S := fun z hz => ha z hz
      have hi : Set.InjOn (fun z => a * z * a⁻¹) S := fun z₁ _ z₂ _ e => by
        simpa using e
      obtain ⟨z, hz, e⟩ := ((S.toFinite.injOn_iff_bijOn_of_mapsTo hm).1 hi).surjOn hy
      have e' : a⁻¹ * y * a⁻¹⁻¹ = z := by
        rw [← e]
        group
      rw [e']
      exact hz
  have hd : Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (Nat.beq (r32 PL 0) 0) (Nat.beq (T 0) X))
        (Nat.ble cnt cap)) (Nat.blt 0 cnt) = true := hh
  obtain ⟨h0, h1⟩ := (bAnd_iff _ _).1 hd
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨h3, -⟩ := (bAnd_iff _ _).1 h2
  have h0' : 0 < cnt := by
    rw [Nat.blt_eq] at h0
    exact h0
  have hrS : r ∈ S := ⟨0, h0', by rw [Nat.eq_of_beq_eq_true h3]; exact pX⟩
  intro h hh'
  exact hcl h hh' r hrS

theorem forall₂_getD {α β : Type*} {R : α → β → Prop} {d₁ : α} {d₂ : β} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat}, i < l₂.length →
      R (l₁.getD i d₁) (l₂.getD i d₂)
  | _, _, .nil, _, hi => absurd hi (Nat.not_lt_zero _)
  | _, _, .cons hab _, 0, _ => hab
  | _, _, .cons _ hr, i + 1, hi => forall₂_getD hr (by simpa using hi)

theorem prep_wordK (hsz : szOK n w = true) {gP gIP : List Nat} {gs : List (Equiv.Perm (Fin n))}
    (h1 : List.Forall₂ (PRep n w) gP gs) (h2 : List.Forall₂ (PRep n w) gIP (gs.map fun g => g⁻¹)) :
    ∀ {wd : List ℤ}, (∀ z ∈ wd, (if 0 < z then z.toNat - 1 else (-z).toNat - 1) < gs.length) →
      PRep n w (wordK n w gP gIP wd) (evalCodes gs wd)
  | [], _ => prep_pidn (szOK_facts hsz).1 (szOK_facts hsz).2
  | z :: wd, hwd => by
    have hn : n < 2 ^ 32 := by
      have := (szOK_facts hsz).1
      omega
    have ih := prep_wordK hsz h1 h2 (wd := wd) fun z' hz' => hwd z' (List.mem_cons_of_mem _ hz')
    have hz := hwd z List.mem_cons_self
    change PRep n w (pcomp n w (mask w)
      (if 0 < z then gP.getD (z.toNat - 1) 0 else gIP.getD ((-z).toNat - 1) 0)
      (wordK n w gP gIP wd))
      ((if 0 < z then gs.getD (z.toNat - 1) 1 else (gs.getD ((-z).toNat - 1) 1)⁻¹) *
        evalCodes gs wd)
    refine prep_pcomp hn ?_ ih
    by_cases hp : 0 < z
    · rw [if_pos hp] at hz
      rw [if_pos hp, if_pos hp]
      exact forall₂_getD h1 hz
    · rw [if_neg hp] at hz
      rw [if_neg hp, if_neg hp]
      have e : (gs.map fun g => g⁻¹).getD ((-z).toNat - 1) 1 = (gs.getD ((-z).toNat - 1) 1)⁻¹ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hz), List.getD_eq_getElem _ _ hz,
          List.getElem_map]
      rw [← e]
      exact forall₂_getD h2 (by simpa using hz)

theorem witnessOKT_of (hn : n < 2 ^ 32) {og : List Table} {cs : List (Equiv.Perm (Fin n))}
    (hog : List.Forall₂ (Rep n) og cs) {T : Table} {x : Equiv.Perm (Fin n)} (hT : Rep n T x)
    {e : Nat} (h : (∃ c ∈ cs, (x * c * x * c⁻¹) ^ e ≠ 1) ∨
      ∃ c₁ ∈ cs, ∃ c₂ ∈ cs, (x * c₁ * x * c₁⁻¹ * c₂ * x * c₂⁻¹) ^ e ≠ 1) :
    witnessOK n e (og.map fun g => (g, invT n g)) T = true := by
  have hpw : ∀ (ws : List Table) (gs : List (Equiv.Perm (Fin n))), List.Forall₂ (Rep n) ws gs →
      gs.prod ^ e ≠ 1 → (!powFixW n ws e) = true := by
    intro ws gs hr hne
    rw [Bool.not_eq_true', ← Bool.not_eq_true, powFixW_iff perm_faithful hr e]
    exact hne
  have hrev : ∀ c ∈ cs, ∃ g ∈ og, Rep n g c := by
    intro c hc
    exact exists_of_mem_right_forall₂ hog hc
  unfold witnessOK
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
  rcases h with ⟨c, hc, hne⟩ | ⟨c₁, hc₁, c₂, hc₂, hne⟩
  · obtain ⟨g, hg, pg⟩ := hrev c hc
    refine Or.inl ⟨(g, invT n g), List.mem_map.2 ⟨g, hg, rfl⟩, ?_⟩
    refine hpw _ [x, c, x, c⁻¹]
      (.cons hT (.cons pg (.cons hT (.cons (CFSG.KS.Tbl.invT_rep hn pg) .nil)))) ?_
    simpa [List.prod_cons, mul_assoc] using hne
  · obtain ⟨g₁, hg₁, p₁⟩ := hrev c₁ hc₁
    obtain ⟨g₂, hg₂, p₂⟩ := hrev c₂ hc₂
    refine Or.inr ⟨(g₁, invT n g₁), List.mem_map.2 ⟨g₁, hg₁, rfl⟩, ?_⟩
    rw [List.any_eq_true]
    refine ⟨(g₂, invT n g₂), List.mem_map.2 ⟨g₂, hg₂, rfl⟩, ?_⟩
    refine hpw _ [x, c₁, x, c₁⁻¹, c₂, x, c₂⁻¹]
      (.cons hT (.cons p₁ (.cons hT (.cons (CFSG.KS.Tbl.invT_rep hn p₁) (.cons p₂ (.cons hT
        (.cons (CFSG.KS.Tbl.invT_rep hn p₂) .nil))))))) ?_
    simpa [List.prod_cons, mul_assoc] using hne

theorem rowOKT_of (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {Tss : List (List Table)} (hTss : levelTables Q = Tss) {NG : Nat} {gT : List Table}
    {gs : List (Equiv.Perm (Fin n))} (hgT : List.Forall₂ (Rep n) gT gs) {uT : Table}
    {u : Equiv.Perm (Fin n)} (hu : Rep n uT u) (hu2 : u * u = 1)
    (hcomm : ∀ g ∈ gs, u * g = g * u) (r : Row) (hp : 0 < r.prime) (hodd : r.oddExp % 2 = 1)
    (hNG : NG % r.prime ^ (r.pexp + 1) ≠ 0)
    (hpow : ∀ c ∈ r.oddWords.map (evalCodes gs), c ^ r.oddExp = 1)
    (hcand : ∀ x ∈ Q.originalSubgroup, (u * x) * (u * x) = 1 → orderOf x = r.prime →
      (∃ c ∈ r.oddWords.map (evalCodes gs), (x * c * x * c⁻¹) ^ (r.prime ^ r.pexp) ≠ 1) ∨
      ∃ c₁ ∈ r.oddWords.map (evalCodes gs), ∃ c₂ ∈ r.oddWords.map (evalCodes gs),
        (x * c₁ * x * c₁⁻¹ * c₂ * x * c₂⁻¹) ^ (r.prime ^ r.pexp) ≠ 1) :
    rowOKT n NG gT uT (candAllT n Tss uT) r = true := by
  have hgI : List.Forall₂ (Rep n) (gT.map (invT n)) (gs.map fun g => g⁻¹) :=
    List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (hgT.imp fun _ _ h => CFSG.KS.Tbl.invT_rep hn h))
  have hog : List.Forall₂ (Rep n) (r.oddWords.map (evalT n gT (gT.map (invT n))))
      (r.oddWords.map (evalCodes gs)) :=
    List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun wd _ => rep_evalT hn hgT hgI wd))
  unfold rowOKT
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, hodd⟩, hNG⟩, fun g hg => ?_⟩, fun g hg => ?_⟩, fun T hT => ?_⟩
  · rw [tblEq_eq_iff (Rep.compT hu hu) (Rep.idT hn)]
    exact hu2
  · obtain ⟨c, hc, pc⟩ := exists_of_mem_left_forall₂ hgT hg
    refine ⟨CFSG.KS.Tbl.invOK_invT hn pc, ?_⟩
    rw [CFSG.KS.SporSch.MOC.commT_eq hu pc, decide_eq_true_eq]
    exact hcomm c hc
  · obtain ⟨c, hc, pc⟩ := exists_of_mem_left_forall₂ hog hg
    refine ⟨CFSG.KS.Tbl.invOK_invT hn pc, ?_⟩
    rw [powFixW_iff perm_faithful (List.Forall₂.cons pc List.Forall₂.nil)]
    simpa using hpow c hc
  · obtain ⟨x, hx, hTx⟩ := exists_of_mem_left_forall₂ (forall₂_candAllT hn Q hTss hu) hT
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff _ hQ] at hx
    obtain ⟨hxG, hsq⟩ := hx
    rw [Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, ordTest_iff perm_faithful hTx hp]
    by_cases hxo : orderOf x = r.prime
    · exact Or.inr (witnessOKT_of hn hog hTx (hcand x hxG hsq hxo))
    · exact Or.inl hxo

end CFSG.KS.SporSch.BPW

end
