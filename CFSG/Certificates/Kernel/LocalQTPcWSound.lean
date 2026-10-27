module

public import Certificates.Data.Kernel.LocalQT.PcW
public import Certificates.Data.Kernel.LocalQT.BaseT
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeCnt

public section

namespace CFSG.KC.LQT.PcW

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KS.Prim
open CFSG.QuasithinUnique.Ch1.SporLat (idTab powTab QuotGen quotGt quotGi wordTabA wordImg ptAct
  sortN powTab_size)
open CFSG.QuasithinUnique.K1.SporadicPerm (compArr slpTabsA slpStepA slpValidAux)
open CFSG.QuasithinUnique.Vol2Native.L239 (CntOk Wit3Ok WitPOk commTab commOf rijTab)

def Rep (n w c : Nat) (t : Array Nat) : Prop :=
  t.size = n ∧ (∀ i < n, t[i]! = pg w (mask w) c i) ∧ c >>> (n * w) = 0 ∧
    ∀ i < n, pg w (mask w) c i < n

section Rep

variable {n w : Nat}

theorem rep_get {c : Nat} {t : Array Nat} (h : Rep n w c t) : ∀ i < n, t[i]! = pg w (mask w) c i :=
  h.2.1

theorem pcS_eq (n w m p q : Nat) : pcS n w m p q = pcomp n w m p q := by
  unfold pcS
  rw [strictN_eqP, strictN_eqP]

theorem powS_zero (n w m idn p : Nat) : powS n w m idn p 0 = idn := by
  unfold powS
  rw [strictN_eqP]
  rfl

theorem powS_succ (n w m idn p k : Nat) :
    powS n w m idn p (k + 1) = pcS n w m p (powS n w m idn p k) := by
  unfold powS
  rw [strictN_eqP, strictN_eqP]

theorem rep_comp (hn : n < 2 ^ 32) (hw : 0 < w) {c d : Nat} {s t : Array Nat}
    (hc : Rep n w c s) (hd : Rep n w d t) :
    Rep n w (pcS n w (mask w) c d) (compArr s t) := by
  rw [pcS_eq]
  obtain ⟨hs1, hs2, -, hs4⟩ := hc
  obtain ⟨ht1, ht2, -, ht4⟩ := hd
  refine ⟨by simp [compArr, ht1], fun i hi => ?_, pcomp_shr c d hn hw, fun i hi => ?_⟩
  · have hi' : i < t.size := by omega
    rw [compArr, getElem!_pos _ i (by simpa using hi'), Array.getElem_map,
      ← getElem!_pos t i hi', ht2 i hi, hs2 _ (ht4 i hi), pg_pcomp hn hi]
  · rw [pg_pcomp hn hi]
    exact hs4 _ (ht4 i hi)

theorem rep_id (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : Rep n w (pidn n w) (idTab n) := by
  refine ⟨by simp [idTab], fun i hi => ?_, pidn_shr hn hw, fun i hi => ?_⟩
  · rw [pg_pidn hn hw hi, idTab, getElem!_pos _ i (by simpa using hi), Array.getElem_range]
  · rw [pg_pidn hn hw hi]
    exact hi

theorem rep_pow (hn : n < 2 ^ 32) (hw : 0 < w) {idn c : Nat} {t : Array Nat}
    (hid : Rep n w idn (idTab n)) (hc : Rep n w c t) :
    ∀ k, Rep n w (powS n w (mask w) idn c k) (powTab n t k)
  | 0 => by
    rw [powS_zero]
    exact hid
  | k + 1 => by
    rw [powS_succ]
    exact rep_comp hn hw hc (rep_pow hn hw hid hc k)

theorem rep_word (hn : n < 2 ^ 32) (hw : 0 < w) {tabs : Array (Array Nat)} {L : Nat → Nat}
    {b : Nat} {tb : Array Nat} (hb : Rep n w b tb) :
    ∀ (ws : List Nat), (∀ l ∈ ws, Rep n w (L l) (tabs.getD l #[])) →
      Rep n w (wordPB n w (mask w) L ws b) (ws.foldr (fun l acc => compArr (tabs.getD l #[]) acc) tb)
  | [], _ => hb
  | l :: ws, h => by
    have e : wordPB n w (mask w) L (l :: ws) b = pcS n w (mask w) (L l) (wordPB n w (mask w) L ws b) :=
      rfl
    rw [e, List.foldr_cons]
    exact rep_comp hn hw (h l (by simp)) (rep_word hn hw hb ws (fun l' hl' => h l' (by simp [hl'])))

theorem wordTabA_foldr (tabs : Array (Array Nat)) (n : Nat) :
    ∀ ws : List Nat,
      wordTabA tabs n ws = ws.foldr (fun l acc => compArr (tabs.getD l #[]) acc) (idTab n)
  | [] => by
    have e : wordImg tabs [] = fun p => p := rfl
    rw [wordTabA, e, List.foldr_nil, idTab]
    simp
  | l :: ws => by
    rw [List.foldr_cons, ← wordTabA_foldr tabs n ws]
    unfold wordTabA compArr
    rw [Array.map_map]
    congr 1

theorem rep_inj (hw : 0 < w) {c d : Nat} {s t : Array Nat} (hc : Rep n w c s) (hd : Rep n w d t)
    (h : s = t) : c = d := by
  refine eq_of_fields hw hc.2.2.1 hd.2.2.1 (fun i hi => ?_)
  rw [← hc.2.1 i hi, ← hd.2.1 i hi, h]

theorem rep_eq {c d : Nat} {s t : Array Nat} (hc : Rep n w c s) (hd : Rep n w d t) (h : c = d) :
    s = t := by
  subst h
  apply Array.ext (by rw [hc.1, hd.1])
  intro i h1 h2
  have hi : i < n := by rw [← hc.1]; exact h1
  rw [← getElem!_pos s i h1, ← getElem!_pos t i h2, hc.2.1 i hi, hd.2.1 i hi]

theorem rep_ne (hw : 0 < w) {c d : Nat} {s t : Array Nat} (hc : Rep n w c s) (hd : Rep n w d t)
    (h : c ≠ d) : s ≠ t := fun e => h (rep_inj hw hc hd e)

theorem rep_qt (hn : n < 2 ^ 32) (hw : 0 < w) {idn : Nat} (hid : Rep n w idn (idTab n))
    {L : List (Array Nat)} {Lc : Nat → Nat} (x : QuotGen)
    (hL : ∀ l ∈ x.w, Rep n w (Lc l) (L.toArray.getD l #[])) :
    Rep n w (qtW n w (mask w) idn Lc x.w x.k) (quotGt n L x) := by
  unfold qtW quotGt
  rw [wordTabA_foldr]
  exact rep_pow hn hw hid (rep_word hn hw hid x.w hL) x.k

theorem rep_qi (hn : n < 2 ^ 32) (hw : 0 < w) {idn : Nat} (hid : Rep n w idn (idTab n))
    {L : List (Array Nat)} {Lc : Nat → Nat} (x : QuotGen)
    (hL : ∀ l ∈ x.w, Rep n w (Lc l) (L.toArray.getD l #[])) :
    Rep n w (powS n w (mask w) idn (qtW n w (mask w) idn Lc x.w x.k) (x.m - 1)) (quotGi n L x) :=
  rep_pow hn hw hid (rep_qt hn hw hid x hL) (x.m - 1)

theorem rep_rij (hn : n < 2 ^ 32) (hw : 0 < w) {idn c₁ c₂ : Nat} {t₁ t₂ : Array Nat}
    (hid : Rep n w idn (idTab n)) (h₁ : Rep n w c₁ t₁) (h₂ : Rep n w c₂ t₂) (i j : Nat) :
    Rep n w (rijS n w (mask w) idn c₁ c₂ i j) (rijTab n t₁ t₂ i j) :=
  rep_comp hn hw (rep_pow hn hw hid h₁ i) (rep_pow hn hw hid h₂ j)

theorem rep_comm (hn : n < 2 ^ 32) (hw : 0 < w) {a b c d : Nat} {A B C D : Array Nat}
    (ha : Rep n w a A) (hb : Rep n w b B) (hc : Rep n w c C) (hd : Rep n w d D) :
    Rep n w (commS n w (mask w) a b c d) (commTab A B C D) :=
  rep_comp hn hw (rep_comp hn hw (rep_comp hn hw ha hb) hc) hd

end Rep

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true :=
  (bAnd_iff a b).1 h

theorem ne_of_bIf {a b : Nat} (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b) = true) :
    a ≠ b := by
  intro e
  subst e
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem ne_of_neB {a b : Nat} (h : neB a b = true) : a ≠ b :=
  ne_of_bIf h

theorem memK_spec {v : Nat} : ∀ {l : List Nat}, memK v l = true → v ∈ l
  | [], h => Bool.noConfusion h
  | a :: l, h => by
    have e : memK v (a :: l) = Bool.rec (motive := fun _ => Bool) (memK v l) true (Nat.beq v a) := rfl
    rw [e] at h
    cases hb : Nat.beq v a
    · rw [hb] at h
      exact List.mem_cons_of_mem a (memK_spec h)
    · rw [Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self

theorem not_memK {v : Nat} {l : List Nat} (h : Bool.rec (motive := fun _ => Bool) true false (memK v l) = true) :
    memK v l = false := by
  cases hm : memK v l
  · rfl
  · rw [hm] at h
    exact absurd h Bool.false_ne_true

theorem memK_false {v : Nat} : ∀ {l : List Nat}, memK v l = false → v ∉ l
  | [], _ => List.not_mem_nil
  | a :: l, h => by
    have e : memK v (a :: l) = Bool.rec (motive := fun _ => Bool) (memK v l) true (Nat.beq v a) := rfl
    rw [e] at h
    cases hb : Nat.beq v a
    · rw [hb] at h
      intro hv
      rcases List.mem_cons.1 hv with hv | hv
      · subst hv
        rw [Nat.beq_refl] at hb
        exact Bool.false_ne_true hb.symm
      · exact memK_false h hv
    · rw [hb] at h
      exact Bool.noConfusion h

theorem distF_spec : ∀ {l acc : List Nat}, distF l acc = true → l.Nodup ∧ ∀ a ∈ l, a ∉ acc
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, acc, h => by
    have e : distF (x :: l) acc = strictB x (fun v =>
        Bool.rec (motive := fun _ => Bool) false (distF l (v :: acc))
          (Bool.rec (motive := fun _ => Bool) true false (memK v acc))) := rfl
    rw [e, strictB_eqP] at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    have hx := memK_false (not_memK h1)
    obtain ⟨hn, ha⟩ := distF_spec h2
    refine ⟨List.nodup_cons.2 ⟨fun hm => ha x hm List.mem_cons_self, hn⟩, fun a ham => ?_⟩
    rcases List.mem_cons.1 ham with rfl | ham
    · exact hx
    · exact fun hacc => ha a ham (List.mem_cons_of_mem x hacc)

theorem allL_spec {α : Type} {f : α → Bool} : ∀ {l : List α}, allL l f = true → ∀ x ∈ l, f x = true
  | [], _, _, hx => absurd hx List.not_mem_nil
  | a :: l, h, x, hx => by
    have e : allL (a :: l) f = Bool.rec (motive := fun _ => Bool) false (allL l f) (f a) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact allL_spec h2 x hx

theorem sortK_spec : ∀ {l : List Nat} {lb : Nat}, sortK l lb = true →
    (∀ a ∈ l, lb ≤ a) ∧ l.Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | a :: l, lb, h => by
    have e : sortK (a :: l) lb = Bool.rec (motive := fun _ => Bool) false (sortK l (Nat.succ a))
        (Nat.ble lb a) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    have hle : lb ≤ a := Nat.le_of_ble_eq_true h1
    obtain ⟨hl, hp⟩ := sortK_spec h2
    refine ⟨fun b hb => ?_, List.pairwise_cons.2 ⟨fun b hb => hl b hb, hp⟩⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hle
    · have := hl b hb
      omega

theorem imgsK_eq (w m c : Nat) : ∀ l : List Nat, imgsK w m c l = l.map (pg w m c)
  | [] => rfl
  | x :: l => by
    have e : imgsK w m c (x :: l) = pg w m c x :: imgsK w m c l := rfl
    rw [e, imgsK_eq w m c l, List.map_cons]

theorem labK_spec {n w c : Nat} {t : Array Nat} {x : List Nat} (hc : Rep n w c t)
    (h : labK n w (mask w) c x = true) : ptAct t x = x := by
  obtain ⟨h1, h23⟩ := bAnd_true h
  obtain ⟨h2, h3⟩ := bAnd_true h23
  obtain ⟨-, hsort⟩ := sortK_spec h1
  have hall := allL_spec h2
  rw [imgsK_eq] at h3
  have hnd := (distF_spec h3).1
  have hlt : ∀ p ∈ x, p < n ∧ pg w (mask w) c p ∈ x := fun p hp => by
    obtain ⟨a, b⟩ := bAnd_true (hall p hp)
    exact ⟨by simpa [Nat.blt_eq] using a, memK_spec b⟩
  have hmap : x.map (fun p => t.getD p 0) = x.map (pg w (mask w) c) := by
    apply List.map_congr_left
    intro p hp
    rw [← hc.2.1 p (hlt p hp).1, Array.getElem!_eq_getD]
    rfl
  have hsub : x.map (pg w (mask w) c) ⊆ x := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    exact (hlt p hp).2
  have hperm : List.Perm (x.map (pg w (mask w) c)) x :=
    (hnd.subperm hsub).perm_of_length_le (by simp)
  unfold ptAct sortN
  rw [hmap]
  have hs1 := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (x.map (pg w (mask w) c))
  refine List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
    (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) (hs1.imp fun hab => by simpa using hab)
    (hsort.imp fun hab => Nat.le_of_lt hab) ((List.mergeSort_perm _ _).trans hperm)

theorem labsK_spec {n w c : Nat} {t : Array Nat} {xs : List (List Nat)} (hc : Rep n w c t)
    (h : labsK n w (mask w) c xs = true) : ∀ x ∈ xs, ptAct t x = x := by
  unfold labsK at h
  rw [strictB_eqP] at h
  exact fun x hx => labK_spec hc (allL_spec h x hx)

theorem nodup_of_rep {n w : Nat} (hw : 0 < w) {α : Type} {l : List α} {f : α → Nat}
    {g : α → Array Nat} (hr : ∀ a ∈ l, Rep n w (f a) (g a)) (h : (l.map f).Nodup) :
    (l.map g).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨fun hm => h.1 ?_, ih (fun b hb => hr b (List.mem_cons_of_mem a hb)) h.2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    rw [← rep_inj hw (hr b (List.mem_cons_of_mem a hb)) (hr a List.mem_cons_self) e]
    exact List.mem_map_of_mem hb

theorem getD_toArray {L : List (Array Nat)} {l : Nat} (hl : l < L.length) :
    L.toArray.getD l #[] = L[l]! := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, getElem!_pos L l hl,
    List.getElem?_eq_getElem hl, Option.getD_some]

section Wit

variable {n w m idn len : Nat} {Lc : Nat → Nat} {L : List (Array Nat)}

theorem cntOk_of_cp (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hm : m = mask w)
    (hid : Rep n w idn (idTab n)) (hlen : L.length = len)
    (hL : ∀ l < len, Rep n w (Lc l) L[l]!) {lbls : List (List Nat)}
    {r₁ r₂ : QuotGen} {qs : List QuotGen} {t₁ t₂ : Nat}
    (hw₁ : ∀ l ∈ r₁.w, l < len) (hw₂ : ∀ l ∈ r₂.w, l < len)
    (ht₁ : qtW n w m idn Lc r₁.w r₁.k = t₁) (ht₂ : qtW n w m idn Lc r₂.w r₂.k = t₂)
    (h1 : t₁ ≠ idn) (h2 : t₂ ≠ idn) (h3 : powS n w m idn t₁ 3 = idn)
    (h4 : powS n w m idn t₂ 3 = idn) (h5 : pcS n w m t₁ t₂ = pcS n w m t₂ t₁) (h6 : t₂ ≠ t₁)
    (h7 : t₂ ≠ powS n w m idn t₁ 2) (h8 : 4 < qs.length)
    (hq : ∀ q ∈ qs, (∀ l ∈ q.w, l < len) ∧ 0 < q.m ∧
      powS n w m idn (qtW n w m idn Lc q.w q.k) q.m = idn ∧
      labsK n w m (qtW n w m idn Lc q.w q.k) lbls = true)
    (hc : ∀ i < 3, ∀ j < 3, (i ≠ 0 ∨ j ≠ 0) →
      (qs.map fun q => commS n w m (qtW n w m idn Lc q.w q.k) (rijS n w m idn t₁ t₂ i j)
        (powS n w m idn (qtW n w m idn Lc q.w q.k) (q.m - 1))
        (powS n w m idn (rijS n w m idn t₁ t₂ i j) 2)).Nodup) :
    CntOk n ptAct L lbls r₁ r₂ qs := by
  subst hm
  have h32 : n < 2 ^ 32 := by omega
  have hw0 := w_pos hw
  have hL' : ∀ x : QuotGen, (∀ l ∈ x.w, l < len) →
      ∀ l ∈ x.w, Rep n w (Lc l) (L.toArray.getD l #[]) := fun x hx l hl => by
    rw [getD_toArray (by rw [hlen]; exact hx l hl)]
    exact hL l (hx l hl)
  have hr₁ := rep_qt h32 hw0 hid r₁ (hL' r₁ hw₁)
  have hr₂ := rep_qt h32 hw0 hid r₂ (hL' r₂ hw₂)
  rw [ht₁] at hr₁
  rw [ht₂] at hr₂
  have hp : ∀ {c : Nat} {t : Array Nat}, Rep n w c t → ∀ k, powS n w (mask w) idn c k = idn →
      powTab n t k = idTab n := fun hc k e => rep_eq (rep_pow h32 hw0 hid hc k) hid e
  refine ⟨fun l hl => hlen ▸ hw₁ l hl, fun l hl => hlen ▸ hw₂ l hl, rep_ne hw0 hr₁ hid h1,
    rep_ne hw0 hr₂ hid h2, hp hr₁ 3 h3, hp hr₂ 3 h4, ?_, rep_ne hw0 hr₂ hr₁ h6,
    rep_ne hw0 hr₂ (rep_pow h32 hw0 hid hr₁ 2) h7, h8, fun q hqm => ?_, ?_⟩
  · exact rep_eq (rep_comp h32 hw0 hr₁ hr₂) (rep_comp h32 hw0 hr₂ hr₁) h5
  · obtain ⟨hqw, hqm', hqp, hql⟩ := hq q hqm
    have hrq := rep_qt h32 hw0 hid q (hL' q hqw)
    exact ⟨fun l hl => hlen ▸ hqw l hl, hqm', hp hrq q.m hqp, labsK_spec hrq hql⟩
  · intro i hi j hj hij
    have hx := rep_rij h32 hw0 hid hr₁ hr₂ i j
    refine nodup_of_rep (n := n) hw0 (fun q hqm => ?_) (hc i hi j hj hij)
    obtain ⟨hqw, -, -, -⟩ := hq q hqm
    exact rep_comm h32 hw0 (rep_qt h32 hw0 hid q (hL' q hqw)) hx (rep_qi h32 hw0 hid q (hL' q hqw))
      (rep_pow h32 hw0 hid hx 2)

theorem wit3Ok_of_cp (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hm : m = mask w)
    (hid : Rep n w idn (idTab n)) (hlen : L.length = len)
    (hL : ∀ l < len, Rep n w (Lc l) L[l]!) {lbls : List (List Nat)}
    {b q₁ q₂ : QuotGen} {tb c₁ c₂ : Nat}
    (hlet : ∀ x ∈ [b, q₁, q₂], (∀ l ∈ x.w, l < len) ∧ 0 < x.m) (hbm : b.m = 3)
    (htb : qtW n w m idn Lc b.w b.k = tb) (h1 : tb ≠ idn) (h2 : powS n w m idn tb 3 = idn)
    (hq : ∀ q ∈ [q₁, q₂], powS n w m idn (qtW n w m idn Lc q.w q.k) q.m = idn ∧
      labsK n w m (qtW n w m idn Lc q.w q.k) lbls = true)
    (hc₁ : commS n w m (qtW n w m idn Lc q₁.w q₁.k) tb
      (powS n w m idn (qtW n w m idn Lc q₁.w q₁.k) (q₁.m - 1)) (powS n w m idn tb (b.m - 1)) = c₁)
    (hc₂ : commS n w m (qtW n w m idn Lc q₂.w q₂.k) tb
      (powS n w m idn (qtW n w m idn Lc q₂.w q₂.k) (q₂.m - 1)) (powS n w m idn tb (b.m - 1)) = c₂)
    (h3 : pcS n w m c₁ c₂ ≠ pcS n w m c₂ c₁ ∨ pcS n w m c₁ c₁ ≠ idn) :
    Wit3Ok n ptAct L lbls b q₁ q₂ := by
  subst hm
  have h32 : n < 2 ^ 32 := by omega
  have hw0 := w_pos hw
  have hL' : ∀ x : QuotGen, (∀ l ∈ x.w, l < len) →
      ∀ l ∈ x.w, Rep n w (Lc l) (L.toArray.getD l #[]) := fun x hx l hl => by
    rw [getD_toArray (by rw [hlen]; exact hx l hl)]
    exact hL l (hx l hl)
  have hwb := (hlet b (by simp)).1
  have hw₁ := (hlet q₁ (by simp)).1
  have hw₂ := (hlet q₂ (by simp)).1
  have hrb := rep_qt h32 hw0 hid b (hL' b hwb)
  have hrbi := rep_qi h32 hw0 hid b (hL' b hwb)
  rw [htb] at hrb hrbi
  have hp : ∀ {c : Nat} {t : Array Nat}, Rep n w c t → ∀ k, powS n w (mask w) idn c k = idn →
      powTab n t k = idTab n := fun hc k e => rep_eq (rep_pow h32 hw0 hid hc k) hid e
  have hC : ∀ (q : QuotGen) (hqw : ∀ l ∈ q.w, l < len) {c : Nat},
      commS n w (mask w) (qtW n w (mask w) idn Lc q.w q.k) tb
        (powS n w (mask w) idn (qtW n w (mask w) idn Lc q.w q.k) (q.m - 1))
        (powS n w (mask w) idn tb (b.m - 1)) = c → Rep n w c (commOf n L q b) := by
    intro q hqw c e
    rw [← e]
    exact rep_comm h32 hw0 (rep_qt h32 hw0 hid q (hL' q hqw)) hrb
      (rep_qi h32 hw0 hid q (hL' q hqw)) hrbi
  have hr₁ := hC q₁ hw₁ hc₁
  have hr₂ := hC q₂ hw₂ hc₂
  refine ⟨fun x hx => ⟨fun l hl => hlen ▸ (hlet x hx).1 l hl, (hlet x hx).2⟩, hbm,
    rep_ne hw0 hrb hid h1, hp hrb 3 h2, fun q hqm => ?_, ?_⟩
  · have hqw := (hlet q (by simp at hqm ⊢; tauto)).1
    have hrq := rep_qt h32 hw0 hid q (hL' q hqw)
    exact ⟨hp hrq q.m (hq q hqm).1, labsK_spec hrq (hq q hqm).2⟩
  · rcases h3 with h3 | h3
    · exact Or.inl (rep_ne hw0 (rep_comp h32 hw0 hr₁ hr₂) (rep_comp h32 hw0 hr₂ hr₁) h3)
    · exact Or.inr (rep_ne hw0 (rep_comp h32 hw0 hr₁ hr₁) hid h3)

theorem witPOk_of_cp (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hm : m = mask w)
    (hid : Rep n w idn (idTab n)) (hlen : L.length = len)
    (hL : ∀ l < len, Rep n w (Lc l) L[l]!) {lbls : List (List Nat)} {p : Nat}
    {b q : QuotGen} {tb tq : Nat}
    (hlet : ∀ x ∈ [b, q], ∀ l ∈ x.w, l < len)
    (htb : qtW n w m idn Lc b.w b.k = tb) (htq : qtW n w m idn Lc q.w q.k = tq)
    (h1 : tb ≠ idn) (h2 : powS n w m idn tb p = idn) (h3 : labsK n w m tq lbls = true)
    (h4 : pcS n w m tq tb ≠ pcS n w m tb tq) :
    WitPOk n ptAct L lbls p b q := by
  subst hm
  have h32 : n < 2 ^ 32 := by omega
  have hw0 := w_pos hw
  have hL' : ∀ x : QuotGen, (∀ l ∈ x.w, l < len) →
      ∀ l ∈ x.w, Rep n w (Lc l) (L.toArray.getD l #[]) := fun x hx l hl => by
    rw [getD_toArray (by rw [hlen]; exact hx l hl)]
    exact hL l (hx l hl)
  have hrb := rep_qt h32 hw0 hid b (hL' b (hlet b (by simp)))
  have hrq := rep_qt h32 hw0 hid q (hL' q (hlet q (by simp)))
  rw [htb] at hrb
  rw [htq] at hrq
  exact ⟨fun x hx l hl => hlen ▸ hlet x hx l hl, rep_ne hw0 hrb hid h1,
    rep_eq (rep_pow h32 hw0 hid hrb p) hid h2, labsK_spec hrq h3,
    rep_ne hw0 (rep_comp h32 hw0 hrq hrb) (rep_comp h32 hw0 hrb hrq) h4⟩

end Wit

theorem lenA_eq {α : Type} : ∀ l : List α, CFSG.KC.LQT.L.lenA l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenA_eq l)

theorem nthP_eq : ∀ (l : List (Nat × Nat)) (i : Nat), CFSG.KC.LQT.PP.nthP l i = l[i]!
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, i + 1 => by
    have e : CFSG.KC.LQT.PP.nthP (x :: l) (i + 1) = CFSG.KC.LQT.PP.nthP l i := rfl
    rw [e, nthP_eq l i]
    simp

theorem allR_spec' {lo len : Nat} {f : Nat → Bool} (h : CFSG.KC.LQT.PP.allR lo len f = true) :
    ∀ j < len, f (lo + j) = true := by
  induction len with
  | zero => intro j hj; omega
  | succ m ih =>
    have e : CFSG.KC.LQT.PP.allR lo (m + 1) f =
        Bool.rec (motive := fun _ => Bool) false (CFSG.KC.LQT.PP.allR lo m f) (f (Nat.add lo m)) :=
      rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h2 j hj
    · exact h1

theorem nodesT_spec {n w : Nat} {prog : List (Nat × Nat)} {TF : Nat → Nat} {lo len j : Nat}
    (h : CFSG.KC.LQT.BT.nodesT n w prog TF lo len = true) (hlo : lo ≤ j) (hj : j < lo + len)
    (h2 : 2 ≤ j) (h3 : j < prog.length + 2) :
    TF j = CFSG.KC.LQT.PW.mulW n w (TF (prog[j - 2]!).1) (TF (prog[j - 2]!).2) := by
  have hf := allR_spec' h (j - lo) (by omega)
  rw [Nat.add_sub_cancel' hlo] at hf
  have e1 : Nat.ble 2 j = true := by
    rw [Nat.ble_eq]
    exact h2
  have e2 : Nat.blt j (Nat.add (CFSG.KC.LQT.L.lenA prog) 2) = true := by
    rw [lenA_eq, Nat.blt_eq]
    exact h3
  change Bool.rec (motive := fun _ => Bool) true
    (Nat.beq (TF j) (CFSG.KC.LQT.PW.mulW n w (TF (CFSG.KC.LQT.PP.nthP prog (Nat.sub j 2)).1)
      (TF (CFSG.KC.LQT.PP.nthP prog (Nat.sub j 2)).2)))
    (Bool.rec (motive := fun _ => Bool) false (Nat.blt j (Nat.add (CFSG.KC.LQT.L.lenA prog) 2))
      (Nat.ble 2 j)) = true at hf
  rw [e1, e2] at hf
  rw [Nat.eq_of_beq_eq_true hf, nthP_eq]
  rfl

theorem slp_rep {n w : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) {ta tb : Array Nat}
    {prog : List (Nat × Nat)} {TF : Nat → Nat} (h0 : Rep n w (TF 0) ta) (h1 : Rep n w (TF 1) tb)
    (hv : slpValidAux prog 2 = true)
    (hnd : ∀ j, 2 ≤ j → j < prog.length + 2 →
      TF j = pcomp n w (mask w) (TF (prog[j - 2]!).1) (TF (prog[j - 2]!).2)) :
    ∀ j < prog.length + 2, Rep n w (TF j) (slpTabsA ta tb prog)[j]! := by
  have key : ∀ (l : List (Nat × Nat)) (k : Nat) (acc : Array (Array Nat)), acc.size = k + 2 →
      (∀ j < k + 2, Rep n w (TF j) acc[j]!) → slpValidAux l (k + 2) = true →
      (∀ i < l.length, TF (k + 2 + i) = pcomp n w (mask w) (TF (l[i]!).1) (TF (l[i]!).2)) →
      (l.foldl slpStepA acc).size = k + 2 + l.length ∧
        ∀ j < k + 2 + l.length, Rep n w (TF j) (l.foldl slpStepA acc)[j]! := by
    intro l
    induction l with
    | nil => intro k acc hs ha _ _; exact ⟨hs, ha⟩
    | cons p l ih =>
      intro k acc hs ha hvl hl
      have hv' := hvl
      rw [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv'
      obtain ⟨⟨hp1, hp2⟩, hv2⟩ := hv'
      have hnew : Rep n w (TF (k + 2)) (compArr acc[p.1]! acc[p.2]!) := by
        have e := hl 0 (by simp)
        simp only [Nat.add_zero, List.getElem!_cons_zero] at e
        rw [e, ← pcS_eq]
        exact rep_comp hn hw (ha p.1 hp1) (ha p.2 hp2)
      have hs' : (slpStepA acc p).size = k + 1 + 2 := by
        simp [slpStepA, hs]
      have ha' : ∀ j < k + 1 + 2, Rep n w (TF j) (slpStepA acc p)[j]! := by
        intro j hj
        unfold slpStepA
        rcases Nat.lt_or_ge j (k + 2) with hjk | hjk
        · rw [getElem!_pos _ j (by simp [hs]; omega), Array.getElem_push_lt (by omega),
            ← getElem!_pos acc j (by omega)]
          exact ha j hjk
        · have e : j = k + 2 := by omega
          subst e
          have e2 : (acc.push (compArr acc[p.1]! acc[p.2]!))[k + 2]! = compArr acc[p.1]! acc[p.2]! := by
            rw [getElem!_pos _ (k + 2) (by simp [hs]), Array.getElem_push]
            simp [hs]
          rw [e2]
          exact hnew
      have hl' : ∀ i < l.length, TF (k + 1 + 2 + i) = pcomp n w (mask w) (TF (l[i]!).1)
          (TF (l[i]!).2) := by
        intro i hi
        have e := hl (i + 1) (by simp; omega)
        rw [List.getElem!_cons_succ] at e
        rw [← e]
        congr 1
        omega
      have hv3 : slpValidAux l (k + 1 + 2) = true := by
        rw [show k + 1 + 2 = k + 2 + 1 by omega]
        exact hv2
      obtain ⟨r1, r2⟩ := ih (k + 1) (slpStepA acc p) hs' ha' hv3 hl'
      rw [List.foldl_cons]
      refine ⟨by rw [r1]; simp; omega, fun j hj => r2 j (by simp at hj; omega)⟩
  intro j hj
  have hacc : ∀ j < 0 + 2, Rep n w (TF j) (#[ta, tb] : Array (Array Nat))[j]! := by
    intro j hj
    rcases j with _ | _ | j
    · exact h0
    · exact h1
    · omega
  have := (key prog 0 #[ta, tb] rfl hacc (by simpa using hv) (fun i hi => by
    have e := hnd (0 + 2 + i) (by omega) (by omega)
    rw [e]
    congr 3 <;> simp)).2 j (by omega)
  exact this

theorem rep_of_canon {n w m nw c : Nat} {F : Nat → Nat} (hm : m = mask w) (hnw : nw = n * w)
    (hc : canonK n w m nw c = true) (hF : allN n (fun i => Nat.beq (pg w m c i) (F i)) = true) :
    Rep n w c ((List.range n).map F).toArray := by
  subst hm hnw
  obtain ⟨-, -, h3, h4⟩ := canon_facts hc
  refine ⟨by simp, fun i hi => ?_, h3, h4⟩
  rw [getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getElem_map,
    List.getElem_range]
  exact (Nat.eq_of_beq_eq_true (allN_spec hF i hi)).symm

end CFSG.KC.LQT.PcW

end
