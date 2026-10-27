module

public import Certificates.Data.Kernel.J4Q.CovTab
public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Sporadic.J4.QTProof

public section

namespace CFSG.KS.J4CovTab

open CFSG.KC.J4Q CFSG.KC.J4Q.CovTab

variable {G : Type*} [Group G]

structure Model (c rm one : ℕ) (Rep : ℕ → G → Prop) : Prop where
  one : Rep one 1
  mul : ∀ {n m : ℕ} {g h : G}, Rep n g → Rep m h → Rep (mulJ c rm n m) (g * h)
  inj : ∀ {n : ℕ} {g h : G}, Rep n g → Rep n h → g = h
  fn : ∀ {n m : ℕ} {g : G}, Rep n g → Rep m g → n = m

@[expose] def tab (p1 p2 : G) (i : ℕ) : G :=
  p1 ^ (i / 9) * p2 ^ (i / 3 % 3) * (p1 * p2 * p1 ^ 2 * p2 ^ 2) ^ (i % 3)

@[expose] def cjM (cj : List (List ℕ)) (j : ℕ) : ℕ := (cj.getD j []).getD 0 0

structure Facts (Rep : ℕ → G → Prop) (gs : ℕ → G) (rm r : ℕ) (cj cw : List (List ℕ))
    (fu : List ℕ) (p1 p2 g1 g2 t : G) : Prop where
  p3 : p1 ^ 3 = 1
  clos1 : ∀ k < 27, ∃ l < 27, tab p1 p2 k * p1 = tab p1 p2 l
  clos2 : ∀ k < 27, ∃ l < 27, tab p1 p2 k * p2 = tab p1 p2 l
  dist : ∀ k < 27, ∀ k' < k, tab p1 p2 k' ≠ tab p1 p2 k
  cj0 : 0 < cj.length ∧ cjM cj 0 = 18
  conj : ∀ j < cj.length, cjM cj j < 27 ∧ ∃ c : G, c * tab p1 p2 (cjM cj j) = p1 * c
  wit : ∀ k, 0 < k → k < 27 → ∃ u < 27, ∃ j < cj.length,
    tab p1 p2 u * tab p1 p2 k = tab p1 p2 (cjM cj j) * tab p1 p2 u ∨
      tab p1 p2 (cjM cj j) * tab p1 p2 u * tab p1 p2 k = tab p1 p2 u
  fu1 : fu.getD 0 0 < 27 ∧ p1 * g1 = g1 * tab p1 p2 (fu.getD 0 0)
  fu2 : fu.getD 1 0 < 27 ∧ p1 * g2 = g2 * tab p1 p2 (fu.getD 1 0)
  fu3 : fu.getD 2 0 < 27 ∧ p1 * t = t * tab p1 p2 (fu.getD 2 0)
  root : ∃ n, Rep n t ∧ vecJ rm r n ≠ r
  gen : ∀ k < 3, gs k ∈ Subgroup.closure ({g1, g2} : Set G)

section Loops

open CFSG.KC.SlpPc

private theorem ct_andB (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private theorem ct_orB (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

private theorem ct_sB (y : ℕ) (k : ℕ → Bool) : sB y k = k y := by cases y <;> rfl

private theorem ct_strictB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem ct_strictN (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem ct_brec {a b c : Bool} (h : Bool.rec (motive := fun _ => Bool) a b c = true) :
    a = true ∨ b = true := by
  cases c
  · exact Or.inl h
  · exact Or.inr h

private theorem ct_nthD {α : Type} (d : α) : ∀ (l : List α) (i : ℕ), nthD d l i = l.getD i d
  | [], i => by rw [List.getD_nil]; rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by rw [List.getD_cons_succ]; exact ct_nthD d l i

private theorem ct_getD_P {α : Type} {P : α → Prop} {l : List α} {d : α} (hd : P d)
    (hl : ∀ x ∈ l, P x) (i : ℕ) : P (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hl _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact hd

private theorem ct_lk_P {P : ℕ → Prop} {ONE : ℕ} (hONE : P ONE) {bl : List (List ℕ)}
    {cur : List ℕ} (hbl : ∀ l ∈ bl, ∀ x ∈ l, P x) (hcur : ∀ x ∈ cur, P x) (n r : ℕ) :
    P (lk ONE bl cur n r) := by
  unfold lk
  cases Nat.beq (Nat.shiftRight r 6) (Nat.shiftRight n 6)
  · change P (nthD ONE (nthD List.nil bl _) _)
    rw [ct_nthD, ct_nthD]
    exact ct_getD_P hONE (ct_getD_P (P := fun l => ∀ x ∈ l, P x)
      (fun x hx => absurd hx List.not_mem_nil) hbl _) _
  · change P (nthD ONE cur _)
    rw [ct_nthD]
    exact ct_getD_P hONE hcur _

private theorem ct_runP {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {P : ℕ → Prop} (hONE : P ONE)
    (hmul : ∀ a b, P a → P b → P (mul a b)) (k : List (List ℕ) → List ℕ → ℕ → Bool) :
    ∀ (prg : List (ℕ × ℕ)) (bl : List (List ℕ)) (cur : List ℕ) (n : ℕ),
      (∀ l ∈ bl, ∀ x ∈ l, P x) → (∀ x ∈ cur, P x) → runP mul ONE prg bl cur n k = true →
      ∃ bl' cur' n', (∀ l ∈ bl', ∀ x ∈ l, P x) ∧ (∀ x ∈ cur', P x) ∧ k bl' cur' n' = true
  | [], bl, cur, n, hbl, hcur, h => ⟨bl, cur, n, hbl, hcur, h⟩
  | p :: prg, bl, cur, n, hbl, hcur, h => by
    change sB (mul (lk ONE bl cur n p.1) (lk ONE bl cur n p.2)) (fun x => sB (Nat.succ n) fun n1 =>
      Bool.rec (motive := fun _ => Bool) (runP mul ONE prg bl (List.cons x cur) n1 k)
        (runP mul ONE prg (List.cons (List.cons x cur) bl) List.nil n1 k)
        (Nat.beq (Nat.land n1 63) 0)) = true at h
    simp only [ct_sB] at h
    have hx := hmul _ _ (ct_lk_P hONE hbl hcur n p.1) (ct_lk_P hONE hbl hcur n p.2)
    have hxc : ∀ y ∈ List.cons (mul (lk ONE bl cur n p.1) (lk ONE bl cur n p.2)) cur, P y := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hcur y hy
    rcases ct_brec h with h | h
    · exact ct_runP hONE hmul k prg bl _ _ hbl hxc h
    · refine ct_runP hONE hmul k prg _ List.nil _ ?_ (fun y hy => absurd hy List.not_mem_nil) h
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hxc
      · exact hbl l hl

private theorem ct_natRec (C : ℕ → Bool) : ∀ m : ℕ,
    Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (C k) ih) m = true →
      ∀ k < m, C k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | m + 1, h, k, hk => by
    change andB (C m) (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (C k) ih) m) =
      true at h
    rw [ct_andB, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ct_natRec C m h.2 k hk
    · exact h.1

private theorem ct_listRec {α : Type} (C : α → Bool) : ∀ l : List α,
    List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (C x) ih) l = true →
      ∀ x ∈ l, C x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    change andB (C y) (List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (C x) ih) l) =
      true at h
    rw [ct_andB, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ct_listRec C l h.2 x hx

private theorem ct_memN (x : ℕ) : ∀ T : List ℕ, memN x T = true ↔ x ∈ T
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | y :: T => by
    change orB (Nat.beq x y) (memN x T) = true ↔ _
    rw [ct_orB, Bool.or_eq_true, Nat.beq_eq, ct_memN x T, List.mem_cons]

private theorem ct_distN : ∀ {T : List ℕ}, distN T = true → T.Nodup
  | [], _ => List.nodup_nil
  | y :: T, h => by
    change andB (notB (memN y T)) (distN T) = true at h
    rw [ct_andB, Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hy => ?_, ct_distN h.2⟩
    have hm := (ct_memN y T).2 hy
    rw [hm] at h
    exact absurd h.1 Bool.false_ne_true

private theorem ct_tabFrom (c rm one : ℕ) (P1 P2 Z : List ℕ) (k : List ℕ → Bool) :
    ∀ (n : ℕ) (acc : List ℕ),
      tabFrom c rm one P1 P2 Z n acc k = k ((List.range n).map (entry c rm one P1 P2 Z) ++ acc)
  | 0, acc => rfl
  | n + 1, acc => by
    change strictB (entry c rm one P1 P2 Z n) (fun x => tabFrom c rm one P1 P2 Z n (x :: acc) k) =
      _
    rw [ct_strictB, ct_tabFrom c rm one P1 P2 Z k n, List.range_succ, List.map_append,
      List.append_assoc]
    rfl

end Loops

theorem chk_sound {c rm one r : ℕ} {mats invs : List ℕ} {prg prg2 : List (ℕ × ℕ)} {rp xr fu : List ℕ}
    {cj cw : List (List ℕ)} {Rep : ℕ → G → Prop} (_hR : Model c rm one Rep) (gs : ℕ → G)
    (_hm : ∀ k < 5, Rep (getN one mats k) (gs k)) (_hi : ∀ k < 5, Rep (getN one invs k) (gs k)⁻¹)
    (_h : chk c rm one r mats invs prg rp cj cw fu prg2 xr = true) :
    ∃ p1 p2 g1 g2 t : G, Facts Rep gs rm r cj cw fu p1 p2 g1 g2 t := by
  classical
  unfold chk at _h
  obtain ⟨bl, cur, n, hbl, hcur, h⟩ := ct_runP (P := fun x => ∃ g : G, Rep x g) ⟨1, _hR.one⟩
    (by rintro a b ⟨g, hg⟩ ⟨k, hk⟩; exact ⟨g * k, _hR.mul hg hk⟩) _ prg [] _ 11
    (fun l hl => absurd hl List.not_mem_nil) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact ⟨_, _hi _ (by norm_num)⟩
        | exact ⟨_, _hm _ (by norm_num)⟩
        | exact ⟨1, _hR.one⟩) _h
  have hP : ∀ k, ∃ g : G, Rep (CFSG.KC.SlpPc.lk one bl cur n k) g := fun k =>
    ct_lk_P (P := fun x => ∃ g : G, Rep x g) ⟨1, _hR.one⟩ hbl hcur n k
  unfold postOK at h
  simp only [ct_strictB] at h
  obtain ⟨p1, hp1⟩ := hP (CFSG.KC.SlpPc.nthD 0 rp 0)
  obtain ⟨p2, hp2⟩ := hP (CFSG.KC.SlpPc.nthD 0 rp 1)
  obtain ⟨g1, hg1⟩ := hP (CFSG.KC.SlpPc.nthD 0 rp 2)
  obtain ⟨g2, hg2⟩ := hP (CFSG.KC.SlpPc.nthD 0 rp 3)
  obtain ⟨g1', hg1'⟩ := hP (CFSG.KC.SlpPc.nthD 0 rp 4)
  obtain ⟨g2', hg2'⟩ := hP (CFSG.KC.SlpPc.nthD 0 rp 5)
  obtain ⟨t, ht⟩ := hP (CFSG.KC.SlpPc.nthD 0 rp 6)
  set P1 := CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 rp 0) with hP1
  set P2 := CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 rp 1) with hP2
  set G1 := CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 rp 2) with hG1
  set G2 := CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 rp 3) with hG2
  set G1i := CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 rp 4) with hG1i
  set G2i := CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 rp 5) with hG2i
  set TT := CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 rp 6) with hTT
  set S1 := mulJ c rm P1 P1 with hS1
  set S2 := mulJ c rm P2 P2 with hS2
  set Z := mulJ c rm (mulJ c rm (mulJ c rm P1 P2) S1) S2 with hZ
  set S3 := mulJ c rm Z Z with hS3
  set E := entry c rm one [one, P1, S1] [one, P2, S2] [one, Z, S3] with hE
  rw [ct_tabFrom] at h
  set T := (List.range 27).map E ++ [] with hT
  simp only [tabOK, ct_andB, Bool.and_eq_true] at h
  obtain ⟨h3, -, hdist, hcl1, hcl2, hcj0, hcj, hcw, hfu1, hfu2, hfu3, hne, hgi1, hgi2, hprg2⟩ := h
  have hs1 : Rep S1 (p1 * p1) := _hR.mul hp1 hp1
  have hs2 : Rep S2 (p2 * p2) := _hR.mul hp2 hp2
  have hz : Rep Z (p1 * p2 * p1 ^ 2 * p2 ^ 2) := by
    rw [pow_two, pow_two]
    exact _hR.mul (_hR.mul (_hR.mul hp1 hp2) hs1) hs2
  have hs3 : Rep S3 ((p1 * p2 * p1 ^ 2 * p2 ^ 2) * (p1 * p2 * p1 ^ 2 * p2 ^ 2)) := _hR.mul hz hz
  have h3e : ∀ {x : G} {a b : ℕ}, Rep a x → Rep b (x * x) → ∀ j < 3,
      Rep (CFSG.KC.SlpPc.nthD one [one, a, b] j) (x ^ j) := by
    intro x a b ha hb j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [pow_zero]
      exact _hR.one
    · rw [pow_one]
      exact ha
    · rw [pow_two]
      exact hb
  have hEr : ∀ i < 27, Rep (E i) (tab p1 p2 i) := by
    intro i hi
    rw [hE]
    unfold entry tab
    rw [ct_strictN]
    change Rep (mulJ c rm (mulJ c rm (CFSG.KC.SlpPc.nthD one _ (i / 9))
      (CFSG.KC.SlpPc.nthD one _ (i / 3 % 3))) (CFSG.KC.SlpPc.nthD one _ (i % 3))) _
    exact _hR.mul (_hR.mul (h3e hp1 hs1 _ (by omega)) (h3e hp2 hs2 _ (by omega)))
      (h3e hz hs3 _ (by omega))
  have hTl : T = (List.range 27).map E := by rw [hT, List.append_nil]
  have hTi : ∀ i < 27, CFSG.KC.SlpPc.nthD one T i = E i := by
    intro i hi
    rw [ct_nthD, hTl, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getElem_range]
  have hTr : ∀ i < 27, Rep (CFSG.KC.SlpPc.nthD one T i) (tab p1 p2 i) := fun i hi =>
    (hTi i hi) ▸ hEr i hi
  have hmemT : ∀ y, memN y T = true → ∃ l < 27, y = E l := by
    intro y hy
    rw [ct_memN, hTl] at hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    exact ⟨l, List.mem_range.1 hl, rfl⟩
  have hET : ∀ k < 27, E k ∈ T := fun k hk => by
    rw [hTl]
    exact List.mem_map_of_mem (List.mem_range.2 hk)
  have hclos : ∀ {g : ℕ} {x : G}, Rep g x → closOK c rm g T = true →
      ∀ k < 27, ∃ l < 27, tab p1 p2 k * x = tab p1 p2 l := by
    intro g x hg hc k hk
    have hm := ct_listRec (fun y => strictB (mulJ c rm y g) fun y => memN y T) T hc (E k) (hET k hk)
    rw [ct_strictB] at hm
    obtain ⟨l, hl, he⟩ := hmemT _ hm
    have hr := _hR.mul (hEr k hk) hg
    rw [he] at hr
    exact ⟨l, hl, _hR.inj hr (hEr l hl)⟩
  have hinv : ∀ {g gi : G} {G' Gi : ℕ}, Rep G' g → Rep Gi gi → mulJ c rm G' Gi = one →
      gi = g⁻¹ := by
    intro g gi G' Gi hg hgi he
    have hr := _hR.mul hg hgi
    rw [he] at hr
    exact eq_inv_of_mul_eq_one_right (_hR.inj hr _hR.one)
  rw [Nat.beq_eq] at hgi1 hgi2
  have e1 := hinv hg1 hg1' hgi1
  have e2 := hinv hg2 hg2' hgi2
  set Sg : Subgroup G := Subgroup.closure ({g1, g2} : Set G) with hSg
  have hg1S : g1 ∈ Sg := Subgroup.subset_closure (by simp)
  have hg2S : g2 ∈ Sg := Subgroup.subset_closure (by simp)
  obtain ⟨bl2, cur2, n2, hbl2, hcur2, hx⟩ := ct_runP (P := fun x => ∃ s ∈ Sg, Rep x s)
    ⟨1, Sg.one_mem, _hR.one⟩
    (by rintro a b ⟨g, hg, hga⟩ ⟨k, hk, hkb⟩; exact ⟨g * k, Sg.mul_mem hg hk, _hR.mul hga hkb⟩)
    _ prg2 [] _ 5 (fun l hl => absurd hl List.not_mem_nil) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨g2', e2 ▸ Sg.inv_mem hg2S, hg2'⟩
      · exact ⟨g1', e1 ▸ Sg.inv_mem hg1S, hg1'⟩
      · exact ⟨g2, hg2S, hg2⟩
      · exact ⟨g1, hg1S, hg1⟩
      · exact ⟨1, Sg.one_mem, _hR.one⟩) hprg2
  have hxk := ct_natRec (fun k => Nat.beq (CFSG.KC.SlpPc.lk one bl2 cur2 n2
    (CFSG.KC.SlpPc.nthD 0 xr k)) (getN one mats k)) 3 hx
  have hfu : ∀ {g : ℕ} {x : G} {e : ℕ}, Rep g x → fuOne c rm one P1 g T e = true →
      e < 27 ∧ p1 * x = x * tab p1 p2 e := by
    intro g x e hg hf
    unfold fuOne at hf
    rw [ct_andB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hf
    have hr := _hR.mul hp1 hg
    rw [hf.2] at hr
    exact ⟨hf.1, _hR.inj hr (_hR.mul hg (hTr _ hf.1))⟩
  have hcjA := ct_listRec (fun e => andB (Nat.blt (CFSG.KC.SlpPc.nthD 0 e 0) 27)
    ((fun C => Nat.beq (mulJ c rm C (CFSG.KC.SlpPc.nthD one T (CFSG.KC.SlpPc.nthD 0 e 0)))
      (mulJ c rm P1 C)) (CFSG.KC.SlpPc.lk one bl cur n (CFSG.KC.SlpPc.nthD 0 e 1)))) cj hcj
  have hconj : ∀ j < cj.length, cjM cj j < 27 ∧ ∃ c' : G, c' * tab p1 p2 (cjM cj j) = p1 * c' := by
    intro j hj
    have hm := hcjA (cj.getD j []) (by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj)
    simp only [ct_andB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hm
    have hcm : cjM cj j = CFSG.KC.SlpPc.nthD 0 (cj.getD j []) 0 := by
      rw [cjM, ct_nthD]
    rw [hcm]
    obtain ⟨c', hc'⟩ := hP (CFSG.KC.SlpPc.nthD 0 (cj.getD j []) 1)
    refine ⟨hm.1, c', ?_⟩
    have hr := _hR.mul hc' (hTr _ hm.1)
    rw [hm.2] at hr
    exact _hR.inj hr (_hR.mul hp1 hc')
  have hcwA := ct_natRec (fun i => cwOne c rm one T cj (CFSG.KC.SlpPc.nthD one T (Nat.succ i))
    (CFSG.KC.SlpPc.nthD List.nil cw (Nat.succ i))) 26 hcw
  rw [ct_nthD] at hfu1 hfu2 hfu3
  refine ⟨p1, p2, g1, g2, t, ?_, hclos hp1 hcl1, hclos hp2 hcl2, ?_, ?_, hconj, ?_,
    hfu hg1 hfu1, hfu hg2 hfu2, hfu ht hfu3, ?_, ?_⟩
  ·
    rw [Nat.beq_eq] at h3
    have hr := _hR.mul hs1 hp1
    rw [h3] at hr
    rw [pow_three']
    exact _hR.inj hr _hR.one
  ·
    intro k hk k' hk' he
    have hnd := ct_distN hdist
    rw [hTl] at hnd
    have hEE := _hR.fn (hEr k' (by omega)) (he ▸ hEr k hk)
    have := List.inj_on_of_nodup_map hnd (List.mem_range.2 (by omega : k' < 27))
      (List.mem_range.2 hk) hEE
    omega
  ·
    rw [Nat.beq_eq] at hcj0
    rcases cj with _ | ⟨e, cj⟩
    · exact absurd hcj0 (by decide)
    · refine ⟨by simp, ?_⟩
      rw [cjM, ct_nthD, ct_nthD] at *
      exact hcj0
  ·
    intro k hk0 hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hw := hcwA i (by omega)
    unfold cwOne at hw
    simp only [ct_andB, Bool.and_eq_true, Nat.blt_eq] at hw
    obtain ⟨hu, hj, -, hb⟩ := hw
    refine ⟨_, hu, _, hj, ?_⟩
    have hcm : CFSG.KC.SlpPc.nthD 0 (CFSG.KC.SlpPc.nthD List.nil cj
        (CFSG.KC.SlpPc.nthD 0 (CFSG.KC.SlpPc.nthD List.nil cw (i + 1)) 1)) 0 =
        cjM cj (CFSG.KC.SlpPc.nthD 0 (CFSG.KC.SlpPc.nthD List.nil cw (i + 1)) 1) := by
      rw [cjM, ct_nthD, ct_nthD]
    rw [hcm] at hb
    have hU := hTr _ hu
    have hX := hTr (i + 1) hk
    have hEm := hTr _ (hconj _ hj).1
    rcases ct_brec hb with hb | hb
    · rw [Nat.beq_eq] at hb
      have hr := _hR.mul hU hX
      rw [hb] at hr
      exact Or.inl (_hR.inj hr (_hR.mul hEm hU))
    · rw [Nat.beq_eq] at hb
      have hr := _hR.mul (_hR.mul hEm hU) hX
      rw [hb] at hr
      exact Or.inr (_hR.inj hr hU)
  ·
    refine ⟨TT, ht, fun e => ?_⟩
    unfold neN at hne
    rw [e, Nat.beq_refl] at hne
    exact absurd hne (by decide)
  ·
    intro k hk
    have hk' := hxk k hk
    rw [Nat.beq_eq] at hk'
    obtain ⟨s, hs, hsr⟩ := ct_lk_P (P := fun x => ∃ s ∈ Sg, Rep x s) ⟨1, Sg.one_mem, _hR.one⟩
      hbl2 hcur2 n2 (CFSG.KC.SlpPc.nthD 0 xr k)
    rw [hk'] at hsr
    rw [_hR.inj (_hm k (by omega)) hsr]
    exact hs

end CFSG.KS.J4CovTab

namespace CFSG.KS.J4CovTab

open CFSG.KC.J4Q CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def jRep (n : ℕ) (g : J) : Prop :=
  ∃ X : Array V2, WfA X ∧ encR X = n ∧ rowsMatrix X = Mx g

theorem wf_mem {X : Array V2} (hX : WfA X) : ∀ x ∈ X, x.wf = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact Array.all_eq_true.1 hX.2 i hi

theorem eq_of_enc {X Y : Array V2} (hX : WfA X) (hY : WfA Y) (e : encR X = encR Y) : X = Y := by
  apply eqRows_iff.1
  rw [eqRows_eq hX hY, e]
  exact Nat.beq_refl _

theorem jModel {c rm one pad t0 t1 t2 t3 t4 t5 t6 : ℕ} (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    Model c rm one jRep where
  one := ⟨idRows (), wf_idRows, enc_idRows hK, by rw [rowsMatrix_idRows, map_one]⟩
  mul := by
    rintro _ _ g h ⟨X, hX, rfl, eX⟩ ⟨Y, hY, rfl, eY⟩
    exact ⟨mulRows X Y, wf_mulRows hX hY, enc_mulRows hK hX hY,
      by rw [rowsMatrix_mulRows, eX, eY, map_mul]⟩
  inj := by
    rintro _ g h ⟨X, hX, rfl, eX⟩ ⟨Y, hY, e, eY⟩
    have hXY := eq_of_enc hY hX e
    subst hXY
    exact Mx_injective (eX.symm.trans eY)
  fn := by
    rintro _ _ g ⟨X, hX, rfl, eX⟩ ⟨Y, hY, rfl, eY⟩
    cases h : eqRows X Y
    · exact absurd (eX.trans eY.symm) (rowsMatrix_ne_of_eqRows_false hX.1 hY.1 (wf_mem hX)
        (wf_mem hY) h)
    · rw [eqRows_iff.1 h]

theorem not_mem_Hj {c rm one pad t0 t1 t2 t3 t4 t5 t6 : ℕ}
    (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (hM : MatFacts) {n : ℕ} {t : J} (ht : jRep n t)
    (hv : vecJ rm (v2N rootV) n ≠ v2N rootV) : t ∉ Hj := by
  obtain ⟨X, hX, rfl, eX⟩ := ht
  intro hmem
  have hfix := Hj_fix_root hM _ (Hj.inv_mem hmem)
  rw [← ofRow_inj, inv_smul_row, ← Mx_apply, ← eX] at hfix
  have hr : rootV.wf = true := by decide
  apply hv
  rw [← v2N_frApply hK hX hr]
  congr 1
  apply V2.eq_of_toVec_eq (wf_frApply hX rootV) hr
  rw [frApply_toVec_eq_vecMul]
  exact hfix

end CFSG.KS.J4CovTab

end
