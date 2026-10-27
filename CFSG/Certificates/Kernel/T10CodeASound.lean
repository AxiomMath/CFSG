module

public import Certificates.Data.Kernel.T10CodeA
public import CFSG.Certificates.Kernel.T10CodeSound

public section

namespace CFSG.KC.T10Code

open CFSG.OddStandard.AltStdSmall4.ModT10 CFSG.OddStandard.AltStdSmall4.ModT10.T10

theorem testBit_boolShift (c : Bool) (n j : Nat) :
    (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 c) n).testBit j = (c && decide (n = j)) := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  cases c <;> simp [Nat.testBit_two_pow]

theorem testBit_maskN (p : Nat → Bool) (n j : Nat) :
    (maskN p n).testBit j = (decide (j < n) && p j) := by
  induction n with
  | zero => simp [maskN]
  | succ n ih =>
    change (Nat.lor (maskN p n)
      (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (p n)) n)).testBit j = _
    rw [Nat.lor_eq, Nat.testBit_or, ih, testBit_boolShift]
    rcases Nat.lt_trichotomy j n with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h, show n ≠ j by omega]
    · simp
    · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega, show n ≠ j by omega]

theorem land_ALL_eq_iff (d : Nat) : Nat.land d ALL = ALL ↔ ∀ g < 1024, d.testBit g = true := by
  constructor
  · intro h g hg
    have := congrArg (fun n => n.testBit g) h
    simpa [Nat.land_eq, Nat.testBit_and, testBit_ALL, hg] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro g
    rw [Nat.land_eq, Nat.testBit_and, testBit_ALL]
    by_cases hg : g < 1024
    · simp [hg, h g hg]
    · simp [hg]

theorem land_eq_zero_iff (a b : Nat) :
    Nat.land a b = 0 ↔ ∀ y, a.testBit y = true → b.testBit y = false := by
  constructor
  · intro h y hy
    have := congrArg (fun n => n.testBit y) h
    simpa [Nat.land_eq, Nat.testBit_and, hy] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro y
    rw [Nat.land_eq, Nat.testBit_and, Nat.zero_testBit]
    cases hy : a.testBit y
    · rfl
    · simp [h y hy]

theorem allR0 {p : Nat → Bool} {N : Nat} (h : allR p 0 N = true) : ∀ i < N, p i = true := by
  intro i hi
  have := allR_spec h i hi
  rwa [Nat.zero_add] at this

theorem cntN_succ (p : Nat → Bool) (N : Nat) :
    cntN p (N + 1) = cntN p N + (if p N = true then 1 else 0) := by
  change Bool.rec (motive := fun _ => Nat) (cntN p N) (Nat.succ (cntN p N)) (p N) = _
  cases p N <;> rfl

theorem cntN_false (N : Nat) : cntN (fun _ => false) N = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [cntN_succ, ih]; rfl

theorem cntN_or {p q : Nat → Bool} {N : Nat} (h : ∀ x < N, ¬ (p x = true ∧ q x = true)) :
    cntN (fun x => p x || q x) N = cntN p N + cntN q N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [cntN_succ, cntN_succ, cntN_succ (p := q), ih fun x hx => h x (by omega)]
    have := h N (by omega)
    cases hp : p N <;> cases hq : q N <;> simp_all <;> omega

theorem sumM_succ (f : Nat → Nat) (m n : Nat) :
    sumM f m (n + 1) = sumM f m n + (if m.testBit n = true then f n else 0) := by
  change Nat.add (sumM f m n) (Bool.rec (motive := fun _ => Nat) 0 (f n) (tb m n)) = _
  rw [tb_eq]
  cases m.testBit n <;> rfl

theorem sumM_eq (f : Nat → Nat) (g : Nat → Bool) (lab : Nat → Nat) (m N : Nat)
    (hf : ∀ i < 25, f i = cntN (fun x => g x && decide (lab x = i)) N) :
    ∀ n ≤ 25, sumM f m n = cntN (fun x => g x && m.testBit (lab x) && decide (lab x < n)) N := by
  intro n hn
  induction n with
  | zero =>
    rw [cntN_congr (q := fun _ => false) (fun x _ => by simp), cntN_false]
    rfl
  | succ n ih =>
    have hsplit : cntN (fun x => g x && m.testBit (lab x) && decide (lab x < n + 1)) N =
        cntN (fun x => g x && m.testBit (lab x) && decide (lab x < n)) N +
          cntN (fun x => g x && decide (lab x = n) && m.testBit n) N := by
      rw [← cntN_or (fun x _ => by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rintro ⟨⟨_, h1⟩, ⟨_, h2⟩, _⟩
        omega)]
      refine cntN_congr fun x _ => ?_
      rcases Nat.lt_trichotomy (lab x) n with h | h | h
      · simp [h, Nat.lt_succ_of_lt h, Nat.ne_of_lt h]
      · rw [h]
        cases g x <;> cases m.testBit n <;> simp
      · simp [show ¬ lab x < n by omega, show ¬ lab x < n + 1 by omega, show lab x ≠ n by omega]
    have hlast : cntN (fun x => g x && decide (lab x = n) && m.testBit n) N =
        if m.testBit n = true then f n else 0 := by
      cases hm : m.testBit n
      · rw [cntN_congr (q := fun _ => false) (fun x _ => by simp), cntN_false]
        rfl
      · rw [hf n (by omega)]
        simp
    rw [sumM_succ, ih (by omega), hsplit, hlast]

theorem memO_eq {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j) (c : Nat) {x : Nat}
    (hx : x < 1024) : memO P c x = (orbitOf (allL ()) (ofCode c)).contains (ofCode x) := by
  have key : (orbitOf (allL ()) (ofCode c)).contains (ofCode x) = true ↔
      ∃ g < 1024, ofCode g * ofCode c * (ofCode g)⁻¹ = ofCode x := by
    rw [List.contains_iff, orbitOf, List.mem_dedup, allL, List.map_map, List.mem_map]
    simp only [List.mem_range, Function.comp_apply]
  have hbit : ∀ g < 1024, (difW (mulW (mulW P (BC c)) (invW P)) (BC x)).testBit g =
      !decide (ofCode g * ofCode c * (ofCode g)⁻¹ = ofCode x) := by
    intro g hg
    rw [difW_testBit, atW_mulW, atW_mulW, atW_invW, hP g hg, atW_BC c hg, atW_BC x hg]
  rw [memO, Bool.eq_iff_iff, key]
  cases hb : Nat.beq (Nat.land (difW (mulW (mulW P (BC c)) (invW P)) (BC x)) ALL) ALL
  · have hne : ¬ (Nat.land (difW (mulW (mulW P (BC c)) (invW P)) (BC x)) ALL = ALL) :=
      Nat.ne_of_beq_eq_false hb
    rw [land_ALL_eq_iff] at hne
    simp only [not_forall] at hne
    obtain ⟨g, hg, hgb⟩ := hne
    rw [hbit g hg] at hgb
    simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq] at hgb
    exact ⟨fun _ => ⟨g, hg, by simpa using hgb⟩, fun _ => rfl⟩
  · have he := (land_ALL_eq_iff _).1 (Nat.eq_of_beq_eq_true hb)
    simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro g hg hgx
    have := he g hg
    rw [hbit g hg, hgx] at this
    simp at this

theorem labD_eq (D : List (Nat × Nat)) (x : Nat) : labD D x = D.findIdx fun d => tb d.2 x := by
  induction D with
  | nil => rfl
  | cons d D ih =>
    rw [List.findIdx_cons, ← ih]
    change Bool.rec (motive := fun _ => Nat) (Nat.succ (labD D x)) 0 (tb d.2 x) = _
    cases tb d.2 x <;> rfl

theorem findIdx_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.findIdx p = l.findIdx q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.findIdx_cons, List.findIdx_cons, h a (by simp),
      findIdx_congr' fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem orbOK_spec {P : W10} :
    ∀ {D : List (Nat × Nat)}, orbOK P D = true → ∀ d ∈ D, d.2 = maskN (memO P d.1) 1024
  | [], _, d, hd => absurd hd List.not_mem_nil
  | e :: D, h, d, hd => by
    change Bool.rec (motive := fun _ => Bool) false (orbOK P D)
      (Nat.beq e.2 (maskN (memO P e.1) 1024)) = true at h
    cases he : Nat.beq e.2 (maskN (memO P e.1) 1024)
    · rw [he] at h
      exact absurd h Bool.false_ne_true
    · rw [he] at h
      rcases List.mem_cons.1 hd with rfl | hd
      · exact Nat.eq_of_beq_eq_true he
      · exact orbOK_spec h d hd

theorem orbD_ok {P : W10} (h0 : orbOK P orbD0 = true) (h1 : orbOK P orbD1 = true)
    (h2 : orbOK P orbD2 = true) (h3 : orbOK P orbD3 = true) (h4 : orbOK P orbD4 = true) :
    ∀ d ∈ orbD, d.2 = maskN (memO P d.1) 1024 := by
  intro d hd
  simp only [orbD, List.mem_append] at hd
  rcases hd with (((hd | hd) | hd) | hd) | hd
  · exact orbOK_spec h0 d hd
  · exact orbOK_spec h1 d hd
  · exact orbOK_spec h2 d hd
  · exact orbOK_spec h3 d hd
  · exact orbOK_spec h4 d hd

theorem repCodes_eq : repCodes = orbD.map Prod.fst := by
  simp only [repCodes, orbD, orbD0, orbD1, orbD2, orbD3, orbD4, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil]

theorem findIdx_orbits (L : List T10) (cs : List Nat) (D : List (Nat × Nat))
    (hcs : cs = D.map Prod.fst) (y : T10) (x : Nat)
    (hD : ∀ d ∈ D, (orbitOf L (ofCode d.1)).contains y = tb d.2 x) :
    ((cs.map ofCode).map (orbitOf L)).findIdx (fun o => o.contains y) = labD D x := by
  rw [hcs, List.map_map, List.map_map, List.findIdx_map, labD_eq]
  exact findIdx_congr' fun d hd => hD d hd

theorem clsIdx_eq {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j)
    (hO : ∀ d ∈ orbD, d.2 = maskN (memO P d.1) 1024) {x : Nat} (hx : x < 1024) :
    clsIdx (orbitsT ()) (ofCode x) = labD orbD x := by
  have h := findIdx_orbits (allL ()) repCodes orbD repCodes_eq (ofCode x) x fun d hd => by
    rw [tb_eq, hO d hd, testBit_maskN, ← memO_eq hP d.1 hx, decide_eq_true hx, Bool.true_and]
  exact h

noncomputable def pairsC : List (T10 × Nat) :=
  ((List.range 1024).filter fun x => isInv (ofCode x)).map fun x => (ofCode x, labD orbD x)

theorem pairsT_eq (hcls : ∀ x < 1024, clsIdx (orbitsT ()) (ofCode x) = labD orbD x) :
    pairsT () = pairsC := by
  simp only [pairsT, pairsC, allL, List.filter_map, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro x hx
  rw [hcls x (List.mem_range.1 (List.mem_filter.1 hx).1)]

theorem filter_pairs (h : Nat → Bool) :
    (pairsC.filter fun p => h p.2).map Prod.fst =
      ((List.range 1024).filter fun x => isInv (ofCode x) && h (labD orbD x)).map ofCode := by
  simp only [pairsC, List.filter_map, List.map_map, List.filter_filter, Function.comp_def]
  exact congrArg (List.map ofCode) (List.filter_congr fun x _ => Bool.and_comm _ _)

theorem members_eq (i : Nat) : members pairsC i =
    ((List.range 1024).filter fun x => isInv (ofCode x) && (labD orbD x == i)).map ofCode :=
  filter_pairs fun k => k == i

section Classes

variable {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j) (hK : ∀ i < 25, kchk P i = true)
include hP hK

theorem Kof_spec {i : Nat} (hi : i < 25) (y : Nat) :
    tb (Kof i) y = true ↔ y < 1024 ∧ isInv (ofCode y) = true ∧ labD orbD y = i := by
  rw [tb_eq, Nat.eq_of_beq_eq_true (hK i hi), testBit_maskN]
  by_cases hy : y < 1024
  · rw [isInvc_eq hP hy, decide_eq_true hy, Bool.true_and, Bool.and_eq_true, Nat.beq_eq]
    exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩
  · rw [decide_eq_false hy, Bool.false_and]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h.1 hy⟩

omit hP hK in
theorem commB_comm (a b : T10) : commB a b = commB b a := by
  unfold commB
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact eq_comm

theorem rvec_spec {x j : Nat} (hx : x < 1024) (hj : j < 25) :
    (rvec P x).testBit j = true ↔ ∀ y < 1024, isInv (ofCode y) = true → labD orbD y = j →
      commB (ofCode x) (ofCode y) = true := by
  rw [rvec, testBit_maskN]
  simp only [hj, decide_true, Bool.true_and, Nat.beq_eq, land_eq_zero_iff]
  constructor
  · intro h y hy hyi hyl
    have hk := (Kof_spec hP hK hj y).2 ⟨hy, hyi, hyl⟩
    rw [tb_eq] at hk
    have hc := h y
    rw [commB_comm, ← commc_eq hP hy hx, commc, tb_eq]
    cases hcd : (CDW P x).testBit y
    · rfl
    · rw [hc hcd] at hk
      exact absurd hk Bool.false_ne_true
  · intro h y hcd
    cases hk : (Kof j).testBit y
    · rfl
    · rw [← tb_eq] at hk
      obtain ⟨hy, hyi, hyl⟩ := (Kof_spec hP hK hj y).1 hk
      have hc := h y hy hyi hyl
      rw [commB_comm, ← commc_eq hP hy hx, commc, tb_eq, hcd] at hc
      exact absurd hc Bool.false_ne_true

end Classes

theorem testBit_andAcc (p : Nat → Bool) (r : Nat → Nat) (init N j : Nat) :
    (andAcc p r init N).testBit j = true ↔
      init.testBit j = true ∧ ∀ x < N, p x = true → (r x).testBit j = true := by
  induction N with
  | zero => simp [andAcc]
  | succ N ih =>
    change (Bool.rec (motive := fun _ => Nat) (andAcc p r init N)
      (Nat.land (andAcc p r init N) (r N)) (p N)).testBit j = true ↔ _
    have hsplit : (∀ x < N + 1, p x = true → (r x).testBit j = true) ↔
        (∀ x < N, p x = true → (r x).testBit j = true) ∧ (p N = true → (r N).testBit j = true) := by
      constructor
      · intro h
        exact ⟨fun x hx => h x (by omega), h N (by omega)⟩
      · rintro ⟨h, hN⟩ x hx
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
        · exact h x hx
        · exact hN
    rw [hsplit]
    cases hp : p N
    · simp only [ih, Bool.false_eq_true, false_implies, and_true]
    · simp only [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true, ih, forall_const, and_assoc]

theorem testBit_R25 (j : Nat) : R25.testBit j = decide (j < 25) := by
  have : R25 = 2 ^ 25 - 1 := rfl
  rw [this, Nat.testBit_two_pow_sub_one]

theorem cmOf_eq (Q : List (T10 × Nat)) {i j : Nat} (hi : i < 25) (hj : j < 25) :
    cmOf (commTab Q) i j = classesCommute Q i j := by
  simp [cmOf, commTab, hi, hj]

theorem classesCommute_iff (i j : Nat) :
    classesCommute pairsC i j = true ↔ ∀ x < 1024, isInv (ofCode x) = true → labD orbD x = i →
      ∀ y < 1024, isInv (ofCode y) = true → labD orbD y = j →
        commB (ofCode x) (ofCode y) = true := by
  simp only [classesCommute, members_eq, List.all_eq_true, List.mem_map,
    List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq, forall_exists_index, and_imp]
  constructor
  · intro h x hx hxi hxl y hy hyi hyl
    first
    | exact h _ x hx hxi hxl rfl _ y hy hyi hyl rfl
    | exact h x hx hxi hxl y hy hyi hyl
  · intro h
    first
    | exact h
    | exact fun _ x hx hxi hxl e _ y hy hyi hyl e' => e ▸ e' ▸ h x hx hxi hxl y hy hyi hyl

theorem cm_eq {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j) (hK : ∀ i < 25, kchk P i = true)
    (hR : ∀ i < 25, rowOK P i = true) {i j : Nat} (hi : i < 25) (hj : j < 25) :
    cmOf (commTab pairsC) i j = tb (rowM i) j := by
  rw [cmOf_eq _ hi hj, tb_eq, Nat.eq_of_beq_eq_true (hR i hi), Bool.eq_iff_iff,
    classesCommute_iff, testBit_andAcc, testBit_R25]
  simp only [hj, decide_true, true_and]
  constructor
  · intro h x _ hk
    obtain ⟨hx, hxi, hxl⟩ := (Kof_spec hP hK hi x).1 hk
    exact (rvec_spec hP hK hx hj).2 fun y hy hyi hyl => h x hx hxi hxl y hy hyi hyl
  · intro h x hx hxi hxl y hy hyi hyl
    have hk : tb (Kof i) x = true := (Kof_spec hP hK hi x).2 ⟨hx, hxi, hxl⟩
    exact (rvec_spec hP hK hx hj).1 (h x hx hk) y hy hyi hyl

theorem mem_of_mem_cliques {cm : ℕ → ℕ → Bool} :
    ∀ {L S : List ℕ}, S ∈ cliques cm L → ∀ s ∈ S, s ∈ L
  | [], S, hS, s, hs => by
    simp only [cliques, List.mem_singleton] at hS
    subst hS
    exact absurd hs List.not_mem_nil
  | k :: ks, S, hS, s, hs => by
    simp only [cliques, List.mem_append, List.mem_map, List.mem_filter] at hS
    rcases hS with hS | ⟨S', ⟨hS', _⟩, rfl⟩
    · exact List.mem_cons_of_mem k (mem_of_mem_cliques hS s hs)
    · rcases List.mem_cons.1 hs with rfl | hs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_cliques hS' s hs)

theorem dfsM_spec {row : ℕ → ℕ} {Q : ℕ → Bool} {cm : ℕ → ℕ → Bool} :
    ∀ {L : List ℕ}, (∀ a ∈ L, ∀ b ∈ L, cm a b = tb (row a) b) → ∀ {ch al : ℕ},
      dfsM row Q L ch al = true → ∀ S ∈ cliques cm L, (∀ s ∈ S, tb al s = true) →
        ∃ m, (∀ i, m.testBit i = (ch.testBit i || S.contains i)) ∧ Q m = true
  | [], _, ch, al, h, S, hS, _ => by
    simp only [cliques, List.mem_singleton] at hS
    subst hS
    exact ⟨ch, fun i => by simp, h⟩
  | k :: ks, hcm, ch, al, h, S, hS, hal => by
    change (dfsM row Q ks ch al && (!(tb (row k) k && tb al k) ||
      dfsM row Q ks (Nat.lor ch (Nat.shiftLeft 1 k)) (Nat.land al (row k)))) = true at h
    rw [Bool.and_eq_true] at h
    have hcm' : ∀ a ∈ ks, ∀ b ∈ ks, cm a b = tb (row a) b := fun a ha b hb =>
      hcm a (List.mem_cons_of_mem k ha) b (List.mem_cons_of_mem k hb)
    simp only [cliques, List.mem_append, List.mem_map, List.mem_filter] at hS
    rcases hS with hS | ⟨S', ⟨hS', hc⟩, rfl⟩
    · exact dfsM_spec hcm' h.1 S hS hal
    · rw [Bool.and_eq_true, List.all_eq_true] at hc
      have hk : tb al k = true := hal k List.mem_cons_self
      have hkk : tb (row k) k = true := by
        rw [← hcm k List.mem_cons_self k List.mem_cons_self]
        exact hc.1
      have h2 := h.2
      rw [hkk, hk] at h2
      simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h2
      obtain ⟨m, hm, hQ⟩ := dfsM_spec hcm' h2 S' hS' fun s hs => by
        have hsl := List.mem_cons_of_mem k (mem_of_mem_cliques hS' s hs)
        have hal' := hal s (List.mem_cons_of_mem k hs)
        have hks := hc.2 s hs
        rw [hcm k List.mem_cons_self s hsl] at hks
        rw [tb_eq] at hal' hks ⊢
        rw [Nat.land_eq, Nat.testBit_and, hal', hks]
        rfl
      refine ⟨m, fun i => ?_, hQ⟩
      rw [hm i, Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', Nat.one_shiftLeft,
        Nat.testBit_two_pow, List.contains_cons]
      by_cases hik : i = k
      · subst hik
        simp
      · have hb : (i == k) = false := beq_eq_false_iff_ne.2 hik
        simp [hb, hik, Ne.symm hik]

theorem allQm_spec {m n : Nat} (h : allQm m n = true) :
    ∀ i < n, m.testBit i = true → tb QB i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (allQm m n) (!tb m n || tb QB n) = true at h
    intro i hi hm
    cases hq : (!tb m n || tb QB n)
    · rw [hq] at h
      exact absurd h Bool.false_ne_true
    · rw [hq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih h i hi hm
      · rw [tb_eq, hm] at hq
        simpa using hq

theorem leafOK_of {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j)
    (hK : ∀ i < 25, kchk P i = true) (hC : ∀ i < 25, clsOK P i = true)
    (hL : ∀ x < 1024, isInv (ofCode x) = true → labD orbD x < 25) {S : List Nat} {m : Nat}
    (hm : ∀ i, m.testBit i = S.contains i) (h : leafM m = true) : leafOK pairsC S = true := by
  have hC' := fun i (hi : i < 25) => by
    have := hC i hi
    simp only [clsOK, Bool.and_eq_true] at this
    exact this
  have hsz : ∀ i < 25, szOf i = cntN (fun x => isInv (ofCode x) && decide (labD orbD x = i)) 1024 := by
    intro i hi
    rw [Nat.eq_of_beq_eq_true (hC' i hi).1.1]
    refine cntN_congr fun x hx => ?_
    rw [Bool.eq_iff_iff, Kof_spec hP hK hi]
    simp [hx]
  have htc : ∀ i < 25, tcOf i = cntN (fun x => (isInv (ofCode x) && commB (ofCode x) tm) &&
      decide (labD orbD x = i)) 1024 := by
    intro i hi
    rw [Nat.eq_of_beq_eq_true (hC' i hi).1.2]
    refine cntN_congr fun x hx => ?_
    rw [commc_eq hP hx (by omega), ← tm_eq]
    cases hk : tb (Kof i) x
    · have hk' : ¬ (x < 1024 ∧ isInv (ofCode x) = true ∧ labD orbD x = i) := by
        rw [← Kof_spec hP hK hi]
        simp [hk]
      simp only [Bool.false_and]
      symm
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hi' : isInv (ofCode x) = true
      · exact Or.inr (fun hl => hk' ⟨hx, hi', hl⟩)
      · exact Or.inl (Or.inl (by simpa using hi'))
    · obtain ⟨_, hi', hl⟩ := (Kof_spec hP hK hi x).1 hk
      simp [hi', hl]
  have hcnt : ∀ g : Nat → Bool, (∀ x, g x = true → isInv (ofCode x) = true) →
      ∀ f : Nat → Nat, (∀ i < 25, f i = cntN (fun x => g x && decide (labD orbD x = i)) 1024) →
        sumM f m 25 = cntN (fun x => g x && S.contains (labD orbD x)) 1024 := by
    intro g hg f hf
    rw [sumM_eq f g (labD orbD) m 1024 hf 25 le_rfl]
    refine cntN_congr fun x hx => ?_
    cases hgx : g x
    · rfl
    · simp [hm, hL x hx (hg x hgx)]
  have hU : (pairsC.filter fun p => S.contains p.2).map Prod.fst =
      ((List.range 1024).filter fun x => isInv (ofCode x) && S.contains (labD orbD x)).map ofCode :=
    filter_pairs _
  have hlen : sumM szOf m 25 = (((List.range 1024).filter fun x =>
      isInv (ofCode x) && S.contains (labD orbD x)).map ofCode).length := by
    rw [hcnt (fun x => isInv (ofCode x)) (fun _ h => h) szOf hsz, List.length_map, cntN_eq]
  have htm : sumM tcOf m 25 = ((((List.range 1024).filter fun x =>
      isInv (ofCode x) && S.contains (labD orbD x)).map ofCode).filter fun g => commB g tm).length := by
    rw [hcnt (fun x => isInv (ofCode x) && commB (ofCode x) tm)
      (fun x h => by simp only [Bool.and_eq_true] at h; exact h.1) tcOf htc, cntN_eq,
      List.filter_map, List.length_map, List.filter_filter]
    exact congrArg List.length (List.filter_congr fun x _ => by
      simp only [Function.comp_apply]
      cases isInv (ofCode x) <;> cases commB (ofCode x) tm <;> cases S.contains (labD orbD x) <;> rfl)
  have hQ : allQm m 25 = true → (((List.range 1024).filter fun x =>
      isInv (ofCode x) && S.contains (labD orbD x)).map ofCode).all inQ = true := by
    intro hq
    rw [List.all_eq_true]
    intro u hu
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true] at hx
    obtain ⟨hx, hxi, hxs⟩ := hx
    have hl := hL x hx hxi
    have hqb := allQm_spec hq _ hl (by rw [hm]; exact hxs)
    have h3 := (hC' _ hl).2
    rw [hqb, Bool.not_true, Bool.false_or, Nat.beq_eq, land_eq_zero_iff] at h3
    have hk : tb (Kof (labD orbD x)) x = true := (Kof_spec hP hK hl x).2 ⟨hx, hxi, rfl⟩
    rw [tb_eq] at hk
    have hq' := h3 x hk
    rw [← inQc_eq hP hx, inQc, tb_eq, hq']
    rfl
  simp only [leafOK, hU]
  simp only [leafM, Bool.or_eq_true] at h
  rw [← hlen, ← htm]
  rcases h with (h | h) | h
  · have h' : sumM szOf m 25 ≠ 63 := Nat.ne_of_beq_eq_false (by simpa using h)
    have h1 : (sumM szOf m 25 != 63) = true := bne_iff_ne.2 h'
    rw [h1, Bool.true_or, Bool.true_or]
  · rw [hQ h, Bool.or_true, Bool.true_or]
  · have h1 : (sumM tcOf m 25 == 15) = true := beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)
    rw [h1, Bool.or_true]

theorem t10CheckA_of {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j)
    (hO : ∀ d ∈ orbD, d.2 = maskN (memO P d.1) 1024) (hL : ∀ x < 1024, labOK P x = true)
    (hK : ∀ i < 25, kchk P i = true) (hC : ∀ i < 25, clsOK P i = true)
    (hR : ∀ i < 25, rowOK P i = true) (hD : dfsM rowM leafM R25L 0 R25 = true) :
    t10CheckA () = true := by
  have hlab : ∀ x < 1024, isInv (ofCode x) = true → labD orbD x < 25 := by
    intro x hx hi
    have := hL x hx
    rw [labOK, isInvc_eq hP hx, hi, Bool.not_true, Bool.false_or, Nat.blt_eq] at this
    exact this
  simp only [t10CheckA]
  rw [pairsT_eq fun x hx => clsIdx_eq hP hO hx, Bool.and_eq_true, List.all_eq_true,
    List.all_eq_true]
  refine ⟨fun p hp => ?_, fun S hS => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (by simpa only [pairsC] using hp)
    simp only [List.mem_filter, List.mem_range] at hx
    exact decide_eq_true (hlab x hx.1 hx.2)
  · have hR25 : List.range 25 = R25L := by decide
    rw [hR25] at hS
    have h25 : ∀ a ∈ R25L, a < 25 := by decide
    obtain ⟨m, hm, hQ⟩ := dfsM_spec (cm := cmOf (commTab pairsC))
      (fun a ha b hb => cm_eq hP hK hR (h25 a ha) (h25 b hb)) hD S hS fun s hs => by
        rw [tb_eq, testBit_R25]
        exact decide_eq_true (h25 s (mem_of_mem_cliques hS s hs))
    exact leafOK_of hP hK hC hlab (fun i => by rw [hm i]; simp) hQ

end CFSG.KC.T10Code
