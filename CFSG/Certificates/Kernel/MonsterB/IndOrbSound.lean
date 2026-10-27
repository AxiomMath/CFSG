module

public import Certificates.Data.Kernel.MonsterB.IndOrb
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound

public section

namespace CFSG.KC.IndOrb

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.U6Orb CFSG.Monster.B.TwoA.Census

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

theorem anyL_iff {α : Type} (f : α → Bool) (L : List α) :
    anyL f L = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => simp [anyL]
  | cons x L ih =>
    change orB (f x) (anyL f L) = true ↔ _
    rw [orB_eq_true, ih]
    simp

theorem bIf_true {c t : Bool} (h : bIf(c, t, true) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

section Perm

variable {P w I wI N : ℕ}

theorem invTabOK_sound (h : invTabOK P w I wI N = true) :
    ∀ p < N, fget P p w < N ∧ fget I (fget P p w) wI = p := by
  simp only [invTabOK, strictB_eq, allN_iff, andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem pt_inj (h : invTabOK P w I wI N = true) {p q : ℕ} (hp : p < N) (hq : q < N)
    (e : fget P p w = fget P q w) : p = q := by
  have h1 := (invTabOK_sound h p hp).2
  have h2 := (invTabOK_sound h q hq).2
  rw [e] at h1
  rw [← h1, h2]

theorem pt_surj (h : invTabOK P w I wI N = true) {x : ℕ} (hx : x < N) : ∃ p < N, fget P p w = x := by
  have hsub : (Finset.range N).image (fun p => fget P p w) ⊆ Finset.range N := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (invTabOK_sound h p (Finset.mem_range.1 hp)).1
  have hcard : ((Finset.range N).image (fun p => fget P p w)).card = (Finset.range N).card :=
    Finset.card_image_of_injOn fun p hp q hq e =>
      pt_inj h (Finset.mem_range.1 hp) (Finset.mem_range.1 hq) e
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have : x ∈ (Finset.range N).image (fun p => fget P p w) := by
    rw [heq]
    exact Finset.mem_range.2 hx
  obtain ⟨p, hp, e⟩ := Finset.mem_image.1 this
  exact ⟨p, Finset.mem_range.1 hp, e⟩

theorem pt_ix (h : invTabOK P w I wI N = true) {x : ℕ} (hx : x < N) :
    fget I x wI < N ∧ fget P (fget I x wI) w = x := by
  obtain ⟨p, hp, rfl⟩ := pt_surj h hx
  rw [(invTabOK_sound h p hp).2]
  exact ⟨hp, rfl⟩

@[expose] noncomputable def orbL (P w o n : ℕ) : List ℕ := (List.range' o n).map fun p => fget P p w

theorem mem_orbL {o n x : ℕ} : x ∈ orbL P w o n ↔ ∃ j < n, fget P (o + j) w = x := by
  simp only [orbL, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨p, ⟨j, hj, rfl⟩, e⟩
    exact ⟨j, hj, by simpa using e⟩
  · rintro ⟨j, hj, e⟩
    exact ⟨o + j, ⟨j, hj, by simp⟩, e⟩

theorem orbL_length (o n : ℕ) : (orbL P w o n).length = n := by simp [orbL]

theorem orbL_getElem {o n j : ℕ} (hj : j < (orbL P w o n).length) :
    (orbL P w o n)[j] = fget P (o + j) w := by
  simp [orbL]

theorem inOrb_iff {o n x : ℕ} :
    inOrb I wI N o n x = true ↔ x < N ∧ o ≤ fget I x wI ∧ fget I x wI < o + n := by
  simp only [inOrb, andB_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq]

theorem mem_orb (h : invTabOK P w I wI N = true) {o n x : ℕ} (hon : o + n ≤ N) :
    x ∈ orbL P w o n ↔ inOrb I wI N o n x = true := by
  rw [mem_orbL, inOrb_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have := invTabOK_sound h (o + j) (by omega)
    rw [this.2]
    exact ⟨this.1, by omega, by omega⟩
  · rintro ⟨hx, h1, h2⟩
    exact ⟨fget I x wI - o, by omega, by rw [Nat.add_sub_cancel' h1]; exact (pt_ix h hx).2⟩

theorem orbL_append (o a b : ℕ) : orbL P w o a ++ orbL P w (o + a) b = orbL P w o (a + b) := by
  have e := List.range'_append (s := o) (m := a) (n := b) (step := 1)
  rw [Nat.one_mul] at e
  simp only [orbL, ← List.map_append, e]

theorem orbL_perm (h : invTabOK P w I wI N = true) : (orbL P w 0 N).Perm (List.range N) := by
  have hnd : (orbL P w 0 N).Nodup := by
    refine List.Nodup.map_on (fun p hp q hq e => ?_) List.nodup_range'
    rw [List.mem_range'] at hp hq
    obtain ⟨i, hi, rfl⟩ := hp
    obtain ⟨j, hj, rfl⟩ := hq
    exact pt_inj h (by omega) (by omega) e
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun x => ?_
  rw [mem_orbL, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (invTabOK_sound h _ (by omega)).1
  · intro hx
    obtain ⟨p, hp, e⟩ := pt_surj h hx
    exact ⟨p, hp, by simpa using e⟩

end Perm

theorem mergeSort_eq_of_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    (l₁.mergeSort fun a b => decide (a ≤ b)) = l₂.mergeSort fun a b => decide (a ≤ b) := by
  have hs : ∀ l : List ℕ, (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) := fun l =>
    (List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l).imp
      fun h => by simpa using h
  exact List.Perm.eq_of_pairwise' (hs l₁) (hs l₂)
    ((List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm))

theorem mergeSort_range (N : ℕ) :
    ((List.range N).mergeSort fun a b => decide (a ≤ b)) = List.range N :=
  List.mergeSort_of_pairwise (List.pairwise_lt_range.imp fun h => by simpa using le_of_lt h)

section Orbit

variable {act : ℕ → ℕ → ℕ} {ng P w I wI N o n D wE root : ℕ}

theorem orbOK_sound (h : orbOK act ng P w o n D wE root = true) :
    fget P o w = root ∧ (∀ i < n, ∀ k < ng, tabE ng wE D i k < n ∧
      fget P (o + tabE ng wE D i k) w = act k (fget P (o + i) w)) ∧
      CFSG.KC.Bfs.replayOK (tabE ng wE D) ng n = true := by
  simp only [orbOK, strictB_eq, allN_iff, andB_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem orbOK_edge (h : orbOK act ng P w o n D wE root = true) {i k : ℕ} (hi : i < n)
    (hk : k < ng) : act k (fget P (o + i) w) ∈ orbL P w o n :=
  mem_orbL.2 ⟨_, ((orbOK_sound h).2.1 i hi k hk).1, ((orbOK_sound h).2.1 i hi k hk).2⟩

theorem orbOK_root (h : orbOK act ng P w o n D wE root = true) (hn : 0 < n) :
    root ∈ orbL P w o n :=
  mem_orbL.2 ⟨0, hn, by rw [Nat.add_zero]; exact (orbOK_sound h).1⟩

theorem orbOK_natBfs {act' : ℕ → ℕ → ℕ} (hact : ∀ k < ng, ∀ x < N, act' k x = act k x)
    (hinv : invTabOK P w I wI N = true) (h : orbOK act' ng P w o n D wE root = true)
    (hn : 0 < n) (hon : o + n ≤ N) {fuel : ℕ} (hf : n ≤ fuel) :
    (natBfs act ng root fuel).pts = (orbL P w o n).toArray ∧
      natCertOK act ng (fun u => decide (u < N)) root (natBfs act ng root fuel) = true := by
  obtain ⟨h0, hE', hr⟩ := orbOK_sound h
  have hE : ∀ i < n, ∀ k < ng, tabE ng wE D i k < n ∧
      fget P (o + tabE ng wE D i k) w = act k (fget P (o + i) w) := fun i hi k hk => by
    rw [← hact k hk _ (invTabOK_sound hinv _ (by omega)).1]
    exact hE' i hi k hk
  have hs : (orbL P w o n).toArray.size = n := by simp [orbL_length]
  have hget : ∀ j < n, (orbL P w o n).toArray[j]! = fget P (o + j) w := fun j hj => by
    rw [getElem!_pos _ j (by rw [hs]; exact hj), List.getElem_toArray, orbL_getElem]
  obtain ⟨h1, h2⟩ := CFSG.KC.Bfs.natBfs_of_replay (act := act) (ngen := ng)
    (valid := fun u => decide (u < N)) (root := root) (fuel := fuel) (L := (orbL P w o n).toArray)
    (E := tabE ng wE D) (by rw [hs]; exact hn) (by rw [hget 0 hn, Nat.add_zero, h0])
    (fun a ha b hb e => by
      rw [hs] at ha hb
      rw [hget a ha, hget b hb] at e
      have := pt_inj hinv (by omega) (by omega) e
      omega)
    (fun i hi k hk => by
      rw [hs] at hi
      obtain ⟨e1, e2⟩ := hE i hi k hk
      exact ⟨by rw [hs]; exact e1, by rw [hget _ e1, hget i hi, e2]⟩)
    (by rw [hs]; exact hr)
    (fun j hj => by
      rw [hs] at hj
      rw [hget j hj]
      exact decide_eq_true (invTabOK_sound hinv _ (by omega)).1)
    (by rw [hs]; exact hf)
  exact ⟨h1, h2⟩

end Orbit

theorem rangeOK_sound {G N M b o : ℕ} (h : rangeOK G N M b o = true) :
    (∀ i < N, fget G i 12 < N) ∧ ∀ i < M, b ≤ fget G (o + i) 12 := by
  simp only [rangeOK, strictB_eq, allN_iff, andB_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq] at h
  exact h

theorem gen2_zero (G0 G1 : ℕ) : gen2 G0 G1 0 = G0 := rfl

theorem gen2_ne {G0 G1 c : ℕ} (hc : c ≠ 0) : gen2 G0 G1 c = G1 := by
  have : Nat.beq c 0 = false := by
    cases e : Nat.beq c 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hc
  simp only [gen2, this]

theorem wordT_nil (G0 G1 i : ℕ) : wordT G0 G1 [] i = i := rfl

theorem wordT_cons (G0 G1 c : ℕ) (w : List ℕ) (i : ℕ) :
    wordT G0 G1 (c :: w) i = fget (gen2 G0 G1 c) (wordT G0 G1 w i) 12 := rfl

theorem fixOK_sound {G0 G1 : ℕ} {WS : List (List ℕ)} {cs : List ℕ} {P w o n b : ℕ}
    (h : fixOK G0 G1 WS cs P w o n b = true) :
    ∀ j < n, fget P (o + j) w ∈ cs ∨
      ∃ wd ∈ WS, wordT G0 G1 wd (b + fget P (o + j) w) ≠ b + fget P (o + j) w := by
  simp only [fixOK, strictB_eq, allN_iff, orB_eq_true, anyL_iff, Nat.beq_eq, notB_eq,
    Bool.not_eq_true', Nat.add_eq] at h
  intro j hj
  rcases h j hj with ⟨c, hc, e⟩ | ⟨wd, hw, e⟩
  · exact Or.inl (e ▸ hc)
  · refine Or.inr ⟨wd, hw, fun e' => ?_⟩
    rw [e', Nat.beq_refl] at e
    exact absurd e (by decide)

theorem fixAt_sound {G0 G1 : ℕ} {WS : List (List ℕ)} {x : ℕ} (h : fixAt G0 G1 WS x = true) :
    ∀ wd ∈ WS, wordT G0 G1 wd x = x := by
  simp only [fixAt, strictB_eq, allL_iff, Nat.beq_eq] at h
  exact h

theorem keyOK_sound {H m S I wI N o n : ℕ} (h : keyOK H m S I wI N o n = true) :
    ∀ i < m, inOrb I wI N o n (fget H i 12) = true ∧
      fget S (fget H i 12) 12 = fget H (m + i) 12 ∧
      (i + 1 < m → fget H i 12 < fget H (i + 1) 12) := by
  simp only [keyOK, strictB_eq, allN_iff, andB_eq_true, Nat.beq_eq, Nat.add_eq] at h
  intro i hi
  obtain ⟨h1, h2, h3⟩ := h i hi
  refine ⟨h1, h2, fun hi' => ?_⟩
  have := bIf_true h3 (by rw [Nat.blt_eq]; exact hi')
  rwa [Nat.blt_eq] at this

theorem strictMono_of_step {f : ℕ → ℕ} {m : ℕ} (h : ∀ i, i + 1 < m → f i < f (i + 1)) :
    ∀ i j, i < j → j < m → f i < f j := by
  intro i j hij hjm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact lt_trans (ih hij (by omega)) (h j hjm)
    · exact h i hjm

theorem nodup_keys {f : ℕ → ℕ} {m : ℕ} (h : ∀ i, i + 1 < m → f i < f (i + 1)) :
    ((List.range m).map f).Nodup := by
  refine List.Nodup.map_on (fun i hi j hj e => ?_) List.nodup_range
  rw [List.mem_range] at hi hj
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd e (ne_of_lt (strictMono_of_step h i j hij hj))
  · rfl
  · exact absurd e (ne_of_gt (strictMono_of_step h j i hij hi))

theorem mem_of_subset_nodup {l₁ l₂ : List ℕ} (hs : l₁ ⊆ l₂) (hn : l₁.Nodup)
    (hl : l₂.length ≤ l₁.length) {x : ℕ} (hx : x ∈ l₂) : x ∈ l₁ :=
  ((hn.subperm hs).perm_of_length_le hl).symm.subset hx

theorem foldl_set_get_of_not_mem :
    ∀ (l : List (ℕ × ℕ)) (t : Array ℕ) {x : ℕ}, x ∉ l.map Prod.fst →
      (l.foldl (fun t p => t.set! p.1 p.2) t)[x]! = t[x]!
  | [], _, _, _ => rfl
  | q :: l, t, x, hx => by
    rw [List.map_cons, List.mem_cons, not_or] at hx
    rw [List.foldl_cons, foldl_set_get_of_not_mem l _ hx.2]
    simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_ne (Ne.symm hx.1)]

theorem foldl_set_size :
    ∀ (l : List (ℕ × ℕ)) (t : Array ℕ), (l.foldl (fun t p => t.set! p.1 p.2) t).size = t.size
  | [], _ => rfl
  | q :: l, t => by
    rw [List.foldl_cons, foldl_set_size l]
    simp

theorem foldl_set_get :
    ∀ (l : List (ℕ × ℕ)) (t : Array ℕ), (l.map Prod.fst).Nodup → ∀ p ∈ l, p.1 < t.size →
      (l.foldl (fun t p => t.set! p.1 p.2) t)[p.1]! = p.2
  | [], _, _, p, hp, _ => absurd hp (List.not_mem_nil)
  | q :: l, t, hnd, p, hp, hlt => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [foldl_set_get_of_not_mem l _ hnd.1]
      simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_self_of_lt hlt]
    · exact foldl_set_get l _ hnd.2 p hp (by simpa using hlt)

theorem sigOK_sound {G0 G1 b P o n D S T ZI N oz nz : ℕ}
    (h : sigOK G0 G1 b P o n D S T ZI N oz nz = true) :
    ∀ j < n, inOrb ZI 12 N oz nz (fget S (fget P (o + j) 12) 12) = true ∧
      fget T (fget S (fget P (o + j) 12) 12) 12 = fget P (o + j) 12 ∧
      ∀ g < 2, fget S (fget P (o + tabE 2 12 D j g) 12) 12 =
        zActK G0 G1 b g (fget S (fget P (o + j) 12) 12) := by
  simp only [sigOK, strictB_eq, allN_iff, andB_eq_true, Nat.beq_eq, Nat.add_eq] at h
  exact h

theorem tauOK_sound {G0 G1 b P o n T ZI N : ℕ} (h : tauOK G0 G1 b P o n T ZI N = true) :
    ∀ j < n, inOrb ZI 12 N o n (fget T (fget P (o + j) 12) 12) = true ∧
      fget T (fget T (fget P (o + j) 12) 12) 12 = fget P (o + j) 12 ∧
      fget T (fget P (o + j) 12) 12 ≠ fget P (o + j) 12 ∧
      ∀ g < 2, fget T (zActK G0 G1 b g (fget P (o + j) 12)) 12 =
        zActK G0 G1 b g (fget T (fget P (o + j) 12) 12) := by
  simp only [tauOK, strictB_eq, allN_iff, andB_eq_true, Nat.beq_eq, Nat.add_eq, notB_eq,
    Bool.not_eq_true'] at h
  intro j hj
  obtain ⟨h1, h2, h3, h4⟩ := h j hj
  refine ⟨h1, h2, fun e => ?_, h4⟩
  rw [e, Nat.beq_refl] at h3
  exact absurd h3 (by decide)

theorem mapOK_sound {C P w o n b : ℕ} {f : ℕ → ℕ} (h : mapOK C P w o n b f = true) :
    ∀ j < n, fget C (b + fget P (o + j) w) 12 = f (fget P (o + j) w) := by
  simp only [mapOK, strictB_eq, allN_iff, Nat.beq_eq, Nat.add_eq] at h
  exact h

theorem backOK_sound {C P o n b a S I N oz nz : ℕ} (h : backOK C P o n b a S I N oz nz = true) :
    ∀ j < n, a ≤ fget C (b + fget P (o + j) 12) 12 ∧
      inOrb I 12 N oz nz (fget C (b + fget P (o + j) 12) 12 - a) = true ∧
      fget S (fget C (b + fget P (o + j) 12) 12 - a) 12 = fget P (o + j) 12 := by
  simp only [backOK, strictB_eq, allN_iff, andB_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.add_eq,
    Nat.sub_eq] at h
  exact h

end CFSG.KC.IndOrb

end
