module

public import Certificates.Data.Kernel.HeLoc.Tree
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import CFSG.Certificates.Kernel.MonsterB.BfsReplaySound
public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
public import CFSG.Certificates.Kernel.RankThree.F2Perm
import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KC.HeLoc

open CFSG.KS.SporSch CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KC.Misc.Clos (allN_iff)
open CFSG.KS (bAnd_iff)

variable {n : Nat}

@[expose] noncomputable def treePerm (gp : Nat → Equiv.Perm (Fin n)) (P Lb : Nat → Nat) :
    Nat → Equiv.Perm (Fin n)
  | i => if h : 0 < i ∧ P i < i then gp (Lb i) * treePerm gp P Lb (P i) else 1
termination_by i => i
decreasing_by exact h.2

@[expose] def treeArr (n : Nat) (gs : Array (Array Nat)) (P Lb : Nat → Nat) : Nat → Array Nat
  | i => if h : 0 < i ∧ P i < i then compA n gs[Lb i]! (treeArr n gs P Lb (P i)) else idA n
termination_by i => i
decreasing_by exact h.2

variable {gp : Nat → Equiv.Perm (Fin n)} {P Lb : Nat → Nat} {gs : Array (Array Nat)}
  {g : Nat → Nat → Nat} {ng N : Nat}

theorem treePerm_zero : treePerm gp P Lb 0 = 1 := by
  rw [treePerm]
  simp

theorem treePerm_pos {i : Nat} (h : 0 < i ∧ P i < i) :
    treePerm gp P Lb i = gp (Lb i) * treePerm gp P Lb (P i) := by
  rw [treePerm, dif_pos h]

theorem treeArr_zero : treeArr n gs P Lb 0 = idA n := by
  rw [treeArr]
  simp

theorem treeArr_pos {i : Nat} (h : 0 < i ∧ P i < i) :
    treeArr n gs P Lb i = compA n gs[Lb i]! (treeArr n gs P Lb (P i)) := by
  rw [treeArr, dif_pos h]

theorem size_treeArr (i : Nat) : (treeArr n gs P Lb i).size = n := by
  rw [treeArr]
  split
  · simp [compA]
  · simp [idA]

@[expose] def TreeOK (ng N : Nat) (P Lb : Nat → Nat) : Prop :=
  ∀ i < N, 0 < i → P i < i ∧ Lb i < ng

theorem treeOK_of {ng N : Nat} {P Lb : Nat → Nat}
    (h : ∀ i < N, 0 < i → treeAtK ng P Lb i = true) : TreeOK ng N P Lb := by
  intro i hi h0
  have h1 := h i hi h0
  unfold treeAtK at h1
  rw [bAnd_iff, Nat.blt_eq, Nat.blt_eq] at h1
  exact h1

theorem beq_zero_false {i : Nat} (hi : 0 < i) : Nat.beq i 0 = false :=
  Bool.eq_false_iff.2 fun h => by
    have := Nat.eq_of_beq_eq_true h
    omega

theorem trV_zero (x : Nat) : trV g P Lb 0 0 x = x := rfl

theorem trV_succ_zero (f x : Nat) : trV g P Lb (f + 1) 0 x = x := rfl

theorem trV_succ_pos {f i : Nat} (hi : 0 < i) (x : Nat) :
    trV g P Lb (f + 1) i x = g (Lb i) (trV g P Lb f (P i) x) := by
  change Bool.rec (motive := fun _ => Nat) (g (Lb i) (trV g P Lb f (P i) x)) x (Nat.beq i 0) = _
  rw [beq_zero_false hi]

theorem repF_trV (ht : TreeOK ng N P Lb) (hg : ∀ k < ng, RepF n (g k) (gp k)) :
    ∀ f i, i ≤ f → i < N → RepF n (trV g P Lb f i) (treePerm gp P Lb i) := by
  intro f
  induction f with
  | zero =>
    intro i hi _
    have : i = 0 := by omega
    subst this
    rw [treePerm_zero]
    exact RepF.one
  | succ f ih =>
    intro i hi hN
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [treePerm_zero]
      exact fun x _ => trV_succ_zero f x
    · obtain ⟨hp, hl⟩ := ht i hN h0
      rw [treePerm_pos ⟨h0, hp⟩]
      have h1 := (hg (Lb i) hl).comp (ih (P i) (by omega) (by omega))
      intro x hx
      rw [trV_succ_pos h0]
      exact h1 x hx

theorem rep_treeArr (ht : TreeOK ng N P Lb) (hg : ∀ k < ng, Rep n gs[k]! (gp k)) :
    ∀ i < N, Rep n (treeArr n gs P Lb i) (treePerm gp P Lb i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hN
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [treePerm_zero, treeArr_zero]
      exact rep_idA
    · obtain ⟨hp, hl⟩ := ht i hN h0
      rw [treePerm_pos ⟨h0, hp⟩, treeArr_pos ⟨h0, hp⟩]
      exact rep_compA (hg (Lb i) hl) (ih (P i) hp (by omega))

theorem par_iff {a b : Nat} (ha : a < 2) (hb : b < 2) :
    ((a = 0 ↔ b = 0) ↔ (a + b) % 2 = 0) := by
  interval_cases a <;> interval_cases b <;> decide

theorem trQ_spec {H K : Subgroup (Equiv.Perm (Fin n))} {q : Nat → Nat} (ht : TreeOK ng N P Lb)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, (a * b ∈ K ↔ (a ∈ K ↔ b ∈ K)))
    (hgH : ∀ k < ng, gp k ∈ H) (hq : ∀ k < ng, (gp k ∈ K ↔ q k = 0)) (hq2 : ∀ k < ng, q k < 2) :
    ∀ f i, i ≤ f → i < N → treePerm gp P Lb i ∈ H ∧
      (treePerm gp P Lb i ∈ K ↔ trQ q P Lb f i = 0) ∧ trQ q P Lb f i < 2 := by
  intro f
  induction f with
  | zero =>
    intro i hi _
    have : i = 0 := by omega
    subst this
    rw [treePerm_zero]
    exact ⟨H.one_mem, ⟨fun _ => rfl, fun _ => K.one_mem⟩, Nat.zero_lt_two⟩
  | succ f ih =>
    intro i hi hN
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [treePerm_zero]
      exact ⟨H.one_mem, ⟨fun _ => rfl, fun _ => K.one_mem⟩, Nat.zero_lt_two⟩
    · obtain ⟨hp, hl⟩ := ht i hN h0
      obtain ⟨h1, h2, h3⟩ := ih (P i) (by omega) (by omega)
      have e : trQ q P Lb (f + 1) i = (q (Lb i) + trQ q P Lb f (P i)) % 2 := by
        change Bool.rec (motive := fun _ => Nat) ((q (Lb i) + trQ q P Lb f (P i)) % 2) 0
          (Nat.beq i 0) = _
        rw [beq_zero_false h0]
      rw [treePerm_pos ⟨h0, hp⟩, e, hmul _ (hgH _ hl) _ h1, hq _ hl, h2]
      refine ⟨H.mul_mem (hgH _ hl) h1, par_iff (hq2 _ hl) h3, Nat.mod_lt _ (by norm_num)⟩

theorem arr_eq_of_rep {t u : Array Nat} {x : Equiv.Perm (Fin n)} (ht : t.size = n)
    (hu : u.size = n) (hxt : Rep n t x) (hxu : Rep n u x) : t = u := by
  apply Array.ext (by rw [ht, hu])
  intro i h1 h2
  have hi : i < n := by rwa [ht] at h1
  rw [← getElem!_pos t i h1, ← getElem!_pos u i h2, hxt ⟨i, hi⟩, hxu ⟨i, hi⟩]

theorem edges_of_edgeAtK {H K : Subgroup (Equiv.Perm (Fin n))} {q : Nat → Nat}
    {E : Nat → Nat → Nat} {bs : List Nat} (ht : TreeOK ng N P Lb)
    (hg : ∀ k < ng, RepF n (g k) (gp k)) (hgs : ∀ k < ng, Rep n gs[k]! (gp k))
    (hmul : ∀ a ∈ H, ∀ b ∈ H, (a * b ∈ K ↔ (a ∈ K ↔ b ∈ K)))
    (hgH : ∀ k < ng, gp k ∈ H) (hq : ∀ k < ng, (gp k ∈ K ↔ q k = 0)) (hq2 : ∀ k < ng, q k < 2)
    (hbs : ∀ b ∈ bs, b < n)
    (hF : ∀ x ∈ H, ∀ y ∈ H, (x ∈ K ↔ y ∈ K) →
      (∀ b (hb : b ∈ bs), (x ⟨b, hbs b hb⟩ : Nat) = y ⟨b, hbs b hb⟩) → x = y)
    (hE : ∀ i < N, edgeAtK g q P Lb E N N ng bs i = true) :
    ∀ i < N, ∀ k < ng, E i k < N ∧
      treeArr n gs P Lb (E i k) = compA n gs[k]! (treeArr n gs P Lb i) := by
  intro i hi k hk
  have h1 := (allN_iff _ _).1 (hE i hi) k hk
  simp only [bAnd_iff, Nat.blt_eq] at h1
  obtain ⟨hlt, heq, hpar⟩ := h1
  have hR1 := repF_trV ht hg N (E i k) hlt.le hlt
  have hR2 := repF_trV ht hg N i hi.le hi
  have hQ1 := trQ_spec ht hmul hgH hq hq2 N (E i k) hlt.le hlt
  have hQ2 := trQ_spec ht hmul hgH hq hq2 N i hi.le hi
  have hpe := Nat.eq_of_beq_eq_true hpar
  have hperm : treePerm gp P Lb (E i k) = gp k * treePerm gp P Lb i := by
    refine hF _ hQ1.1 _ (H.mul_mem (hgH k hk) hQ2.1) ?_ fun b hb => ?_
    · rw [hmul _ (hgH k hk) _ hQ2.1, hQ1.2.1, hq k hk, hQ2.2.1, hpe]
      exact (par_iff (hq2 k hk) hQ2.2.2).symm
    · have e := (eqOnL_iff _ _ _).1 heq b hb
      rw [← hR1 b (hbs b hb), e, Equiv.Perm.mul_apply, hR2 b (hbs b hb)]
      exact (hg k hk) _ (treePerm gp P Lb i _).2
  refine ⟨hlt, arr_eq_of_rep (x := treePerm gp P Lb (E i k)) (size_treeArr _) (by simp [compA])
    ?_ ?_⟩
  · exact rep_treeArr ht hgs _ hlt
  · rw [hperm]
    exact rep_compA (hgs k hk) (rep_treeArr ht hgs i hi)

theorem keyV_eq (ps : List Nat) (h : Nat → Nat) :
    keyV n ps h = Nat.ofDigits n (ps.map h) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change h p + n * keyV n ps h = _
    rw [ih, List.map_cons, Nat.ofDigits_cons]

theorem keys_inj_of_sortAtK {key SK SKI : Nat → Nat}
    (h : ∀ j < N, sortAtK key SK SKI N j = true) :
    ∀ a < N, ∀ b < N, key a = key b → a = b := by
  have hs : ∀ j < N, SKI j < N ∧ SK (SKI j) = j ∧ (j + 1 < N → key (SK j) < key (SK (j + 1))) := by
    intro j hj
    have h1 := h j hj
    unfold sortAtK at h1
    rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h1
    refine ⟨h1.1, Nat.eq_of_beq_eq_true h1.2.1, fun hj1 => ?_⟩
    have h2 := h1.2.2
    rw [show Nat.blt (Nat.succ j) N = true by simpa [Nat.blt_eq] using hj1] at h2
    simpa [Nat.blt_eq] using h2
  have hmono : ∀ j d, j + d + 1 < N → key (SK j) < key (SK (j + d + 1)) := by
    intro j d
    induction d with
    | zero => intro hd; exact (hs j (by omega)).2.2 (by omega)
    | succ d ih =>
      intro hd
      exact lt_trans (ih (by omega)) ((hs (j + d + 1) (by omega)).2.2 (by omega))
  intro a ha b hb e
  obtain ⟨pa, ea, -⟩ := hs a ha
  obtain ⟨pb, eb, -⟩ := hs b hb
  by_contra hne
  have hp : SKI a ≠ SKI b := fun hp => hne (by rw [← ea, hp, eb])
  rcases Nat.lt_or_gt_of_ne hp with hl | hl
  · have := hmono (SKI a) (SKI b - SKI a - 1) (by omega)
    rw [show SKI a + (SKI b - SKI a - 1) + 1 = SKI b by omega, ea, eb, e] at this
    exact lt_irrefl _ this
  · have := hmono (SKI b) (SKI a - SKI b - 1) (by omega)
    rw [show SKI b + (SKI a - SKI b - 1) + 1 = SKI a by omega, ea, eb, e] at this
    exact lt_irrefl _ this

theorem keyA_treeArr (ht : TreeOK ng N P Lb) (hg : ∀ k < ng, RepF n (g k) (gp k))
    (hgs : ∀ k < ng, Rep n gs[k]! (gp k)) {ps : List Nat} (hps : ∀ p ∈ ps, p < n) {a : Nat}
    (ha : a < N) : keyA n ps (treeArr n gs P Lb a) = keyV n ps (trV g P Lb N a) := by
  rw [keyV_eq, keyA]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [(rep_treeArr ht hgs a ha) ⟨p, hps p hp⟩, repF_trV ht hg N a ha.le ha p (hps p hp)]

theorem enumBfs_tree {ps : List Nat} {fuel : Nat} {E : Nat → Nat → Nat}
    (ht : TreeOK ng N P Lb) (hgs : ∀ k < ng, Rep n gs[k]! (gp k)) (hsz : gs.size = ng)
    (hN : 0 < N) (hfuel : N ≤ fuel)
    (hkey : ∀ a < N, ∀ b < N, keyA n ps (treeArr n gs P Lb a) = keyA n ps (treeArr n gs P Lb b) →
      a = b)
    (hE : ∀ i < N, ∀ k < ng, E i k < N ∧
      treeArr n gs P Lb (E i k) = compA n gs[k]! (treeArr n gs P Lb i))
    (hrep : CFSG.KC.Bfs.replayOK E ng N = true) :
    (enumBfs n gs ps fuel).pts = Array.ofFn (n := N) fun i => treeArr n gs P Lb i.val := by
  have _ := ht
  have _ := hgs
  set L : Array (Array Nat) := Array.ofFn (n := N) fun i => treeArr n gs P Lb i.val with hL
  have hLs : L.size = N := by simp [hL]
  have hget : ∀ i < N, L[i]! = treeArr n gs P Lb i := fun i hi => by
    rw [hL, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  unfold enumBfs
  rw [CFSG.KC.Bfs.arrBfs_eq]
  change (CFSG.KC.Bfs.gBfs (leftA n gs) gs.size (keyA n ps) (idA n) fuel).1 = L
  refine CFSG.KC.Bfs.gBfs_eq_of_replay (E := E) (by omega) ?_ ?_ ?_ ?_ (by omega)
  · rw [hget 0 hN, treeArr_zero]
  · intro a ha b hb e
    rw [hLs] at ha hb
    rw [hget a ha, hget b hb] at e
    exact hkey a ha b hb e
  · intro i hi k hk
    rw [hLs] at hi
    rw [hsz] at hk
    obtain ⟨h1, h2⟩ := hE i hi k hk
    refine ⟨by rw [hLs]; exact h1, ?_⟩
    rw [hget _ h1, hget i hi, h2]
    rfl
  · rw [hLs, hsz]
    exact hrep

theorem enumOK_tree {ps : List Nat} {fuel : Nat} {E : Nat → Nat → Nat}
    (ht : TreeOK ng N P Lb) (hgs : ∀ k < ng, Rep n gs[k]! (gp k)) (hsz : gs.size = ng)
    (hN : 0 < N) (hfuel : N ≤ fuel)
    (hkey : ∀ a < N, ∀ b < N, keyA n ps (treeArr n gs P Lb a) = keyA n ps (treeArr n gs P Lb b) →
      a = b)
    (hE : ∀ i < N, ∀ k < ng, E i k < N ∧
      treeArr n gs P Lb (E i k) = compA n gs[k]! (treeArr n gs P Lb i)) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true := by
  set S : Finset (Array Nat) := (Finset.range N).image (treeArr n gs P Lb) with hSdef
  have hmemS : ∀ x, x ∈ S ↔ ∃ i < N, treeArr n gs P Lb i = x := by
    intro x
    simp [hSdef]
  have hS : ∀ x, CFSG.KC.Bfs.Reach (leftA n gs) gs.size (idA n) x ↔ x ∈ S := by
    intro x
    constructor
    · intro h
      induction h with
      | root => exact (hmemS _).2 ⟨0, hN, treeArr_zero⟩
      | step k hk _ ih =>
        obtain ⟨i, hi, rfl⟩ := (hmemS _).1 ih
        rw [hsz] at hk
        obtain ⟨h1, h2⟩ := hE i hi k hk
        exact (hmemS _).2 ⟨E i k, h1, h2⟩
    · intro h
      obtain ⟨i, hi, rfl⟩ := (hmemS _).1 h
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        rcases Nat.eq_zero_or_pos i with rfl | h0
        · rw [treeArr_zero]
          exact CFSG.KC.Bfs.Reach.root
        · obtain ⟨hp, hl⟩ := ht i hi h0
          rw [treeArr_pos ⟨h0, hp⟩]
          exact CFSG.KC.Bfs.Reach.step (Lb i) (by rw [hsz]; exact hl)
            (ih (P i) hp (by omega) ((hmemS _).2 ⟨P i, by omega, rfl⟩))
  have hv : ∀ x ∈ S, validA n x = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS _).1 hx
    exact CFSG.RankThree.Native.F2.validA_of_rep (rep_treeArr ht hgs i hi)
  have hk : ∀ x ∈ S, ∀ y ∈ S, keyA n ps x = keyA n ps y → x = y := by
    intro x hx y hy e
    obtain ⟨a, ha, rfl⟩ := (hmemS _).1 hx
    obtain ⟨b, hb, rfl⟩ := (hmemS _).1 hy
    rw [hkey a ha b hb e]
  have hc : S.card ≤ fuel := le_trans Finset.card_image_le (by simpa using hfuel)
  have hspec := CFSG.KC.Bfs.arrBfs_spec S hS hv hk hc
  unfold enumOK enumBfs
  rw [hspec.1, Bool.and_true, allLt_iff]
  intro k hk
  rw [hsz] at hk
  exact CFSG.RankThree.Native.F2.validA_of_rep (hgs k hk)

end CFSG.KC.HeLoc

end
