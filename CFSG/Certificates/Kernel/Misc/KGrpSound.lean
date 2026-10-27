module

public import Certificates.Data.Kernel.Misc.KGrp
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.GH74.KGroups.ClassCount

public section

namespace CFSG.KC.Misc.KG

open Equiv CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.GH74.KGroups

variable {n : ℕ}

theorem beq_true_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem notB_iff {a : Bool} : notB a = true ↔ ¬ a = true := by
  cases a <;> simp [notB]

theorem impB_iff {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [impB]

theorem allL_iff (L : List ℕ) (f : ℕ → Bool) : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL]
  | cons x L ih =>
    change andB (f x) (allL L f) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem anyL_iff (L : List ℕ) (f : ℕ → Bool) : anyL L f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => simp [anyL]
  | cons x L ih =>
    change orB (f x) (anyL L f) = true ↔ _
    rw [orB_iff, ih]
    simp

theorem memL_iff (c : ℕ) (L : List ℕ) : memL c L = true ↔ c ∈ L := by
  rw [memL, anyL_iff]
  simp

theorem pcode_mul (hn : n ≤ 32) (a b : Perm (Fin n)) :
    P.mul n (pcode a) (pcode b) = pcode (a * b) := ((pcode_enc hn).enc_mul a b).symm

theorem pcode_one (hn : n ≤ 32) : P.one n = pcode (1 : Perm (Fin n)) := (pcode_enc hn).enc_one.symm

theorem pcode_inj (hn : n ≤ 32) {a b : Perm (Fin n)} : pcode a = pcode b ↔ a = b :=
  ⟨fun h => (pcode_enc hn).inj h, congrArg _⟩

theorem pcode_pow (hn : n ≤ 32) (g : Perm (Fin n)) (k : ℕ) : P.pow n (pcode g) k = pcode (g ^ k) := by
  induction k with
  | zero => exact (pcode_one hn).trans (by rw [pow_zero])
  | succ k ih =>
    change P.mul n (P.pow n (pcode g) k) (pcode g) = _
    rw [ih, pcode_mul hn, pow_succ]

theorem beq_iff (hn : n ≤ 32) (a b : Perm (Fin n)) : Nat.beq (pcode a) (pcode b) = true ↔ a = b := by
  rw [beq_true_iff, pcode_inj hn]

theorem isOne_iff (hn : n ≤ 32) (g : Perm (Fin n)) : isOne n (pcode g) = true ↔ g = 1 := by
  rw [isOne, pcode_one hn, beq_iff hn]

theorem comm_iff (hn : n ≤ 32) (a b : Perm (Fin n)) :
    P.comm n (pcode a) (pcode b) = true ↔ a * b = b * a := by
  rw [P.comm, pcode_mul hn, pcode_mul hn, beq_iff hn]

theorem cubeOne_iff (hn : n ≤ 32) (g : Perm (Fin n)) : cubeOne n (pcode g) = true ↔ g ^ 3 = 1 := by
  rw [cubeOne, pcode_pow hn, isOne_iff hn]

theorem memL_map_iff (hn : n ≤ 32) (g : Perm (Fin n)) (L : List (Perm (Fin n))) :
    memL (pcode g) (L.map pcode) = true ↔ g ∈ L := by
  rw [memL_iff, List.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    rwa [← (pcode_inj hn).1 he]
  · exact fun h => ⟨g, h, rfl⟩

theorem pow2K_eq (hn : n ≤ 32) (x : Perm (Fin n)) :
    pow2K n (pcode x) = ([1, x, x ^ 2] : List (Perm (Fin n))).map pcode := by
  simp [pow2K, pcode_pow hn, pcode_one hn]

theorem pow3K_eq (hn : n ≤ 32) (x y : Perm (Fin n)) :
    pow3K n (pcode x) (pcode y) = (pow3list x y).map pcode := by
  simp [pow3K, pow3list, pcode_pow hn, pcode_mul hn, pcode_one hn]

theorem ordGo_iff (hn : n ≤ 32) (g : Perm (Fin n)) (k j : ℕ) :
    ordGo n (pcode g) k (pcode (g ^ j)) = true ↔ (∀ i < k, g ^ (j + i) ≠ 1) ∧ g ^ (j + k) = 1 := by
  induction k generalizing j with
  | zero =>
    change isOne n (pcode (g ^ j)) = true ↔ _
    rw [isOne_iff hn]
    simp
  | succ k ih =>
    change letB (pcode (g ^ j)) (fun a => andB (notB (isOne n a))
      (ordGo n (pcode g) k (P.mul n a (pcode g)))) = true ↔ _
    rw [letB_eq, andB_iff, notB_iff, isOne_iff hn, pcode_mul hn, ← pow_succ, ih (j + 1)]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i hi => ?_, by rwa [show j + (k + 1) = j + 1 + k by omega]⟩
      rcases i with _ | i
      · simpa using h0
      · have := h1 i (by omega)
        rwa [show j + 1 + i = j + (i + 1) by omega] at this
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, by
        rwa [show j + 1 + k = j + (k + 1) by omega]⟩
      have := h1 (i + 1) (by omega)
      rwa [show j + (i + 1) = j + 1 + i by omega] at this

theorem ordK_iff (hn : n ≤ 32) (g : Perm (Fin n)) {m : ℕ} (hm : 0 < m) :
    ordK n (pcode g) m = true ↔ orderOf g = m := by
  have h := ordGo_iff hn g (m - 1) 1
  rw [pow_one] at h
  rw [ordK, Nat.sub_eq, h, orderOf_eq_iff hm, show 1 + (m - 1) = m by omega]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun i hi hi0 => ?_⟩
    have := h1 (i - 1) (by omega)
    rwa [show 1 + (i - 1) = i by omega] at this
  · rintro ⟨h2, h1⟩
    exact ⟨fun i hi => h1 (1 + i) (by omega) (by omega), h2⟩

theorem evalWK_eq (hn : n ≤ 32) (a b : Perm (Fin n)) (w : List Bool) :
    evalWK n (pcode a) (pcode b) w = pcode (evalW a b w) := by
  induction w with
  | nil => exact pcode_one hn
  | cons x w ih =>
    change P.mul n (Bool.rec (motive := fun _ => ℕ) (pcode a) (pcode b) x)
      (evalWK n (pcode a) (pcode b) w) = _
    rw [ih]
    cases x
    · exact pcode_mul hn a _
    · exact pcode_mul hn b _

theorem pairK_iff (hn : n ≤ 32) (a b : Perm (Fin n)) (ws : List (List Bool × ℕ))
    (hws : ∀ wk ∈ ws, 0 < wk.2) : pairK n (pcode a) (pcode b) ws = true ↔ PairInv ws a b := by
  induction ws with
  | nil => simp [pairK, PairInv]
  | cons p ws ih =>
    obtain ⟨w, m⟩ := p
    change andB (ordK n (evalWK n (pcode a) (pcode b) w) m) (pairK n (pcode a) (pcode b) ws) =
      true ↔ _
    rw [andB_iff, evalWK_eq hn, ordK_iff hn _ (hws _ List.mem_cons_self),
      ih fun wk h => hws wk (List.mem_cons_of_mem _ h)]
    simp [PairInv]

variable {H : Subgroup (Perm (Fin n))} {N : ℕ} {E : ℕ → ℕ}

theorem exact_forall (hE : ExactList pcode H N E) (F : ℕ → Bool) (h : ∀ k < N, F (E k) = true) :
    ∀ g ∈ H, F (pcode g) = true := by
  intro g hg
  obtain ⟨k, hk, he⟩ := hE.2.1 g hg
  rw [he]
  exact h k hk

theorem exact_mem (hn : n ≤ 32) (hE : ExactList pcode H N E) {k : ℕ} (hk : k < N)
    {g : Perm (Fin n)} (h : pcode g = E k) : g ∈ H := by
  obtain ⟨g', hg', he⟩ := hE.1 k hk
  rwa [← (pcode_inj hn).1 (he.trans h.symm)]

theorem cntN_eq_card (N : ℕ) (f : ℕ → Bool) :
    cntN N f = ((Finset.range N).filter fun k => f k = true).card := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change cntN N f + Bool.rec (motive := fun _ => ℕ) 0 1 (f N) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases hf : f N
    · simp
    · rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]

theorem exact_cnt (hn : n ≤ 32) (hE : ExactList pcode H N E) (F : ℕ → Bool)
    (p : Perm (Fin n) → Prop) (hF : ∀ g ∈ H, F (pcode g) = true ↔ p g) :
    cntN N (fun k => F (E k)) = Nat.card {g // g ∈ H ∧ p g} := by
  classical
  rw [cntN_eq_card]
  have e1 : Nat.card {k // k < N ∧ F (E k) = true} =
      ((Finset.range N).filter fun k => F (E k) = true).card := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun k => by simp)
  rw [← e1]
  symm
  let f : {g // g ∈ H ∧ p g} → {k // k < N ∧ F (E k) = true} := fun g =>
    ⟨(hE.2.1 g.1 g.2.1).choose, (hE.2.1 g.1 g.2.1).choose_spec.1, by
      rw [← (hE.2.1 g.1 g.2.1).choose_spec.2]
      exact (hF _ g.2.1).2 g.2.2⟩
  refine Nat.card_eq_of_bijective f ⟨fun g g' h => ?_, fun k => ?_⟩
  · have h1 := congrArg Subtype.val h
    have e := (hE.2.1 g.1 g.2.1).choose_spec.2.trans
      ((congrArg E h1).trans (hE.2.1 g'.1 g'.2.1).choose_spec.2.symm)
    exact Subtype.ext ((pcode_inj hn).1 e)
  · obtain ⟨g, hg, he⟩ := hE.1 k.1 k.2.1
    have hp : p g := (hF g hg).1 (by rw [he]; exact k.2.2)
    refine ⟨⟨g, hg, hp⟩, Subtype.ext ?_⟩
    have hs := (hE.2.1 g hg).choose_spec
    exact hE.2.2 _ hs.1 _ k.2.1 (hs.2.symm.trans he)

theorem cnt_ord (hn : n ≤ 32) (hE : ExactList pcode H N E) {m : ℕ} (hm : 0 < m) :
    cntN N (fun k => ordK n (E k) m) = Nat.card {g // g ∈ H ∧ orderOf g = m} :=
  exact_cnt hn hE (fun c => ordK n c m) _ fun g _ => ordK_iff hn g hm

theorem cnt_cent (hn : n ≤ 32) (hE : ExactList pcode H N E) {r : Perm (Fin n)} {R : ℕ}
    (hr : pcode r = R) : cntN N (fun k => P.comm n (E k) R) = centCard H r := by
  rw [← hr]
  exact exact_cnt hn hE (fun c => P.comm n c (pcode r)) _ fun g _ => comm_iff hn g r

theorem fib_card (hn : n ≤ 32) (hE : ExactList pcode H N E) {a : Perm (Fin n)} {A ob : ℕ}
    (ha : pcode a = A) (hob : 0 < ob) {ws : List (List Bool × ℕ)} (hws : ∀ wk ∈ ws, 0 < wk.2) :
    cntN N (fibAt n E A ob ws) = Nat.card {y // y ∈ H ∧ orderOf y = ob ∧ PairInv ws a y} := by
  have e : fibAt n E A ob ws = fun k => andB (ordK n (E k) ob) (pairK n A (E k) ws) := by
    funext k
    rw [fibAt, letB_eq]
  rw [e, ← ha]
  refine exact_cnt hn hE (fun c => andB (ordK n c ob) (pairK n (pcode a) c ws)) _ fun g _ => ?_
  rw [andB_iff, ordK_iff hn g hob, pairK_iff hn a g ws hws]

theorem cent_sound (hn : n ≤ 32) (hE : ExactList pcode H N E) {a b : Perm (Fin n)} {A B : ℕ}
    (ha : pcode a = A) (hb : pcode b = B) (h : ∀ k < N, centAt n E A B k = true) :
    ∀ σ ∈ H, σ * a = a * σ → σ * b = b * σ → σ = 1 := by
  intro σ hσ h1 h2
  have := exact_forall hE (fun s => impB (andB (P.comm n s A) (P.comm n s B)) (isOne n s))
    (fun k hk => by have := h k hk; rwa [centAt, letB_eq] at this) σ hσ
  rw [impB_iff, andB_iff, ← ha, ← hb, comm_iff hn, comm_iff hn, isOne_iff hn] at this
  exact this ⟨h1, h2⟩

theorem mem_CL (hn : n ≤ 32) (hE : ExactList pcode H N E) {r : Perm (Fin n)} {R : ℕ}
    (hr : pcode r = R) {CL : List ℕ} (hc : ∀ k < N, inCAt n E R CL k = true) :
    ∀ g ∈ H, g * r = r * g → pcode g ∈ CL := by
  intro g hg hgr
  have := exact_forall hE (fun g => impB (P.comm n g R) (memL g CL))
    (fun k hk => by have := hc k hk; rwa [inCAt, letB_eq] at this) g hg
  rw [impB_iff, ← hr, comm_iff hn, memL_iff] at this
  exact this hgr

theorem mem_CL3 (hn : n ≤ 32) (hE : ExactList pcode H N E) {r : Perm (Fin n)} {R : ℕ}
    (hr : pcode r = R) {CL : List ℕ} (hc : ∀ k < N, inC3At n E R CL k = true) :
    ∀ g ∈ H, g * r = r * g → g ^ 3 = 1 → pcode g ∈ CL := by
  intro g hg hgr hg3
  have := exact_forall hE (fun g => impB (andB (P.comm n g R) (cubeOne n g)) (memL g CL))
    (fun k hk => by have := hc k hk; rwa [inC3At, letB_eq] at this) g hg
  rw [impB_iff, andB_iff, ← hr, comm_iff hn, cubeOne_iff hn, memL_iff] at this
  exact this ⟨hgr, hg3⟩

theorem e9_sound (hn : n ≤ 32) (hE : ExactList pcode H N E) {r : Perm (Fin n)} {R : ℕ}
    (hr : pcode r = R) {CL : List ℕ} (hc : ∀ k < N, inC3At n E R CL k = true)
    (h : e9K n CL = true) : E9At H r := by
  intro X hX hX1 Y hY hX3 hY3 hXY hXr hYr
  have h1 := (allL_iff _ _).1 h _ (mem_CL3 hn hE hr hc X hX hXr hX3)
  have h2 := (allL_iff _ _).1 h1 _ (mem_CL3 hn hE hr hc Y hY hYr hY3)
  rw [impB_iff, andB_iff, andB_iff, andB_iff, notB_iff, isOne_iff hn, cubeOne_iff hn,
    cubeOne_iff hn, comm_iff hn, orB_iff, orB_iff, isOne_iff hn, beq_iff hn, pcode_pow hn,
    beq_iff hn] at h2
  exact h2 ⟨hX1, hX3, hY3, hXY⟩

theorem e27_sound (hn : n ≤ 32) (hE : ExactList pcode H N E) {X : Perm (Fin n)} {XK : ℕ}
    (hX : pcode X = XK) {CL : List ℕ} (hc : ∀ k < N, inC3At n E XK CL k = true)
    (h : e27K n XK CL = true) : E27At H X := by
  intro Y hY Z hZ hY3 hZ3 hXY hXZ hYZ
  have h1 := (allL_iff _ _).1 h _ (mem_CL3 hn hE hX hc Y hY hXY.symm hY3)
  have h2 := (allL_iff _ _).1 h1 _ (mem_CL3 hn hE hX hc Z hZ hXZ.symm hZ3)
  rw [impB_iff, comm_iff hn, orB_iff, ← hX, pow2K_eq hn, pow3K_eq hn, memL_map_iff hn,
    memL_map_iff hn] at h2
  exact h2 hYZ

theorem cent3_sound (hn : n ≤ 32) (hE : ExactList pcode H N E) {x : Perm (Fin n)} {XK : ℕ}
    (hx : pcode x = XK) {CL : List ℕ} (hc : ∀ k < N, inCAt n E XK CL k = true)
    (h : cent3K n XK CL = true) : Cent3At H x := by
  intro y hy hy3 hxy hyn k hk hkx hky
  have h1 := (allL_iff _ _).1 h _ (mem_CL hn hE hx hc y hy hxy.symm)
  rw [impB_iff, andB_iff, notB_iff, cubeOne_iff hn, ← hx, pow2K_eq hn, memL_map_iff hn] at h1
  have h2 := (allL_iff _ _).1 (h1 ⟨hy3, hyn⟩) _ (mem_CL hn hE hx hc k hk hkx)
  rw [impB_iff, comm_iff hn, pow3K_eq hn, memL_map_iff hn] at h2
  exact h2 hky

end CFSG.KC.Misc.KG

end
