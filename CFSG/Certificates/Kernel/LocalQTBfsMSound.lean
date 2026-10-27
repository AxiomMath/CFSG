module

import all CFSG.Certificates.Kernel.LocalQTBfsKSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc
public import CFSG.Certificates.Kernel.LocalQTBfsKSound
public import Certificates.Data.Kernel.LocalQT.LatM

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {n : ℕ} {C : List Lvl} {F : ℕ}

theorem letQ_eq (y : ℕ) (k : ℕ → SetM × List ℕ) : letQ y k = k y := by
  cases y <;> rfl

theorem memM_eq (S : SetM) (x : ℕ) : memM n C F S x = S.mask.testBit (idxM n C F x) := by
  unfold memM
  rw [P.letB_eq, P.bit_eq]

theorem addM_eq (S : SetM × List ℕ) (y : ℕ) :
    addM n C F S y = if S.1.mask.testBit (idxM n C F y) = true then S else
      (SetM.mk (S.1.mask ||| 2 ^ idxM n C F y) (S.1.size + 1) (y :: S.1.elems)
        (CFSG.KC.Ord.andB S.1.ok (Nat.blt (idxM n C F y) F)), y :: S.2) := by
  unfold addM
  rw [letQ_eq, P.bit_eq]
  cases h : S.1.mask.testBit (idxM n C F y)
  · rw [P.lor_eq]
    rfl
  · rfl

theorem ok_addM {S : SetM × List ℕ} {y : ℕ} (h : (addM n C F S y).1.ok = true) :
    S.1.ok = true := by
  rw [addM_eq] at h
  split_ifs at h
  · exact h
  · exact (P.andB_iff.1 h).1

@[expose] noncomputable def innerM (n : ℕ) (C : List Lvl) (F : ℕ) (G : List ℕ) (x : ℕ)
    (st : SetM × List ℕ) : SetM × List ℕ :=
  List.rec (motive := fun _ => SetM × List ℕ → SetM × List ℕ) (fun st => st)
    (fun g _ ih2 st => ih2 (addM n C F st (P.mul n x g))) G st

@[expose] noncomputable def outerM (n : ℕ) (C : List Lvl) (F : ℕ) (G Fr : List ℕ) (st : SetM × List ℕ) :
    SetM × List ℕ :=
  List.rec (motive := fun _ => SetM × List ℕ → SetM × List ℕ) (fun st => st)
    (fun x _ ih st => ih (innerM n C F G x st)) Fr st

theorem innerM_eq (G : List ℕ) (x : ℕ) :
    ∀ st, innerM n C F G x st = G.foldl (fun st g => addM n C F st (P.mul n x g)) st := by
  induction G with
  | nil => intro st; rfl
  | cons g G ih =>
    intro st
    change innerM n C F G x (addM n C F st (P.mul n x g)) = _
    rw [ih, List.foldl_cons]

theorem outerM_eq (G Fr : List ℕ) : ∀ st, outerM n C F G Fr st =
    Fr.foldl (fun st x => G.foldl (fun st g => addM n C F st (P.mul n x g)) st) st := by
  induction Fr with
  | nil => intro st; rfl
  | cons x Fr ih =>
    intro st
    change outerM n C F G Fr (innerM n C F G x st) = _
    rw [ih, List.foldl_cons, innerM_eq]

theorem roundM_eq (G : List ℕ) (S : SetM) (Fr : List ℕ) : roundM n C F G S Fr =
    Fr.foldl (fun st x => G.foldl (fun st g => addM n C F st (P.mul n x g)) st) (S, []) :=
  outerM_eq G Fr (S, [])

theorem ok_inner (x : ℕ) : ∀ (G : List ℕ) (st : SetM × List ℕ),
    (G.foldl (fun st g => addM n C F st (P.mul n x g)) st).1.ok = true → st.1.ok = true
  | [], _, h => h
  | g :: G, st, h => by
    rw [List.foldl_cons] at h
    exact ok_addM (ok_inner x G _ h)

theorem ok_outer (G : List ℕ) : ∀ (Fr : List ℕ) (st : SetM × List ℕ),
    (Fr.foldl (fun st x => G.foldl (fun st g => addM n C F st (P.mul n x g)) st) st).1.ok =
      true → st.1.ok = true
  | [], _, h => h
  | x :: Fr, st, h => by
    rw [List.foldl_cons] at h
    exact ok_inner x G _ (ok_outer G Fr _ h)

@[expose] noncomputable def stM (n : ℕ) (C : List Lvl) (F : ℕ) (G : List ℕ) (d : ℕ) : SetM × List ℕ :=
  Nat.rec (motive := fun _ => SetM × List ℕ)
    (addM n C F (Prod.mk (SetM.mk 0 0 [] true) []) (P.one n))
    (fun _ st => roundM n C F G st.1 st.2) d

theorem bfsM_eq (G : List ℕ) (d : ℕ) : bfsM n C F G d = (stM n C F G d).1 := rfl

section Corr

variable {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R] (φ : R → ℕ)

abbrev IdxInj (n : ℕ) (C : List Lvl) (F : ℕ) : Prop :=
  ∀ a b : R, idxM n C F (φ a) < F → idxM n C F (φ a) = idxM n C F (φ b) → a = b

abbrev RepM (n : ℕ) (C : List Lvl) (F : ℕ) (S : SetM) (H : Std.HashSet R) : Prop :=
  ∃ E : List R, E.Nodup ∧ (∀ r, r ∈ H ↔ r ∈ E) ∧ S.elems = E.map φ ∧ S.size = E.length ∧
    (∀ i, S.mask.testBit i = true ↔ ∃ r ∈ E, idxM n C F (φ r) = i) ∧
    ∀ r ∈ E, idxM n C F (φ r) < F

abbrev CorM (n : ℕ) (C : List Lvl) (F : ℕ) (A : Std.HashSet R × List R) (B : SetM × List ℕ) :
    Prop :=
  B.1.ok = true → RepM φ n C F B.1 A.1 ∧ B.2 = A.2.map φ

variable {φ}

omit [Mul R] [One R] in
theorem corM_step (hinj : IdxInj φ n C F) {A : Std.HashSet R × List R} {B : SetM × List ℕ}
    (h : CorM φ n C F A B) (y : R) : CorM φ n C F (hstep A y) (addM n C F B (φ y)) := by
  intro hok
  rw [addM_eq] at hok ⊢
  by_cases hb : B.1.mask.testBit (idxM n C F (φ y)) = true
  · simp only [hb, ↓reduceIte] at hok ⊢
    obtain ⟨⟨E, hnd, hmem, hel, hsz, hbit, hlt⟩, hf⟩ := h hok
    obtain ⟨r, hr, e⟩ := (hbit _).1 hb
    have hry : r = y := hinj r y (hlt r hr) e
    subst hry
    have hc : A.1.contains r = true := Std.HashSet.contains_iff_mem.2 ((hmem r).2 hr)
    have e1 : hstep A r = A := by
      unfold hstep
      simp only [hc, ↓reduceIte]
    rw [e1]
    exact ⟨⟨E, hnd, hmem, hel, hsz, hbit, hlt⟩, hf⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    change CFSG.KC.Ord.andB B.1.ok (Nat.blt (idxM n C F (φ y)) F) = true at hok
    rw [P.andB_iff, P.blt_iff] at hok
    obtain ⟨⟨E, hnd, hmem, hel, hsz, hbit, hlt⟩, hf⟩ := h hok.1
    have hy : y ∉ A.1 := fun hy => hb ((hbit _).2 ⟨y, (hmem y).1 hy, rfl⟩)
    have hc : ¬ A.1.contains y = true := fun hc => hy (Std.HashSet.contains_iff_mem.1 hc)
    have e1 : hstep A y = (A.1.insert y, y :: A.2) := by
      unfold hstep
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [e1]
    refine ⟨⟨y :: E, List.nodup_cons.2 ⟨fun e => hy ((hmem y).2 e), hnd⟩, fun r => ?_, ?_, ?_,
      fun i => ?_, fun r hr => ?_⟩, ?_⟩
    · change r ∈ A.1.insert y ↔ r ∈ y :: E
      rw [Std.HashSet.mem_insert, beq_iff_eq, hmem, List.mem_cons, eq_comm]
    · change φ y :: B.1.elems = (y :: E).map φ
      rw [hel, List.map_cons]
    · change B.1.size + 1 = (y :: E).length
      rw [hsz, List.length_cons]
    · change (B.1.mask ||| 2 ^ idxM n C F (φ y)).testBit i = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, hbit, Nat.testBit_two_pow, decide_eq_true_iff]
      simp only [List.mem_cons, exists_eq_or_imp]
      exact or_comm
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hok.2
      · exact hlt r hr
    · change φ y :: B.2 = (y :: A.2).map φ
      rw [hf, List.map_cons]

omit [One R] in
theorem corM_inner (hinj : IdxInj φ n C F) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    (x : R) : ∀ (gs : List R) (A : Std.HashSet R × List R) (B : SetM × List ℕ),
      CorM φ n C F A B → CorM φ n C F (gs.foldl (fun acc g => hstep acc (x * g)) A)
        ((gs.map φ).foldl (fun st g => addM n C F st (P.mul n (φ x) g)) B) := by
  intro gs
  induction gs with
  | nil => intro A B h; exact h
  | cons g gs ih =>
    intro A B h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have := corM_step hinj h (x * g)
    rw [hmf] at this
    exact ih _ _ this

omit [One R] in
theorem corM_outer (hinj : IdxInj φ n C F) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    (gens : List R) : ∀ (Fr : List R) (A : Std.HashSet R × List R) (B : SetM × List ℕ),
      CorM φ n C F A B →
      CorM φ n C F (Fr.foldl (fun acc x => gens.foldl (fun acc g => hstep acc (x * g)) acc) A)
        ((Fr.map φ).foldl (fun st x => (gens.map φ).foldl
          (fun st g => addM n C F st (P.mul n x g)) st) B) := by
  intro Fr
  induction Fr with
  | nil => intro A B h; exact h
  | cons x Fr ih =>
    intro A B h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    exact ih _ _ (corM_inner hinj hmf x gens A B h)

theorem corM_bfs (hinj : IdxInj φ n C F) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    (h1 : φ 1 = P.one n) (gens : List R) : ∀ d,
    CorM φ n C F (bfsRun gens d ((∅ : Std.HashSet R).insert 1, [1])) (stM n C F (gens.map φ) d) := by
  intro d
  induction d with
  | zero =>
    have h0 : CorM φ n C F ((∅ : Std.HashSet R), []) (SetM.mk 0 0 [] true, []) := fun _ =>
      ⟨⟨[], List.nodup_nil, fun r => by simp, rfl, rfl, fun i => by simp, fun r hr => by simp at hr⟩,
        rfl⟩
    have := corM_step hinj h0 1
    rw [h1] at this
    have e : hstep ((∅ : Std.HashSet R), ([] : List R)) 1 =
        ((∅ : Std.HashSet R).insert 1, [1]) := by
      unfold hstep
      simp
    rw [e] at this
    exact this
  | succ d ih =>
    rw [bfsRun_succ, bfsStep_eq]
    change CorM φ n C F _ (roundM n C F (gens.map φ) (stM n C F (gens.map φ) d).1
      (stM n C F (gens.map φ) d).2)
    intro hok
    rw [roundM_eq] at hok ⊢
    have hok0 := ok_outer _ _ _ hok
    obtain ⟨hr, hf⟩ := ih hok0
    rw [hf] at hok ⊢
    exact corM_outer hinj hmf gens _ _ _ (fun _ => ⟨hr, rfl⟩) hok

theorem rep_bfsM (hinj : IdxInj φ n C F) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    (h1 : φ 1 = P.one n) (gens : List R) (d : ℕ) (hok : (bfsM n C F (gens.map φ) d).ok = true) :
    RepM φ n C F (bfsM n C F (gens.map φ) d) (bfsSet gens d) :=
  (corM_bfs hinj hmf h1 gens d hok).1

omit [Mul R] [One R] in
theorem repM_mem (hinj : IdxInj φ n C F) {S : SetM} {H : Std.HashSet R} (h : RepM φ n C F S H)
    (y : R) : memM n C F S (φ y) = true ↔ y ∈ H := by
  obtain ⟨E, -, hmem, -, -, hbit, hlt⟩ := h
  rw [memM_eq, hbit, hmem]
  constructor
  · rintro ⟨r, hr, e⟩
    rwa [hinj r y (hlt r hr) e] at hr
  · exact fun hy => ⟨y, hy, rfl⟩

omit [Mul R] [One R] in
theorem repM_bit {S : SetM} {H : Std.HashSet R} (h : RepM φ n C F S H) (x : ℕ) :
    memM n C F S x = true ↔ ∃ r ∈ H, idxM n C F (φ r) = idxM n C F x := by
  obtain ⟨E, -, hmem, -, -, hbit, -⟩ := h
  rw [memM_eq, hbit]
  simp only [hmem]

omit [Mul R] [One R] in
theorem repM_size {S : SetM} {H : Std.HashSet R} (h : RepM φ n C F S H) : S.size = H.size := by
  obtain ⟨E, hnd, hmem, -, hsz, -, -⟩ := h
  rw [hsz, ← Std.HashSet.length_toList]
  exact ((List.perm_ext_iff_of_nodup hnd (toList_nodup H)).2 fun r => by
    rw [← hmem, Std.HashSet.mem_toList]).length_eq

omit [Mul R] [One R] in
theorem repM_allL {S : SetM} {H : Std.HashSet R} (h : RepM φ n C F S H) (f : ℕ → Bool) :
    P.allL S.elems f = true ↔ ∀ r ∈ H, f (φ r) = true := by
  obtain ⟨E, -, hmem, hel, -, -, -⟩ := h
  rw [P.allL_iff, hel]
  simp only [List.mem_map, hmem]
  constructor
  · exact fun h r hr => h _ ⟨r, hr, rfl⟩
  · rintro h _ ⟨r, hr, rfl⟩
    exact h r hr

omit [Mul R] [One R] in
theorem repM_anyL {S : SetM} {H : Std.HashSet R} (h : RepM φ n C F S H) (f : ℕ → Bool) :
    P.anyL S.elems f = true ↔ ∃ r ∈ H, f (φ r) = true := by
  obtain ⟨E, -, hmem, hel, -, -, -⟩ := h
  rw [P.anyL_iff, hel]
  simp only [List.mem_map, hmem]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
    exact ⟨r, hr, h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨_, ⟨r, hr, rfl⟩, h⟩

theorem closedM_iff (hinj : IdxInj φ n C F) (hmf : ∀ a b : R, φ (a * b) = P.mul n (φ a) (φ b))
    (h1 : φ 1 = P.one n) (gens : List R) {S : SetM} {H : Std.HashSet R} (h : RepM φ n C F S H)
    (hok : S.ok = true) : closedM n C F (gens.map φ) S = true ↔ closedH gens H = true := by
  unfold closedM closedH
  rw [P.andB_iff, P.andB_iff, Bool.and_eq_true, ← h1, repM_mem hinj h, Std.HashSet.contains_iff_mem,
    repM_allL h, toList_all_iff]
  simp only [hok, true_and]
  refine and_congr Iff.rfl (forall₂_congr fun r _ => ?_)
  simp only [P.allL_iff, List.all_eq_true, List.forall_mem_map, ← hmf, repM_mem hinj h,
    Std.HashSet.contains_iff_mem]

omit [Mul R] [One R] in
theorem repM_mask_eq (hinj : IdxInj φ n C F) {S T : SetM} {H K : Std.HashSet R}
    (hS : RepM φ n C F S H) (hT : RepM φ n C F T K) (e : S.mask = T.mask) (r : R) :
    r ∈ H ↔ r ∈ K := by
  rw [← repM_mem hinj hS, ← repM_mem hinj hT, memM_eq, memM_eq, e]

end Corr

end CFSG.KC.LQT.CM

end
