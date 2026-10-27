module

public import Certificates.Data.Kernel.LocalQT.Lat
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem brec_t {α : Sort _} (f t : α) : Bool.rec (motive := fun _ => α) f t true = t := rfl

theorem brec_f {α : Sort _} (f t : α) : Bool.rec (motive := fun _ => α) f t false = f := rfl

def ltR (x y : ℕ) : Prop := hashK x < hashK y ∨ (hashK x = hashK y ∧ x < y)

theorem ltK_iff (x y : ℕ) : ltK x y = true ↔ ltR x y := by
  unfold ltK
  rw [P.letB_eq, P.letB_eq, P.orB_iff, P.andB_iff, P.blt_iff, P.beq_iff, P.blt_iff]
  rfl

theorem ltR_asymm {x y : ℕ} (h : ltR x y) : ¬ ltR y x := by
  unfold ltR at *
  omega

theorem ltR_total {x y : ℕ} (h : x ≠ y) (h' : ¬ ltR x y) : ltR y x := by
  unfold ltR at *
  omega

@[expose] def memN : NT → ℕ → Prop
  | .lf, _ => False
  | .nd l k r, x => memN l x ∨ x = k ∨ memN r x

@[expose] def OrdN : NT → Prop
  | .lf => True
  | .nd l k r => OrdN l ∧ OrdN r ∧ (∀ y, memN l y → ltR y k) ∧ (∀ y, memN r y → ltR k y)

noncomputable def memTG (lt : ℕ → ℕ → Bool) (t : NT) (x : ℕ) : Bool :=
  NT.rec (motive := fun _ => Bool) false
    (fun _ k _ ihl ihr => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) ihr ihl (lt x k)) true (Nat.beq x k)) t

noncomputable def insTG (lt : ℕ → ℕ → Bool) (t : NT) (x : ℕ) : NT :=
  NT.rec (motive := fun _ => NT) (NT.nd NT.lf x NT.lf)
    (fun l k r ihl ihr => Bool.rec (motive := fun _ => NT)
      (Bool.rec (motive := fun _ => NT) (NT.nd l k ihr) (NT.nd ihl k r) (lt x k))
      (NT.nd l k r) (Nat.beq x k)) t

theorem memT_eq (t : NT) (x : ℕ) : memT t x = memTG ltK t x := by
  delta memT memTG
  rfl

theorem insT_eq (t : NT) (x : ℕ) : insT t x = insTG ltK t x := by
  delta insT insTG
  rfl

theorem beq_false {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false :=
  Bool.eq_false_iff.2 fun e => h (P.beq_iff.1 e)

section Gen

variable {lt : ℕ → ℕ → Bool} (hlt : ∀ x y, lt x y = true ↔ ltR x y)
include hlt

theorem lt_false {x y : ℕ} (h : ¬ ltR x y) : lt x y = false :=
  Bool.eq_false_iff.2 fun e => h ((hlt x y).1 e)

theorem memTG_iff : ∀ {t : NT}, OrdN t → ∀ x, (memTG lt t x = true ↔ memN t x)
  | .lf, _, x => by simp [memTG, memN]
  | .nd l k r, ho, x => by
    obtain ⟨ol, orr, bl, br⟩ := ho
    change Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (memTG lt r x) (memTG lt l x) (lt x k)) true
      (Nat.beq x k) = true ↔ _
    by_cases hxk : x = k
    · rw [P.beq_iff.2 hxk]
      dsimp only
      simp [memN, hxk]
    · rw [beq_false hxk]
      dsimp only
      by_cases hl : ltR x k
      · rw [(hlt x k).2 hl]
        dsimp only
        rw [memTG_iff ol x]
        simp only [memN]
        constructor
        · exact fun h => Or.inl h
        · rintro (h | h | h)
          · exact h
          · exact absurd h hxk
          · exact absurd (br x h) (ltR_asymm hl)
      · rw [lt_false hlt hl]
        dsimp only
        rw [memTG_iff orr x]
        simp only [memN]
        constructor
        · exact fun h => Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact absurd (bl x h) hl
          · exact absurd h hxk
          · exact h

theorem mem_insTG (x y : ℕ) : ∀ t : NT, memN (insTG lt t x) y ↔ y = x ∨ memN t y
  | .lf => by
    change memN (NT.nd NT.lf x NT.lf) y ↔ _
    simp [memN]
  | .nd l k r => by
    change memN (Bool.rec (motive := fun _ => NT)
      (Bool.rec (motive := fun _ => NT) (NT.nd l k (insTG lt r x)) (NT.nd (insTG lt l x) k r) (lt x k))
      (NT.nd l k r) (Nat.beq x k)) y ↔ _
    by_cases hxk : x = k
    · rw [P.beq_iff.2 hxk]
      dsimp only
      simp only [memN]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact Or.inr (Or.inl hxk)
        · exact h
    · rw [beq_false hxk]
      dsimp only
      by_cases hl : ltR x k
      · rw [(hlt x k).2 hl]
        dsimp only
        simp only [memN, mem_insTG x y l]
        tauto
      · rw [lt_false hlt hl]
        dsimp only
        simp only [memN, mem_insTG x y r]
        tauto

theorem ord_insTG (x : ℕ) : ∀ {t : NT}, OrdN t → OrdN (insTG lt t x)
  | .lf, _ => by
    change OrdN (NT.nd NT.lf x NT.lf)
    simp [OrdN, memN]
  | .nd l k r, ho => by
    obtain ⟨ol, orr, bl, br⟩ := ho
    change OrdN (Bool.rec (motive := fun _ => NT)
      (Bool.rec (motive := fun _ => NT) (NT.nd l k (insTG lt r x)) (NT.nd (insTG lt l x) k r) (lt x k))
      (NT.nd l k r) (Nat.beq x k))
    by_cases hxk : x = k
    · rw [P.beq_iff.2 hxk]
      dsimp only
      exact ⟨ol, orr, bl, br⟩
    · rw [beq_false hxk]
      dsimp only
      by_cases hl : ltR x k
      · rw [(hlt x k).2 hl]
        dsimp only
        refine ⟨ord_insTG x ol, orr, fun y hy => ?_, br⟩
        rcases (mem_insTG hlt x y l).1 hy with rfl | hy
        · exact hl
        · exact bl y hy
      · rw [lt_false hlt hl]
        dsimp only
        refine ⟨ol, ord_insTG x orr, bl, fun y hy => ?_⟩
        rcases (mem_insTG hlt x y r).1 hy with rfl | hy
        · exact ltR_total hxk hl
        · exact br y hy

end Gen

theorem memT_iff {t : NT} (ho : OrdN t) (x : ℕ) : memT t x = true ↔ memN t x := by
  rw [memT_eq]
  exact memTG_iff ltK_iff ho x

theorem mem_insT (x y : ℕ) (t : NT) : memN (insT t x) y ↔ y = x ∨ memN t y := by
  rw [insT_eq]
  exact mem_insTG ltK_iff x y t

theorem ord_insT (x : ℕ) {t : NT} (ho : OrdN t) : OrdN (insT t x) := by
  rw [insT_eq]
  exact ord_insTG ltK_iff x ho

noncomputable def innerK (mf : ℕ → ℕ → ℕ) (G : List ℕ) (x : ℕ) (st : SetK × List ℕ) :
    SetK × List ℕ :=
  List.rec (motive := fun _ => SetK × List ℕ → SetK × List ℕ) (fun st => st)
    (fun g _ ih2 st => ih2 (addK st (mf x g))) G st

noncomputable def outerK (mf : ℕ → ℕ → ℕ) (G F : List ℕ) (st : SetK × List ℕ) : SetK × List ℕ :=
  List.rec (motive := fun _ => SetK × List ℕ → SetK × List ℕ) (fun st => st)
    (fun x _ ih st => ih (innerK mf G x st)) F st

theorem innerK_eq (mf : ℕ → ℕ → ℕ) (G : List ℕ) (x : ℕ) :
    ∀ st, innerK mf G x st = G.foldl (fun st g => addK st (mf x g)) st := by
  induction G with
  | nil => intro st; rfl
  | cons g G ih =>
    intro st
    change innerK mf G x (addK st (mf x g)) = _
    rw [ih, List.foldl_cons]

theorem outerK_eq (mf : ℕ → ℕ → ℕ) (G F : List ℕ) :
    ∀ st, outerK mf G F st = F.foldl (fun st x => G.foldl (fun st g => addK st (mf x g)) st) st := by
  induction F with
  | nil => intro st; rfl
  | cons x F ih =>
    intro st
    change outerK mf G F (innerK mf G x st) = _
    rw [ih, List.foldl_cons, innerK_eq]

theorem roundG_eq (mf : ℕ → ℕ → ℕ) (G : List ℕ) (S : SetK) (F : List ℕ) :
    roundG mf G S F = F.foldl (fun st x => G.foldl (fun st g => addK st (mf x g)) st) (S, []) :=
  outerK_eq mf G F (S, [])

noncomputable def stG (mf : ℕ → ℕ → ℕ) (o : ℕ) (G : List ℕ) (d : ℕ) : SetK × List ℕ :=
  Nat.rec (motive := fun _ => SetK × List ℕ) (Prod.mk (SetK.mk (NT.nd NT.lf o NT.lf) 1 [o]) [o])
    (fun _ st => roundG mf G st.1 st.2) d

theorem addK_of_mem {S : SetK × List ℕ} {y : ℕ} (h : memT S.1.t y = true) : addK S y = S := by
  unfold addK
  rw [h]

theorem addK_of_not_mem {S : SetK × List ℕ} {y : ℕ} (h : memT S.1.t y = false) :
    addK S y = (SetK.mk (insT S.1.t y) (Nat.succ S.1.size) (y :: S.1.elems), y :: S.2) := by
  unfold addK
  rw [h]

section Corr

variable {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R] (φ : R → ℕ)

abbrev Rep (K : SetK) (H : Std.HashSet R) : Prop :=
  OrdN K.t ∧ (∀ x, memN K.t x ↔ x ∈ K.elems) ∧
    ∃ E : List R, E.Nodup ∧ (∀ r, r ∈ H ↔ r ∈ E) ∧ K.elems = E.map φ ∧ K.size = E.length

abbrev Cor (A : Std.HashSet R × List R) (B : SetK × List ℕ) : Prop :=
  Rep φ B.1 A.1 ∧ B.2 = A.2.map φ

def hstep (A : Std.HashSet R × List R) (y : R) : Std.HashSet R × List R :=
  if A.1.contains y then A else (A.1.insert y, y :: A.2)

variable {φ}

omit [Mul R] [One R] in
theorem rep_mem_iff (hφ : Function.Injective φ) {K : SetK} {H : Std.HashSet R} (h : Rep φ K H)
    (y : R) : memT K.t (φ y) = true ↔ y ∈ H := by
  obtain ⟨ho, hm, E, -, hmem, hel, -⟩ := h
  rw [memT_iff ho, hm, hel, List.mem_map, hmem]
  constructor
  · rintro ⟨r, hr, e⟩
    rwa [hφ e] at hr
  · exact fun hy => ⟨y, hy, rfl⟩

omit [Mul R] [One R] in
theorem cor_step (hφ : Function.Injective φ) {A : Std.HashSet R × List R} {B : SetK × List ℕ}
    (h : Cor φ A B) (y : R) : Cor φ (hstep A y) (addK B (φ y)) := by
  have key := rep_mem_iff hφ h.1 y
  by_cases hy : y ∈ A.1
  · have e1 : hstep A y = A := by
      unfold hstep
      split
      · rfl
      · exact absurd (Std.HashSet.contains_iff_mem.2 hy) ‹_›
    rw [e1, addK_of_mem (key.2 hy)]
    exact h
  · have e1 : hstep A y = (A.1.insert y, y :: A.2) := by
      unfold hstep
      split
      · rename_i hc
        exact absurd (Std.HashSet.contains_iff_mem.1 hc) hy
      · rfl
    rw [e1, addK_of_not_mem (Bool.eq_false_iff.2 fun e => hy (key.1 e))]
    obtain ⟨⟨ho, hm, E, hnd, hmem, hel, hsz⟩, hf⟩ := h
    refine ⟨⟨ord_insT _ ho, fun x => ?_, y :: E, List.nodup_cons.2 ⟨fun e => hy ((hmem y).2 e), hnd⟩,
      fun r => ?_, ?_, ?_⟩, ?_⟩
    · change memN (insT B.1.t (φ y)) x ↔ x ∈ φ y :: B.1.elems
      rw [mem_insT, hm, List.mem_cons]
    · change r ∈ A.1.insert y ↔ r ∈ y :: E
      rw [Std.HashSet.mem_insert, beq_iff_eq, hmem, List.mem_cons, eq_comm]
    · change φ y :: B.1.elems = (y :: E).map φ
      rw [hel, List.map_cons]
    · change Nat.succ B.1.size = (y :: E).length
      rw [hsz, List.length_cons]
    · change φ y :: B.2 = (y :: A.2).map φ
      rw [hf, List.map_cons]

omit [One R] in
theorem cor_inner (hφ : Function.Injective φ) (mf : ℕ → ℕ → ℕ)
    (hmf : ∀ a b : R, φ (a * b) = mf (φ a) (φ b)) (x : R) :
    ∀ (gs : List R) (A : Std.HashSet R × List R) (B : SetK × List ℕ), Cor φ A B →
      Cor φ (gs.foldl (fun acc g => hstep acc (x * g)) A)
        ((gs.map φ).foldl (fun st g => addK st (mf (φ x) g)) B) := by
  intro gs
  induction gs with
  | nil => intro A B h; exact h
  | cons g gs ih =>
    intro A B h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have := cor_step hφ h (x * g)
    rw [hmf] at this
    exact ih _ _ this

omit [One R] in
theorem cor_outer (hφ : Function.Injective φ) (mf : ℕ → ℕ → ℕ)
    (hmf : ∀ a b : R, φ (a * b) = mf (φ a) (φ b)) (gens : List R) :
    ∀ (F : List R) (A : Std.HashSet R × List R) (B : SetK × List ℕ), Cor φ A B →
      Cor φ (F.foldl (fun acc x => gens.foldl (fun acc g => hstep acc (x * g)) acc) A)
        ((F.map φ).foldl (fun st x => (gens.map φ).foldl (fun st g => addK st (mf x g)) st) B) := by
  intro F
  induction F with
  | nil => intro A B h; exact h
  | cons x F ih =>
    intro A B h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    exact ih _ _ (cor_inner hφ mf hmf x gens A B h)

omit [One R] in
theorem bfsStep_eq (gens : List R) (S : Std.HashSet R) (F : List R) :
    bfsStep gens S F = F.foldl (fun acc x => gens.foldl (fun acc g => hstep acc (x * g)) acc)
      (S, []) := by
  unfold bfsStep hstep
  rfl

omit [One R] in
theorem bfsRun_succ (gens : List R) :
    ∀ (n : ℕ) (st : Std.HashSet R × List R),
      bfsRun gens (n + 1) st = bfsStep gens (bfsRun gens n st).1 (bfsRun gens n st).2 := by
  intro n
  induction n with
  | zero => intro st; rfl
  | succ n ih =>
    intro st
    change bfsRun gens (n + 1) (bfsStep gens st.1 st.2) = _
    rw [ih]
    rfl

theorem cor_bfs (hφ : Function.Injective φ) (mf : ℕ → ℕ → ℕ)
    (hmf : ∀ a b : R, φ (a * b) = mf (φ a) (φ b)) (gens : List R) :
    ∀ d, Cor φ (bfsRun gens d ((∅ : Std.HashSet R).insert 1, [1])) (stG mf (φ 1) (gens.map φ) d) := by
  intro d
  induction d with
  | zero =>
    refine ⟨⟨?_, fun x => ?_, [1], List.nodup_singleton _, fun r => ?_, rfl, rfl⟩, rfl⟩
    · change OrdN (NT.nd NT.lf (φ 1) NT.lf)
      simp [OrdN, memN]
    · change memN (NT.nd NT.lf (φ 1) NT.lf) x ↔ x ∈ [φ 1]
      simp [memN]
    · change r ∈ (∅ : Std.HashSet R).insert 1 ↔ r ∈ [1]
      simp only [Std.HashSet.mem_insert, Std.HashSet.not_mem_empty, or_false, beq_iff_eq,
        List.mem_singleton]
      exact eq_comm
  | succ d ih =>
    rw [bfsRun_succ, bfsStep_eq]
    change Cor φ _ (roundG mf (gens.map φ) (stG mf (φ 1) (gens.map φ) d).1
      (stG mf (φ 1) (gens.map φ) d).2)
    rw [roundG_eq, ih.2]
    exact cor_outer hφ mf hmf gens _ _ _ ⟨ih.1, rfl⟩

theorem rep_bfs (hφ : Function.Injective φ) (mf : ℕ → ℕ → ℕ)
    (hmf : ∀ a b : R, φ (a * b) = mf (φ a) (φ b)) (gens : List R) (d : ℕ) :
    Rep φ (bfsG mf (φ 1) (gens.map φ) d) (bfsSet gens d) :=
  (cor_bfs hφ mf hmf gens d).1

omit [Mul R] [One R] in
theorem toList_nodup (H : Std.HashSet R) : H.toList.Nodup :=
  Std.HashSet.distinct_toList.imp fun {a b} h hab => by simp [hab] at h

omit [Mul R] [One R] in
theorem rep_size {K : SetK} {H : Std.HashSet R} (h : Rep φ K H) : K.size = H.size := by
  obtain ⟨-, -, E, hnd, hmem, -, hsz⟩ := h
  rw [hsz, ← Std.HashSet.length_toList]
  exact ((List.perm_ext_iff_of_nodup hnd (toList_nodup H)).2 fun r => by
    rw [← hmem, Std.HashSet.mem_toList]).length_eq

omit [Mul R] [One R] in
theorem rep_memT {K : SetK} {H : Std.HashSet R} (h : Rep φ K H) (x : ℕ) :
    memT K.t x = true ↔ ∃ r ∈ H, φ r = x := by
  obtain ⟨ho, hm, E, -, hmem, hel, -⟩ := h
  rw [memT_iff ho, hm, hel, List.mem_map]
  simp only [hmem]

omit [Mul R] [One R] in
theorem rep_allL {K : SetK} {H : Std.HashSet R} (h : Rep φ K H) (f : ℕ → Bool) :
    P.allL K.elems f = true ↔ ∀ r ∈ H, f (φ r) = true := by
  obtain ⟨-, -, E, -, hmem, hel, -⟩ := h
  rw [P.allL_iff, hel]
  simp only [List.mem_map, hmem]
  constructor
  · exact fun h r hr => h _ ⟨r, hr, rfl⟩
  · rintro h _ ⟨r, hr, rfl⟩
    exact h r hr

omit [Mul R] [One R] in
theorem rep_anyL {K : SetK} {H : Std.HashSet R} (h : Rep φ K H) (f : ℕ → Bool) :
    P.anyL K.elems f = true ↔ ∃ r ∈ H, f (φ r) = true := by
  obtain ⟨-, -, E, -, hmem, hel, -⟩ := h
  rw [P.anyL_iff, hel]
  simp only [List.mem_map, hmem]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
    exact ⟨r, hr, h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨_, ⟨r, hr, rfl⟩, h⟩

omit [Mul R] [One R] in
theorem toList_all_iff (H : Std.HashSet R) (p : R → Bool) :
    H.toList.all p = true ↔ ∀ r ∈ H, p r = true := by
  rw [List.all_eq_true]
  simp only [Std.HashSet.mem_toList]

omit [Mul R] [One R] in
theorem toList_any_iff (H : Std.HashSet R) (p : R → Bool) :
    H.toList.any p = true ↔ ∃ r ∈ H, p r = true := by
  rw [List.any_eq_true]
  simp only [Std.HashSet.mem_toList]

theorem closedG_eq (hφ : Function.Injective φ) (mf : ℕ → ℕ → ℕ)
    (hmf : ∀ a b : R, φ (a * b) = mf (φ a) (φ b)) (gens : List R) {K : SetK} {H : Std.HashSet R}
    (h : Rep φ K H) : closedG mf (φ 1) (gens.map φ) K = closedH gens H := by
  rw [Bool.eq_iff_iff]
  unfold closedG closedH
  rw [P.andB_iff, Bool.and_eq_true, rep_mem_iff hφ h, Std.HashSet.contains_iff_mem, rep_allL h,
    toList_all_iff]
  refine and_congr Iff.rfl (forall₂_congr fun r _ => ?_)
  simp only [P.allL_iff, List.all_eq_true, List.forall_mem_map, ← hmf, rep_mem_iff hφ h,
    Std.HashSet.contains_iff_mem]

end Corr

section RNCode

variable {n : ℕ}

def rdig (r : RN n) (i : ℕ) : ℕ := if h : i < n then ((r.val[(⟨i, h⟩ : Fin n)] : Fin n) : ℕ) else 0

def rnc (r : RN n) : ℕ := P.E (rdig r) n

theorem rdig_of_lt (r : RN n) {i : ℕ} (hi : i < n) :
    rdig r i = ((r.val[(⟨i, hi⟩ : Fin n)] : Fin n) : ℕ) := by
  simp only [rdig, hi, ↓reduceDIte]

theorem rdig_lt (hn : n ≤ 32) (r : RN n) : ∀ i < n, rdig r i < 32 := fun i hi => by
  rw [rdig_of_lt r hi]
  have := (r.val[(⟨i, hi⟩ : Fin n)]).isLt
  omega

theorem img_rnc (hn : n ≤ 32) (r : RN n) (i : Fin n) : P.img (rnc r) i = (r.val[i] : ℕ) := by
  rw [P.img_eq, rnc, P.E_digit (rdig_lt hn r) i.isLt, rdig_of_lt r i.isLt]

theorem rnc_enc (σ : Perm (Fin n)) : rnc (RN.enc σ) = P.code σ := by
  rw [P.code_eq, rnc]
  refine P.E_congr fun i hi => ?_
  rw [rdig_of_lt _ hi, RN.enc_get]
  exact (P.vals_fin σ ⟨i, hi⟩).symm

theorem rnc_mul (hn : n ≤ 32) (x y : RN n) : rnc (x * y) = P.mul n (rnc x) (rnc y) := by
  rw [P.mul, P.ofFn_eq, rnc]
  refine P.E_congr fun i hi => ?_
  rw [rdig_of_lt _ hi, RN.mul_get, img_rnc hn y ⟨i, hi⟩, img_rnc hn x]

theorem rnc_one : rnc (1 : RN n) = P.one n := by
  rw [P.one, P.ofFn_eq, rnc]
  refine P.E_congr fun i hi => ?_
  rw [rdig_of_lt _ hi, RN.one_get]

theorem rnc_inj (hn : n ≤ 32) : Function.Injective (rnc : RN n → ℕ) := by
  intro x y h
  refine RN.ext fun i => Fin.ext ?_
  have := img_rnc hn x i
  rw [h, img_rnc hn y i] at this
  exact this.symm

theorem map_rnc_enc (L : List (Perm (Fin n))) : (L.map RN.enc).map rnc = L.map P.code := by
  rw [List.map_map]
  exact List.map_congr_left fun σ _ => rnc_enc σ

theorem rep_bfsK (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) :
    Rep rnc (bfsK n (L.map P.code) d) (bfsSet (L.map RN.enc) d) := by
  have := rep_bfs (rnc_inj hn) (P.mul n) (rnc_mul hn) (L.map RN.enc) d
  rwa [map_rnc_enc, rnc_one] at this

theorem closedK_eq (hn : n ≤ 32) (L : List (Perm (Fin n))) (d : ℕ) :
    closedK n (L.map P.code) (bfsK n (L.map P.code) d) =
      closedH (L.map RN.enc) (bfsSet (L.map RN.enc) d) := by
  have := closedG_eq (rnc_inj hn) (P.mul n) (rnc_mul hn) (L.map RN.enc) (rep_bfsK hn L d)
  rwa [map_rnc_enc, rnc_one] at this

end RNCode

end CFSG.KC.LQT.L

end
