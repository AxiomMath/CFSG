module

public import Certificates.Data.Kernel.Misc.RuBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBaseInputs
public import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Misc.RuBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.EvenSporadicStandard.TwoRu.HypOne
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def Bij (n : Nat) (f g : Nat → Nat) : Prop :=
  (∀ x < n, f x < n) ∧ (∀ x < n, g x < n) ∧ (∀ x < n, g (f x) = x) ∧ ∀ x < n, f (g x) = x

theorem bij_of {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n) (hg : ∀ x < n, g (f x) = x) :
    Bij n f g := by
  let F : Fin n → Fin n := fun x => ⟨f x, hf x x.2⟩
  have hinj : Function.Injective F := by
    intro a b hab
    have := congrArg (fun y : Fin n => g y.val) hab
    simp only [F, hg a a.2, hg b b.2] at this
    exact Fin.ext this
  have hsurj := Finite.injective_iff_surjective.1 hinj
  have hs : ∀ y < n, ∃ x < n, f x = y := fun y hy => by
    obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
    exact ⟨x.val, x.2, congrArg Fin.val hx⟩
  refine ⟨hf, fun y hy => ?_, hg, fun y hy => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hs y hy
    rw [hg x hx]
    exact hx
  · obtain ⟨x, hx, rfl⟩ := hs y hy
    rw [hg x hx]

@[expose] def TR (n : Nat) (T : Table) (f : Nat → Nat) : Prop :=
  T.size = n ∧ ∀ x < n, ap T x = f x

theorem tr_tblOfArr {n : Nat} {a : Array Nat} (ha : a.size = n) (hb : ∀ x < n, a[x]! < 2 ^ 32) :
    TR n (tblOfArr a) (fun x => a[x]!) := by
  refine ⟨by simp [tblOfArr, ha], fun x hx => ?_⟩
  have hx' : x < a.size := by omega
  have hbx : a[x] < UInt32.size := by
    have := hb x hx
    rw [getElem!_pos a x hx'] at this
    exact this
  unfold ap tblOfArr
  rw [getElem!_pos (a.map UInt32.ofNat) x (by simpa using hx'), Array.getElem_map,
    UInt32.toNat_ofNat_of_lt' hbx]
  exact (getElem!_pos a x hx').symm

theorem tr_idT {n : Nat} (hn : n < 2 ^ 32) : TR n (idT n) (fun x => x) := by
  refine ⟨by simp [idT], fun x hx => ?_⟩
  unfold ap idT
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn,
    UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hx hn)]

theorem tr_map {n : Nat} {T L : Table} {f g : Nat → Nat} (hT : TR n T f) (hf : ∀ x < n, f x < n)
    (hL : TR n L g) : TR n (T.map fun t => L[t.toNat]!) (fun x => g (f x)) := by
  refine ⟨by simp [hT.1], fun x hx => ?_⟩
  have hx' : x < T.size := by rw [hT.1]; exact hx
  unfold ap
  rw [getElem!_pos _ x (by simpa using hx'), Array.getElem_map]
  have h1 := hT.2 x hx
  unfold ap at h1
  rw [getElem!_pos T x hx'] at h1
  rw [h1]
  exact hL.2 _ (hf x hx)

theorem tr_unique {n : Nat} {T : Table} {f g : Nat → Nat} (hf : TR n T f) (hg : TR n T g) :
    ∀ x < n, f x = g x := fun x hx => by rw [← hf.2 x hx, hg.2 x hx]

theorem invT_eq_foldl (n : Nat) (P : Table) :
    invT n P = (List.range' 0 n).foldl
      (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0) := by
  unfold invT
  simp [Id.run]
  rfl

theorem invT_foldl_spec {n : Nat} (P : Table) (hlt : ∀ i < n, (P[i]!).toNat < n)
    (hinj : ∀ i < n, ∀ i' < n, (P[i]!).toNat = (P[i']!).toNat → i = i') :
    ∀ m ≤ n, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0)).size = n ∧
      ∀ i < m, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i))
          (Array.replicate n 0))[(P[i]!).toNat]! = UInt32.ofNat i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨hs, hi⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add, Nat.one_mul]
    generalize hr : (List.range' 0 m).foldl
      (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0) = r
      at hs hi
    refine ⟨by rw [Array.size_setIfInBounds, hs], fun i hi' => ?_⟩
    have hmn : m < n := by omega
    have hPm := hlt m hmn
    have hbound : (P[m]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
      rw [Array.size_setIfInBounds, hs]; exact hPm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt' | heq
    · have hne : (P[m]!).toNat ≠ (P[i]!).toNat := fun h' => by
        have := hinj m hmn i (by omega) h'
        omega
      have hbi : (P[i]!).toNat < r.size := by rw [hs]; exact hlt i (by omega)
      have hbi' : (P[i]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
        rw [Array.size_setIfInBounds]; exact hbi
      rw [getElem!_pos (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)) (P[i]!).toNat hbi',
        Array.getElem_setIfInBounds_ne hbi hne, ← getElem!_pos r (P[i]!).toNat hbi]
      exact hi i hlt'
    · subst heq
      rw [getElem!_pos (r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (P[i]!).toNat hbound,
        Array.getElem_setIfInBounds_self]

theorem tr_invT {n : Nat} (hn : n < 2 ^ 32) {T : Table} {f g : Nat → Nat} (hT : TR n T f)
    (hb : Bij n f g) : TR n (invT n T) g := by
  have hap : ∀ i < n, (T[i]!).toNat = f i := fun i hi => hT.2 i hi
  have hlt : ∀ i < n, (T[i]!).toNat < n := fun i hi => by rw [hap i hi]; exact hb.1 i hi
  have hinj : ∀ i < n, ∀ i' < n, (T[i]!).toNat = (T[i']!).toNat → i = i' := by
    intro i hi i' hi' h
    rw [hap i hi, hap i' hi'] at h
    rw [← hb.2.2.1 i hi, ← hb.2.2.1 i' hi', h]
  have hs := invT_foldl_spec T hlt hinj n le_rfl
  rw [← invT_eq_foldl] at hs
  refine ⟨hs.1, fun y hy => ?_⟩
  have hgy := hb.2.1 y hy
  have h := hs.2 (g y) hgy
  rw [hap _ hgy, hb.2.2.2 y hy] at h
  unfold ap
  rw [h, UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hgy hn)]

theorem allIn_iff {n : Nat} {p : Nat → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    have := h ⟨i, by omega⟩ (List.mem_finRange _)
    simpa using this
  · intro h k _
    simpa using h k.val (by have := k.isLt; omega)

theorem invOK_of {n : Nat} {T R : Table} {f g : Nat → Nat} (hT : TR n T f) (hR : TR n R g)
    (hb : Bij n f g) : invOK n T R = true := by
  unfold invOK
  rw [allIn_iff]
  intro i hi
  rw [hT.2 i hi, hR.2 _ (hb.1 i hi), hb.2.2.1 i hi, beq_self_eq_true]

@[expose] def wordF (F : Int → Nat → Nat) (w : List Int) : Nat → Nat :=
  w.foldr (fun l f x => F l (f x)) (fun x => x)

theorem tr_wordT {n : Nat} (hn : n < 2 ^ 32) {gens : Int → Table} {F : Int → Nat → Nat}
    (w : List Int) (hg : ∀ l ∈ w, TR n (gens l) (F l) ∧ ∀ x < n, F l x < n) :
    TR n (wordT n gens w) (wordF F w) ∧ ∀ x < n, wordF F w x < n := by
  induction w with
  | nil => exact ⟨tr_idT hn, fun x hx => hx⟩
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l' hl' => hg l' (List.mem_cons_of_mem _ hl')
    obtain ⟨hl1, hl2⟩ := hg l List.mem_cons_self
    refine ⟨?_, fun x hx => hl2 _ (ih2 x hx)⟩
    change TR n ((wordT n gens w).map fun t => (gens l)[t.toNat]!) (fun x => F l (wordF F w x))
    exact tr_map ih1 ih2 hl1

theorem apP_mulP {p q i : Nat} (hi : i < 4060) : apP (mulP p q) i = apP p (apP q i) :=
  CFSG.KS.PackFld.pg_pcomp (w := 12) (by decide) hi

theorem apP_idP {i : Nat} (hi : i < 4060) : apP idP i = i :=
  CFSG.KS.PF.pg_pidn (n := 4060) (w := 12) (by decide) (by decide) hi

@[expose] noncomputable def letP (G GI : Nat → Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => G (Nat.sub k 1)) (fun k => GI k) l

theorem wordP_cons (G GI : Nat → Nat) (l : Int) (w : List Int) :
    wordP G GI (l :: w) = mulP (letP G GI l) (wordP G GI w) := by
  change strictN (wordP G GI w) _ = _
  rw [CFSG.KS.PackFld.strictN_eqP]
  rfl

theorem apP_wordP {G GI : Nat → Nat} (w : List Int)
    (hl : ∀ l ∈ w, ∀ x < 4060, apP (letP G GI l) x < 4060) :
    ∀ x < 4060, apP (wordP G GI w) x = wordF (fun l => apP (letP G GI l)) w x := by
  induction w with
  | nil => intro x hx; exact apP_idP hx
  | cons l w ih =>
    intro x hx
    rw [wordP_cons, apP_mulP hx, ih (fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')) x hx]
    rfl

theorem apP_wordP_lt {G GI : Nat → Nat} (w : List Int)
    (hl : ∀ l ∈ w, ∀ x < 4060, apP (letP G GI l) x < 4060) :
    ∀ x < 4060, apP (wordP G GI w) x < 4060 := by
  induction w with
  | nil =>
    intro x hx
    change apP idP x < 4060
    rw [apP_idP hx]
    exact hx
  | cons l w ih =>
    intro x hx
    rw [wordP_cons, apP_mulP hx]
    exact hl l List.mem_cons_self _ (ih (fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')) x hx)

theorem lettersOK_spec {k : Nat} {w : List Int} (h : lettersOK k w = true) :
    ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ k := by
  intro z hz
  simp only [lettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  exact h z hz

theorem tr_word {A AI : Array Table} {P PI : Nat → Nat}
    (hA : ∀ k < A.size, TR 4060 A[k]! (apP (P k)) ∧ TR 4060 AI[k]! (apP (PI k)) ∧
      Bij 4060 (apP (P k)) (apP (PI k)))
    (w : List Int) (hw : lettersOK A.size w = true) :
    TR 4060 (wordT 4060 (letterTab A AI) w) (apP (wordP P PI w)) ∧
      ∀ x < 4060, apP (wordP P PI w) x < 4060 := by
  have hl := lettersOK_spec hw
  have hlet : ∀ l ∈ w, TR 4060 (letterTab A AI l) (apP (letP P PI l)) ∧
      ∀ x < 4060, apP (letP P PI l) x < 4060 := by
    intro l hlw
    obtain ⟨hl0, hlk⟩ := hl l hlw
    rcases l with k | k
    · have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact absurd rfl hl0
        · exact hk
      have hk' : k - 1 < A.size := by simp at hlk; omega
      have e : letterTab A AI (Int.ofNat k) = A[k - 1]! := by
        simp [letterTab, hk]
      rw [e]
      exact ⟨(hA _ hk').1, (hA _ hk').2.2.1⟩
    · have hk' : k < A.size := by simp at hlk; omega
      have hneg : ¬ (0 : Int) < Int.negSucc k := Int.not_lt.2 (Int.le_of_lt (Int.negSucc_lt_zero k))
      have e : letterTab A AI (Int.negSucc k) = AI[k]! := by
        unfold letterTab
        rw [ite_eq_right hneg]
        rfl
      rw [e]
      exact ⟨(hA _ hk').2.1, (hA _ hk').2.2.2.1⟩
  have hr := tr_wordT (by decide) w hlet
  refine ⟨⟨hr.1.1, fun x hx => ?_⟩, apP_wordP_lt w (fun l hl' => (hlet l hl').2)⟩
  rw [hr.1.2 x hx, apP_wordP w (fun l hl' => (hlet l hl').2) x hx]

set_option exponentiation.threshold 50000 in
theorem fld_packL : ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ 48720) →
    CFSG.KS.PackFld.Fld 48720 (packL L) (fun j => L.getD j 0)
  | [], _ => CFSG.KS.PackFld.fld_congr (CFSG.KS.PackFld.fld_zero 48720) (fun j => by simp)
  | x :: L, h => by
    have h1 := CFSG.KS.PackFld.fld_one (w := 48720) (v := x) (h x List.mem_cons_self)
    have h2 := CFSG.KS.PackFld.fld_shl 1 (fld_packL L fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [Nat.mul_one] at h2
    refine CFSG.KS.PackFld.fld_congr (CFSG.KS.PackFld.fld_or h1 h2) fun j => ?_
    rcases j with _ | j
    · simp
    · simp

set_option exponentiation.threshold 50000 in
theorem getS_packL {L : List Nat} (h : ∀ x ∈ L, x < 2 ^ 48720) {j : Nat} (hj : j < L.length) :
    getS (packL L) j = L[j] := by
  change CFSG.KC.Enum.pg 48720 (mask 48720) (packL L) j = _
  have e : L.getD j 0 = L[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hb : L.getD j 0 < 2 ^ 48720 := by
    rw [e]
    exact h _ (List.getElem_mem hj)
  rw [CFSG.KS.PackFld.pg_of_fld (w := 48720) (i := j) (g := fun j => L.getD j 0)
    (fld_packL L h) hb, e]

theorem lt_of_shr {x k : Nat} (h : x >>> k = 0) : x < 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).1 h

theorem mulP_lt (p q : Nat) : mulP p q < 2 ^ 48720 :=
  lt_of_shr (CFSG.KS.PackFld.pcomp_shr (n := 4060) (w := 12) (p := p) (q := q) (by decide)
    (by decide))

theorem wordP_lt (G GI : Nat → Nat) : ∀ w : List Int, wordP G GI w < 2 ^ 48720
  | [] => lt_of_shr (CFSG.KS.PF.pidn_shr (n := 4060) (w := 12) (by decide) (by decide))
  | l :: w => by rw [wordP_cons]; exact mulP_lt _ _

theorem bAnd_eq' (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  ⟨allN_spec, CFSG.KS.PackFld.allN_of_forall⟩

theorem ptK_spec {H HI : Nat → Nat} {b : Nat} {ss : List (List Int)} {fs : List (Nat × List Int)}
    (h : ptK H HI b ss fs = true) :
    (∀ s ∈ ss, apP (wordP H HI s) b = b) ∧
    (∀ i < 4060, (∃ f ∈ fs, f.1 = i) ∨ ∃ s ∈ ss, apP (wordP H HI s) i ≠ i) ∧
    ∀ f ∈ fs, apP (wordP H HI f.2) b = f.1 ∧ apP (wordP H HI f.2) f.1 = b := by
  unfold ptK at h
  rw [CFSG.KS.PackFld.strictB_eqP, bAnd_eq', bAnd_eq', Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlt : ∀ x ∈ ss.map (wordP H HI), x < 2 ^ 48720 := by
    intro x hx
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
    exact wordP_lt _ _ s
  have hget : ∀ j (hj : j < ss.length), getS (packL (ss.map (wordP H HI))) j =
      wordP H HI ss[j] := fun j hj => by
    rw [getS_packL hlt (by simpa using hj), List.getElem_map]
  refine ⟨fun s hs => ?_, fun i hi => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hs
    have := allN_spec h1 j hj
    rw [hget j hj] at this
    exact Nat.eq_of_beq_eq_true this
  · have := allN_spec h2 i hi
    rw [bIf_eq, bIf_eq] at this
    by_cases ha : (fs.any fun f => Nat.beq f.1 i) = true
    · left
      rw [List.any_eq_true] at ha
      obtain ⟨f, hf, he⟩ := ha
      exact ⟨f, hf, Nat.eq_of_beq_eq_true he⟩
    · right
      rw [ite_eq_right ha] at this
      by_cases hb : allN ss.length (fun j =>
          Nat.beq (apP (getS (packL (ss.map (wordP H HI))) j) i) i) = true
      · rw [ite_eq_left hb] at this
        exact absurd this Bool.false_ne_true
      · rw [allN_iff] at hb
        simp only [not_forall] at hb
        obtain ⟨j, hj, hne⟩ := hb
        refine ⟨ss[j], List.getElem_mem hj, fun e => hne ?_⟩
        rw [hget j hj, e]
        exact Nat.beq_refl i
  · rw [List.all_eq_true] at h3
    have := h3 f hf
    rw [CFSG.KS.PackFld.strictB_eqP, bAnd_eq', Bool.and_eq_true] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem fourBaseK_sound {p : Nat} {gs : List (Array Nat)} {G H HI : Nat → Nat}
    {hw : List (List Int)} {pts : List (Nat × List (List Int) × List (Nat × List Int))}
    (hG : ∀ l < gs.length, gs[l]! = unpack 4060 12 (G l))
    (hGp : ∀ l < gs.length, permOK 4060 12 (mask 12) (4060 * 12) (G l) (invP (G l)) = true)
    (hwl : hw.all (lettersOK gs.length) = true)
    (hH : ∀ i < hw.length, Nat.beq (H i) (wordP G (fun l => invP (G l)) hw[i]!) = true)
    (hHp : ∀ i < hw.length, permOK 4060 12 (mask 12) (4060 * 12) (H i) (HI i) = true)
    (hHo : ∀ i < hw.length, Nat.beq (powP (H i) p) idP = true)
    (hq : ∀ q ∈ pts, q.1 < 4060 ∧ q.2.1.all (lettersOK hw.length) = true ∧
      q.2.2.all (fun f => lettersOK hw.length f.2) = true ∧ ptK H HI q.1 q.2.1 q.2.2 = true) :
    fourBaseOK 4060 (gs.map tblOfArr).toArray hw p pts = true := by
  have hn : (4060 : Nat) < 2 ^ 32 := by decide
  have hperm : ∀ {P Q : Nat}, permOK 4060 12 (mask 12) (4060 * 12) P Q = true →
      Bij 4060 (apP P) (apP Q) := fun hpq => by
    obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts hpq
    exact bij_of (fun x hx => (h3 x hx).1) (fun x hx => (h3 x hx).2)
  set gens : Array Table := (gs.map tblOfArr).toArray with hgens
  have hgsz : gens.size = gs.length := by simp [hgens]
  have hA : ∀ k < gens.size, TR 4060 gens[k]! (apP (G k)) ∧
      TR 4060 (gens.map (invT 4060))[k]! (apP (invP (G k))) ∧
      Bij 4060 (apP (G k)) (apP (invP (G k))) := by
    intro k hk
    rw [hgsz] at hk
    have hb := hperm (hGp k hk)
    have e1 : gens[k]! = tblOfArr (unpack 4060 12 (G k)) := by
      rw [hgens, getElem!_pos _ k (by simpa using hk), List.getElem_toArray, List.getElem_map,
        ← getElem!_pos gs k hk, hG k hk]
    have hT : TR 4060 gens[k]! (apP (G k)) := by
      rw [e1]
      have h := tr_tblOfArr (n := 4060) (a := unpack 4060 12 (G k)) (by simp [unpack])
        (fun x hx => by
          rw [CFSG.KS.Raw.Orb.unpack_get hx]
          exact Nat.lt_trans (CFSG.KS.PackFld.pg_lt 12 _ _) (by decide))
      refine ⟨h.1, fun x hx => ?_⟩
      rw [h.2 x hx]
      exact CFSG.KS.Raw.Orb.unpack_get hx
    have e2 : (gens.map (invT 4060))[k]! = invT 4060 gens[k]! := by
      rw [getElem!_pos _ k (by simpa [hgsz] using hk), Array.getElem_map,
        getElem!_pos gens k (by rw [hgsz]; exact hk)]
    exact ⟨hT, by rw [e2]; exact tr_invT hn hT hb, hb⟩
  set hT : Array Table := (hw.map (wordT 4060 (letterTab gens (gens.map (invT 4060))))).toArray
    with hhT
  have hTsz : hT.size = hw.length := by simp [hhT]
  have hB : ∀ i < hT.size, TR 4060 hT[i]! (apP (H i)) ∧
      TR 4060 (hT.map (invT 4060))[i]! (apP (HI i)) ∧ Bij 4060 (apP (H i)) (apP (HI i)) := by
    intro i hi
    rw [hTsz] at hi
    have hb := hperm (hHp i hi)
    have hwi : lettersOK gens.size hw[i] = true := by
      rw [List.all_eq_true] at hwl
      rw [hgsz]
      exact hwl _ (List.getElem_mem hi)
    have hw1 := (tr_word hA hw[i] hwi).1
    have e0 : H i = wordP G (fun l => invP (G l)) hw[i] := by
      have := Nat.eq_of_beq_eq_true (hH i hi)
      rwa [getElem!_pos hw i hi] at this
    have e1 : hT[i]! = wordT 4060 (letterTab gens (gens.map (invT 4060))) hw[i] := by
      rw [hhT, getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getElem_map]
    have hTi : TR 4060 hT[i]! (apP (H i)) := by
      rw [e1, e0]
      exact hw1
    have e2 : (hT.map (invT 4060))[i]! = invT 4060 hT[i]! := by
      rw [getElem!_pos _ i (by simpa [hTsz] using hi), Array.getElem_map,
        getElem!_pos hT i (by rw [hTsz]; exact hi)]
    exact ⟨hTi, by rw [e2]; exact tr_invT hn hTi hb, hb⟩
  unfold fourBaseOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro k hk
    have := hA k hk
    have e2 : (gens.map (invT 4060))[k]! = invT 4060 gens[k]! := by
      rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos gens k hk]
    rw [← getElem!_pos gens k hk, ← e2]
    exact invOK_of this.1 this.2.1 this.2.2
  · rw [hgsz]
    exact hwl
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨h1, h2, h3⟩ := hB i hi
    rw [Bool.and_eq_true]
    refine ⟨invOK_of h1 h2 h3, ?_⟩
    have hi' : i < hw.length := by rw [← hTsz]; exact hi
    have hlet : lettersOK hT.size (List.replicate p ((i : Int) + 1)) = true := by
      simp only [lettersOK, List.all_eq_true, List.mem_replicate, Bool.and_eq_true, bne_iff_ne,
        ne_eq, decide_eq_true_eq]
      rintro z ⟨-, rfl⟩
      omega
    have hr := (tr_word hB _ hlet).1
    have hpow : ∀ x < 4060, apP (wordP H HI (List.replicate p ((i : Int) + 1))) x = x := by
      have e : ∀ e x, x < 4060 → apP (wordP H HI (List.replicate e ((i : Int) + 1))) x =
          apP (powP (H i) e) x := by
        intro e
        induction e with
        | zero => intro x hx; rfl
        | succ e ih =>
          intro x hx
          rw [List.replicate_succ, wordP_cons, apP_mulP hx, ih x hx]
          change _ = apP (strictN (powP (H i) e) (fun a => mulP (H i) a)) x
          rw [CFSG.KS.PackFld.strictN_eqP, apP_mulP hx]
          rfl
      intro x hx
      rw [e p x hx, Nat.eq_of_beq_eq_true (hHo i hi'), apP_idP hx]
    unfold tblEq
    rw [allIn_iff]
    intro x hx
    rw [hr.2 x hx, hpow x hx, (tr_idT hn).2 x hx, beq_self_eq_true]
  · rw [List.all_eq_true]
    intro q hqm
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hq q hqm
    obtain ⟨k1, k2, k3⟩ := ptK_spec hq4
    rw [← hTsz] at hq2 hq3
    have hss : ∀ s ∈ q.2.1, TR 4060 (wordT 4060 (letterTab hT (hT.map (invT 4060))) s)
        (apP (wordP H HI s)) ∧ ∀ x < 4060, apP (wordP H HI s) x < 4060 := fun s hs => by
      rw [List.all_eq_true] at hq2
      exact tr_word hB s (hq2 s hs)
    have hfs : ∀ f ∈ q.2.2, TR 4060 (wordT 4060 (letterTab hT (hT.map (invT 4060))) f.2)
        (apP (wordP H HI f.2)) ∧ ∀ x < 4060, apP (wordP H HI f.2) x < 4060 := fun f hf => by
      rw [List.all_eq_true] at hq3
      exact tr_word hB f.2 (hq3 f hf)
    unfold basePtOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨hq1, hq2⟩, hq3⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro s hs
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
      rw [(hss s' hs').1.2 _ hq1, k1 s' hs', beq_self_eq_true]
    · unfold allIn
      rw [Nat.all_eq_finRange_all, List.all_eq_true]
      intro x _
      simp only [Nat.zero_add, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false,
        List.any_eq_true, beq_iff_eq]
      rcases k2 x.val x.isLt with ⟨f, hf, he⟩ | ⟨s, hs, hne⟩
      · right
        exact ⟨f, hf, he⟩
      · left
        refine ⟨_, List.mem_map_of_mem hs, ?_⟩
        rw [(hss s hs).1.2 _ x.isLt]
        simpa using hne
    · rw [List.all_eq_true]
      intro f hf
      obtain ⟨e1, e2⟩ := k3 f hf
      have hf1 : f.1 < 4060 := by
        rw [← e1]
        exact (hfs f hf).2 _ hq1
      rw [Bool.and_eq_true, (hfs f hf).1.2 _ hq1, (hfs f hf).1.2 _ hf1, e1, e2, beq_self_eq_true,
        beq_self_eq_true]
      exact ⟨rfl, rfl⟩

end CFSG.KC.Misc.RuBase

end
