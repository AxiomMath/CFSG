module

public import Certificates.Data.Kernel.Co3Nine.Defs
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.NativeSetOrbit
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.Co3Nine

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.Certificates
open scoped Pointwise

@[expose] def gL (m : Nat → Equiv.Perm (Fin 276)) (l : Nat) : Equiv.Perm (Fin 276) :=
  if l < 8 then m (l - 1) else (m (l - 8))⁻¹

@[expose] def wP (m : Nat → Equiv.Perm (Fin 276)) (w : List Nat) : Equiv.Perm (Fin 276) :=
  (w.map (gL m)).prod

@[expose] def Letters (w : List Nat) : Prop := ∀ l ∈ w, 0 < l ∧ l < 15

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nb {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem wP_mem {m : Nat → Equiv.Perm (Fin 276)} {H : Subgroup (Equiv.Perm (Fin 276))}
    (hm : ∀ j < 7, m j ∈ H) : ∀ w : List Nat, Letters w → wP m w ∈ H
  | [], _ => H.one_mem
  | l :: w, h => by
    have ih := wP_mem hm w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨h0, h15⟩ := h l List.mem_cons_self
    have hl : gL m l ∈ H := by
      unfold gL
      split_ifs with h8
      · exact hm _ (by omega)
      · exact H.inv_mem (hm _ (by omega))
    simpa only [wP, List.map_cons, List.prod_cons] using H.mul_mem hl ih

theorem lettersK_spec : ∀ w : List Nat, lettersK w = true → Letters w
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | l :: w, h => by
    have h' : bAnd(Nat.blt 0 l, bAnd(Nat.blt l 15, lettersK w)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2⟩
    · exact lettersK_spec w h3 l' hl'

theorem ptsK_spec : ∀ L : List Nat, ptsK L = true → ∀ p ∈ L, p < 276
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | p :: L, h => by
    have h' : bAnd(Nat.blt p 276, ptsK L) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Nat.blt_eq.mp h1
    · exact ptsK_spec L h2 q hq

theorem cntK_eq : ∀ L : List Nat, cntK L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (cntK L) = _
    rw [cntK_eq L]
    rfl

theorem sortedK_spec : ∀ L : List Nat, sortedK L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have ih := sortedK_spec xs h2
    refine List.Pairwise.cons (fun y hy => ?_) ih
    cases xs with
    | nil => exact absurd hy List.not_mem_nil
    | cons z zs =>
      have hxz : x < z := Nat.blt_eq.mp h1
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hxz
      · exact hxz.trans (List.rel_of_pairwise_cons ih hy')

variable {S SI TS : Nat → Nat} {m tg : Nat → Equiv.Perm (Fin 276)}

theorem imK_eq {P : Nat} {g : Equiv.Perm (Fin 276)} (hP : PRep 276 9 P g) (x : Fin 276) :
    imK P x = (g x : Nat) :=
  hP x

theorem ltK_rep (hS : ∀ j < 7, PRep 276 9 (S j) (m j) ∧ PRep 276 9 (SI j) (m j)⁻¹) {l : Nat}
    (h0 : 0 < l) (h15 : l < 15) : PRep 276 9 (ltK S SI l) (gL m l) := by
  unfold ltK gL
  cases hb : Nat.blt l (nat_lit 8) with
  | false =>
    have h8 : ¬ l < 8 := fun h => by
      have h2 : Nat.blt l (nat_lit 8) = true := Nat.blt_eq.mpr h
      rw [hb] at h2
      exact Bool.noConfusion h2
    rw [if_neg h8]
    exact (hS (l - 8) (by omega)).2
  | true =>
    have h8 : l < 8 := Nat.blt_eq.mp hb
    rw [if_pos h8]
    exact (hS (l - 1) (by omega)).1

theorem walk_eq (hS : ∀ j < 7, PRep 276 9 (S j) (m j) ∧ PRep 276 9 (SI j) (m j)⁻¹) :
    ∀ w : List Nat, Letters w → ∀ x : Fin 276, walkK S SI w x = (wP m w x : Nat)
  | [], _, _ => rfl
  | l :: w, h, x => by
    have ih := walk_eq hS w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) x
    obtain ⟨h0, h15⟩ := h l List.mem_cons_self
    change strictN (walkK S SI w x) (fun q => imK (ltK S SI l) q) = _
    rw [strictN_app, ih, imK_eq (ltK_rep hS h0 h15)]
    simp only [wP, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

theorem keyK_testBit (f : Nat → Nat) (q : Nat) : ∀ L : List Nat,
    (keyK f L).testBit q = decide (∃ p ∈ L, f p = q)
  | [] => by
    change Nat.testBit 0 q = _
    simp
  | p :: L => by
    have e : keyK f (p :: L) = 2 ^ f p ||| keyK f L := by
      change Nat.lor (Nat.shiftLeft 1 (f p)) (keyK f L) = _
      change 1 <<< f p ||| keyK f L = _
      rw [Nat.one_shiftLeft]
    rw [e, Nat.testBit_or, Nat.testBit_two_pow, keyK_testBit f q L]
    by_cases h : f p = q
    · simp [h]
    · simp [h]

theorem keyK_eq_iff {f g : Nat → Nat} {L : List Nat} :
    keyK f L = keyK g L ↔ ∀ q, (∃ p ∈ L, f p = q) ↔ (∃ p ∈ L, g p = q) := by
  constructor
  · intro h q
    have := congrArg (fun k => Nat.testBit k q) h
    simp only [keyK_testBit] at this
    exact decide_eq_decide.mp this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [keyK_testBit, keyK_testBit]
    exact decide_eq_decide.mpr (h q)

theorem mem_smul_finSet {σ : Equiv.Perm (Fin 276)} {L : List Nat} {f : Nat → Nat}
    (hL : ∀ p ∈ L, p < 276) (hf : ∀ x : Fin 276, f x = (σ x : Nat)) (x : Fin 276) :
    x ∈ σ • finSet 276 L ↔ ∃ p ∈ L, f p = x := by
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change ((σ⁻¹ x : Fin 276) : Nat) ∈ L ↔ _
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    rw [hf]
    simp
  · rintro ⟨p, hp, hfp⟩
    have e : σ ⟨p, hL p hp⟩ = x := Fin.ext (by rw [← hf ⟨p, hL p hp⟩]; exact hfp)
    rw [← e]
    simpa using hp

theorem smul_eq_iff {σ τ : Equiv.Perm (Fin 276)} {L : List Nat} {f g : Nat → Nat}
    (hL : ∀ p ∈ L, p < 276) (hf : ∀ x : Fin 276, f x = (σ x : Nat))
    (hg : ∀ x : Fin 276, g x = (τ x : Nat)) :
    σ • finSet 276 L = τ • finSet 276 L ↔ keyK f L = keyK g L := by
  rw [keyK_eq_iff]
  constructor
  · intro h q
    by_cases hq : q < 276
    · have h1 := mem_smul_finSet hL hf ⟨q, hq⟩
      have h2 := mem_smul_finSet hL hg ⟨q, hq⟩
      rw [h] at h1
      exact h1.symm.trans h2
    · constructor
      · rintro ⟨p, hp, hfp⟩
        have h1 : f p = (σ ⟨p, hL p hp⟩ : Nat) := hf ⟨p, hL p hp⟩
        have h2 := (σ ⟨p, hL p hp⟩).2
        omega
      · rintro ⟨p, hp, hgp⟩
        have h1 : g p = (τ ⟨p, hL p hp⟩ : Nat) := hg ⟨p, hL p hp⟩
        have h2 := (τ ⟨p, hL p hp⟩).2
        omega
  · intro h
    ext x
    rw [mem_smul_finSet hL hf, mem_smul_finSet hL hg]
    exact h x

theorem eqPtK_iff {σ τ : Equiv.Perm (Fin 276)} {f g : Nat → Nat}
    (hf : ∀ x : Fin 276, f x = (σ x : Nat)) (hg : ∀ x : Fin 276, g x = (τ x : Nat)) :
    eqPtK f g = true ↔ σ = τ := by
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    rw [← hf, ← hg]
    exact Nat.eq_of_beq_eq_true (allN_spec h x x.2)
  · rintro rfl
    refine CFSG.KS.PackFld.allN_of_forall fun p hp => ?_
    have h1 : f p = (σ ⟨p, hp⟩ : Nat) := hf ⟨p, hp⟩
    have h2 : g p = (σ ⟨p, hp⟩ : Nat) := hg ⟨p, hp⟩
    change Nat.beq (f p) (g p) = true
    rw [h1, h2]
    exact Nat.beq_refl _

theorem rowsK_spec {Y : List Nat} {kY : Nat} : ∀ (ks : List Nat) (es : List (List Nat)),
    rowsK S SI TS Y kY ks es = true → es.length = ks.length ∧
      ∀ i < ks.length, ∃ t w, es.getD i [] = t :: w ∧
        rowK S SI TS Y kY (ks.getD i 0) t w = true
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | [], e :: es, h => by
    have e0 : rowsK S SI TS Y kY [] (e :: es) = false := rfl
    rw [e0] at h
    exact absurd h (by decide)
  | k :: ks, [], h => by
    have e0 : rowsK S SI TS Y kY (k :: ks) [] = false := rfl
    rw [e0] at h
    exact absurd h (by decide)
  | k :: ks, [] :: es, h => by
    have e0 : rowsK S SI TS Y kY (k :: ks) ([] :: es) = false := rfl
    rw [e0] at h
    exact absurd h (by decide)
  | k :: ks, (t :: w) :: es, h => by
    have h' : bAnd(rowK S SI TS Y kY k t w, rowsK S SI TS Y kY ks es) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨hl, hr⟩ := rowsK_spec ks es h2
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨t, w, rfl, h1⟩
    | succ i =>
      obtain ⟨t', w', h1', h2'⟩ := hr i (by simpa using hi)
      exact ⟨t', w', by simpa using h1', by simpa using h2'⟩

theorem co39K_sound (hS : ∀ j < 7, PRep 276 9 (S j) (m j) ∧ PRep 276 9 (SI j) (m j)⁻¹)
    (hT : ∀ t < 8, PRep 276 9 (TS t) (tg t)) {Y wx wy ks : List Nat} {es : List (List Nat)}
    (h : co39K S SI TS Y wx wy ks es = true) :
    let X₀ := finSet 276 Y
    let x := wP m wx
    let y := wP m wy
    Letters wx ∧ Letters wy ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ≠ 1 ∧ y ≠ x ∧
      y ≠ x * x ∧ x • X₀ = X₀ ∧ y • X₀ = X₀ ∧ (∀ t < 8, tg t • X₀ = X₀) ∧ es.length = 315 ∧
      (∀ i < 315, Letters (es.getD i []).tail) ∧
      (∀ i j, i < 315 → j < 315 →
        wP m (es.getD i []).tail • X₀ = wP m (es.getD j []).tail • X₀ → i = j) ∧
      (∀ i < 315, wP m (es.getD i []).tail • X₀ = X₀ ∨
        ∃ t < 8, tg t • (wP m (es.getD i []).tail • X₀) ≠ wP m (es.getD i []).tail • X₀) := by
  intro X₀ x y
  rw [co39K, strictB_app] at h
  obtain ⟨hpts, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hxy, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨htf, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hcnt, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hsort, hrows⟩ := (bAnd_iff _ _).1 h
  have hY := ptsK_spec Y hpts
  have hid : ∀ x : Fin 276, (fun p : Nat => p) x = ((1 : Equiv.Perm (Fin 276)) x : Nat) :=
    fun _ => rfl
  have hfixY : ∀ {σ : Equiv.Perm (Fin 276)} {f : Nat → Nat},
      (∀ x : Fin 276, f x = (σ x : Nat)) → keyK f Y = keyK (fun p => p) Y → σ • X₀ = X₀ := by
    intro σ f hf hk
    have := (smul_eq_iff hY hf hid).2 hk
    rwa [one_smul] at this
  unfold xyK at hxy
  unfold tFixK at htf
  obtain ⟨hlx, h⟩ := (bAnd_iff _ _).1 hxy
  obtain ⟨hly, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hx3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hy3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hx1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hy1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hyx, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hyx2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hfx, hfy⟩ := (bAnd_iff _ _).1 h
  have lx := lettersK_spec wx hlx
  have ly := lettersK_spec wy hly
  have wx' : ∀ a : Fin 276, walkK S SI wx a = (x a : Nat) := walk_eq hS wx lx
  have wy' : ∀ a : Fin 276, walkK S SI wy a = (y a : Nat) := walk_eq hS wy ly
  have wxx : ∀ a : Fin 276, walkK S SI wx (x a) = (x (x a) : Nat) := fun a => wx' (x a)
  have wyy : ∀ a : Fin 276, walkK S SI wy (y a) = (y (y a) : Nat) := fun a => wy' (y a)
  have e1 : ∀ a : Fin 276, walkK S SI wx (walkK S SI wx (walkK S SI wx a)) = ((x ^ 3) a : Nat) := by
    intro a
    rw [wx', wxx, wx' (x (x a))]
    simp [pow_succ, Equiv.Perm.mul_apply]
  have e2 : ∀ a : Fin 276, walkK S SI wy (walkK S SI wy (walkK S SI wy a)) = ((y ^ 3) a : Nat) := by
    intro a
    rw [wy', wyy, wy' (y (y a))]
    simp [pow_succ, Equiv.Perm.mul_apply]
  have e3 : ∀ a : Fin 276, walkK S SI wx (walkK S SI wy a) = ((x * y) a : Nat) := by
    intro a
    rw [wy', wx' (y a)]
    rfl
  have e4 : ∀ a : Fin 276, walkK S SI wy (walkK S SI wx a) = ((y * x) a : Nat) := by
    intro a
    rw [wx', wy' (x a)]
    rfl
  have e5 : ∀ a : Fin 276, walkK S SI wx (walkK S SI wx a) = ((x * x) a : Nat) := by
    intro a
    rw [wx', wxx]
    rfl
  refine ⟨lx, ly, (eqPtK_iff e1 hid).1 hx3, (eqPtK_iff e2 hid).1 hy3, (eqPtK_iff e3 e4).1 hc,
    fun he => ?_, fun he => ?_, fun he => ?_, fun he => ?_, hfixY wx' (Nat.eq_of_beq_eq_true hfx),
    hfixY wy' (Nat.eq_of_beq_eq_true hfy), ?_, ?_⟩
  · have := (eqPtK_iff (g := fun p => p) wx' hid).2 he
    rw [nb hx1] at this
    exact absurd this (by decide)
  · have := (eqPtK_iff (g := fun p => p) wy' hid).2 he
    rw [nb hy1] at this
    exact absurd this (by decide)
  · have := (eqPtK_iff wy' wx').2 he
    rw [nb hyx] at this
    exact absurd this (by decide)
  · have := (eqPtK_iff (g := fun p => walkK S SI wx (walkK S SI wx p)) wy' e5).2 he
    rw [nb hyx2] at this
    exact absurd this (by decide)
  · intro t ht
    have hk := Nat.eq_of_beq_eq_true (allN_spec htf t ht)
    exact hfixY (imK_eq (hT t ht)) hk
  have hlen : ks.length = 315 := by
    rw [← cntK_eq]
    exact Nat.eq_of_beq_eq_true hcnt
  obtain ⟨hel, hrow⟩ := rowsK_spec ks es hrows
  have hpw := sortedK_spec ks hsort
  have row : ∀ i < 315, Letters (es.getD i []).tail ∧
      keyK (walkK S SI (es.getD i []).tail) Y = ks.getD i 0 ∧
      (ks.getD i 0 = keyK (fun p => p) Y ∨ ∃ t < 8,
        keyK (fun p => imK (TS t) (walkK S SI (es.getD i []).tail p)) Y ≠ ks.getD i 0) := by
    intro i hi
    obtain ⟨t, w, hte, hr⟩ := hrow i (by omega)
    rw [hte, List.tail_cons]
    unfold rowK at hr
    obtain ⟨r1, hr⟩ := (bAnd_iff _ _).1 hr
    obtain ⟨r2, r3⟩ := (bAnd_iff _ _).1 hr
    refine ⟨lettersK_spec w r1, Nat.eq_of_beq_eq_true r2, ?_⟩
    cases hk : Nat.beq (ks.getD i 0) (keyK (fun p => p) Y) with
    | true => exact Or.inl (Nat.eq_of_beq_eq_true hk)
    | false =>
      rw [hk] at r3
      obtain ⟨r4, r5⟩ := (bAnd_iff _ _).1 r3
      refine Or.inr ⟨t, Nat.blt_eq.mp r4, fun he => ?_⟩
      rw [he, Nat.beq_refl] at r5
      exact absurd r5 (by decide)
  have wrow : ∀ i < 315, ∀ a : Fin 276,
      walkK S SI (es.getD i []).tail a = (wP m (es.getD i []).tail a : Nat) :=
    fun i hi => walk_eq hS _ (row i hi).1
  refine ⟨hel.trans hlen, fun i hi => (row i hi).1, fun i j hi hj he => ?_, fun i hi => ?_⟩
  · have hk := (smul_eq_iff hY (wrow i hi) (wrow j hj)).1 he
    rw [(row i hi).2.1, (row j hj).2.1] at hk
    have hget : ∀ a (ha : a < ks.length), ks.getD a 0 = ks[a] := by
      intro a ha
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
      rfl
    rw [hget i (by omega), hget j (by omega)] at hk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hij | hij
    · have := List.pairwise_iff_getElem.1 hpw i j (by omega) (by omega) hij
      omega
    · have := List.pairwise_iff_getElem.1 hpw j i (by omega) (by omega) hij
      omega
  · rcases (row i hi).2.2 with hk | ⟨t, ht, hk⟩
    · left
      exact hfixY (wrow i hi) ((row i hi).2.1.trans hk)
    · right
      refine ⟨t, ht, fun he => hk ?_⟩
      rw [smul_smul] at he
      have hf : ∀ a : Fin 276, (fun p => imK (TS t) (walkK S SI (es.getD i []).tail p)) a =
          ((tg t * wP m (es.getD i []).tail) a : Nat) := by
        intro a
        change imK (TS t) (walkK S SI (es.getD i []).tail a) = _
        rw [wrow i hi a, imK_eq (hT t ht)]
        rfl
      rw [← (row i hi).2.1]
      exact (smul_eq_iff hY hf (wrow i hi)).1 he

end CFSG.KS.Co3Nine

end
