module

public import Certificates.Data.Kernel.BabyMonster.B9201Facts
public import CFSG.Certificates.Kernel.BabyMonster.WfProd

public section

namespace CFSG.KC.BM.Run

open CFSG.Monster.B.Primes.Native CFSG.KC.BM.B9201

@[expose] def look : List (ℕ × ℕ × ℕ) → ℕ → ℕ → Option ℕ
  | [], _, _ => none
  | (a, b, c) :: t, x, y => cond (Nat.beq a x && Nat.beq b y) (some c) (look t x y)

@[expose] def symMul (tab : List (ℕ × ℕ × ℕ)) : Option ℕ → Option ℕ → Option (Option ℕ)
  | none, b => some b
  | some x, none => some (some x)
  | some x, some y => (look tab x y).map some

@[expose] def symPow (tab : List (ℕ × ℕ × ℕ)) : ℕ → ℕ → Option ℕ → Option (Option ℕ)
  | 0, _, _ => none
  | _ + 1, 0, _ => some none
  | _ + 1, 1, a => some a
  | f + 1, e + 2, a => (symMul tab a a).bind fun sq => (symPow tab f ((e + 2) / 2) sq).bind
      fun Y => cond (Nat.beq ((e + 2) % 2) 1) (symMul tab a Y) (some Y)

@[expose] def outReg : Ins → ℕ
  | .mu _ _ k => k
  | .iv _ k => k
  | .pwr _ _ k => k

@[expose] def stepVal (tab : List (ℕ × ℕ × ℕ)) (σ : ℕ → Option ℕ) : Ins → Option (Option ℕ)
  | .mu i j _ => symMul tab (σ i) (σ j)
  | .iv _ _ => none
  | .pwr e i _ => symPow tab e e (σ i)

@[expose] def oeq : Option (Option ℕ) → Option ℕ → Bool
  | some none, none => true
  | some (some x), some y => Nat.beq x y
  | _, _ => false

@[expose] def upd (σ : ℕ → Option ℕ) (k : ℕ) (o : Option ℕ) : ℕ → Option ℕ :=
  fun i => cond (Nat.beq i k) o (σ i)

@[expose] def runOK (tab : List (ℕ × ℕ × ℕ)) : List Ins → List (Option ℕ) → (ℕ → Option ℕ) → Bool
  | [], [], _ => true
  | ins :: p, o :: os, σ => oeq (stepVal tab σ ins) o && runOK tab p os (upd σ (outReg ins) o)
  | _, _, _ => false

@[expose] def finSt : List Ins → List (Option ℕ) → (ℕ → Option ℕ) → ℕ → Option ℕ
  | ins :: p, o :: os, σ => finSt p os (upd σ (outReg ins) o)
  | _, _, σ => σ

@[expose] def init2 : ℕ → Option ℕ := fun i => cond (Nat.beq i 1) (some 0) (cond (Nat.beq i 2) (some 1) none)

@[expose] def finOK (σ : ℕ → Option ℕ) (regs : ℕ → ℕ) (B : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | k, i :: is => oeq (some (σ (regs k))) (some i) && Nat.blt i B && finOK σ regs B (k + 1) is

@[expose] def ordOK : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | n, (x, y, z) :: t => Nat.beq z n && Nat.blt x n && Nat.blt y n && ordOK (n + 1) t

@[expose] def TabOK (L : List (List ℕ)) (tab : List (ℕ × ℕ × ℕ)) : Prop :=
  List.rec (motive := fun _ => Prop) True
    (fun e _ ih => AllStrips [L.getD e.2.1 []] (L.getD e.1 []) (L.getD e.2.2 []) ∧ ih) tab

theorem beq_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

section Monoid

variable {M : Type*} [Monoid M] (val : ℕ → M)

@[expose] def valO : Option ℕ → M
  | none => 1
  | some i => val i

@[expose] def TabSound (tab : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ p ∈ tab, val p.1 * val p.2.1 = val p.2.2

variable {val}

theorem look_sound : ∀ {tab : List (ℕ × ℕ × ℕ)}, TabSound val tab → ∀ {x y z : ℕ},
    look tab x y = some z → val x * val y = val z
  | [], _, _, _, _, h => by simp [look] at h
  | (a, b, c) :: t, ht, x, y, z, h => by
    unfold look at h
    cases hc : (Nat.beq a x && Nat.beq b y)
    · rw [hc, cond_false] at h
      exact look_sound (fun p hp => ht p (List.mem_cons_of_mem _ hp)) h
    · rw [hc, cond_true, Option.some.injEq] at h
      rw [Bool.and_eq_true] at hc
      have e1 := Nat.eq_of_beq_eq_true hc.1
      have e2 := Nat.eq_of_beq_eq_true hc.2
      subst e1 e2 h
      exact ht _ List.mem_cons_self

theorem symMul_sound {tab : List (ℕ × ℕ × ℕ)} (ht : TabSound val tab) :
    ∀ {a b : Option ℕ} {c : Option ℕ}, symMul tab a b = some c →
      valO val a * valO val b = valO val c
  | none, b, c, h => by
    simp only [symMul, Option.some.injEq] at h
    rw [h, valO, one_mul]
  | some x, none, c, h => by
    simp only [symMul, Option.some.injEq] at h
    rw [← h, valO, valO, mul_one]
  | some x, some y, c, h => by
    simp only [symMul, Option.map_eq_some_iff] at h
    obtain ⟨z, hz, rfl⟩ := h
    exact look_sound ht hz

theorem symPow_sound {tab : List (ℕ × ℕ × ℕ)} (ht : TabSound val tab) :
    ∀ (f e : ℕ) {a c : Option ℕ}, symPow tab f e a = some c → valO val a ^ e = valO val c
  | 0, _, _, _, h => by simp [symPow] at h
  | _ + 1, 0, a, c, h => by
    simp only [symPow, Option.some.injEq] at h
    rw [← h, pow_zero, valO]
  | _ + 1, 1, a, c, h => by
    simp only [symPow, Option.some.injEq] at h
    rw [h, pow_one]
  | f + 1, e + 2, a, c, h => by
    simp only [symPow, Option.bind_eq_some_iff] at h
    obtain ⟨sq, hsq, Y, hY, hc⟩ := h
    have e1 := symMul_sound ht hsq
    have e2 := symPow_sound ht f ((e + 2) / 2) hY
    rw [← e1, ← pow_two, ← pow_mul] at e2
    cases hm : Nat.beq ((e + 2) % 2) 1
    · rw [hm, cond_false, Option.some.injEq] at hc
      have : (e + 2) % 2 = 0 := by
        have := Nat.ne_of_beq_eq_false hm
        omega
      rw [← hc, ← e2]
      congr 1
      omega
    · rw [hm, cond_true] at hc
      have : (e + 2) % 2 = 1 := Nat.eq_of_beq_eq_true hm
      rw [← symMul_sound ht hc, ← e2, ← pow_succ']
      congr 1
      omega

theorem oeq_eq {u : Option (Option ℕ)} {o : Option ℕ} (h : oeq u o = true) : u = some o := by
  match u, o, h with
  | some none, none, _ => rfl
  | some (some x), some y, h => rw [Nat.eq_of_beq_eq_true h]

theorem valO_upd (σ : ℕ → Option ℕ) (k : ℕ) (o : Option ℕ) :
    (fun i => valO val (upd σ k o i)) = Function.update (fun i => valO val (σ i)) k (valO val o) := by
  funext i
  unfold upd
  by_cases hi : i = k
  · subst hi
    rw [Nat.beq_refl, cond_true, Function.update_self]
  · rw [beq_ne hi, cond_false, Function.update_of_ne hi]

theorem step_sound {tab : List (ℕ × ℕ × ℕ)} (ht : TabSound val tab) (σ : ℕ → Option ℕ) (ins : Ins)
    (o : Option ℕ) (h : stepVal tab σ ins = some o) :
    insStepM (fun i => valO val (σ i)) ins = fun i => valO val (upd σ (outReg ins) o i) := by
  rw [valO_upd]
  cases ins with
  | mu i j k =>
    simp only [stepVal] at h
    simp only [insStepM, outReg, symMul_sound ht h]
  | iv i k => simp [stepVal] at h
  | pwr e i k =>
    simp only [stepVal] at h
    simp only [insStepM, outReg, symPow_sound ht e e h]

theorem runOK_sound {tab : List (ℕ × ℕ × ℕ)} (ht : TabSound val tab) :
    ∀ (prog : List Ins) (outs : List (Option ℕ)) (σ : ℕ → Option ℕ), runOK tab prog outs σ = true →
      prog.foldl insStepM (fun i => valO val (σ i)) = fun i => valO val (finSt prog outs σ i)
  | [], [], σ, _ => rfl
  | [], _ :: _, _, h => by simp [runOK] at h
  | _ :: _, [], _, h => by simp [runOK] at h
  | ins :: p, o :: os, σ, h => by
    simp only [runOK, Bool.and_eq_true] at h
    rw [List.foldl_cons, step_sound ht σ ins o (oeq_eq h.1)]
    exact runOK_sound ht p os _ h.2

theorem valO_init2 (a b : M) (h0 : val 0 = a) (h1 : val 1 = b) :
    (fun i => valO val (init2 i)) = fun i => if i = 1 then a else if i = 2 then b else 1 := by
  funext i
  unfold init2
  by_cases e1 : i = 1
  · subst e1
    simp [valO, h0]
  · by_cases e2 : i = 2
    · subst e2
      simp [valO, h1]
    · rw [beq_ne e1, beq_ne e2]
      simp [valO, e1, e2]

end Monoid

@[expose] noncomputable def litV (L : List (List ℕ)) (i : ℕ) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  stripMat (L.getD i [])

theorem tab_sound {L : List (List ℕ)} : ∀ (tab : List (ℕ × ℕ × ℕ)) (n : ℕ),
    (∀ i < n, wfMat (L.getD i []) = true) → ordOK n tab = true → TabOK L tab →
      (∀ i < n + tab.length, wfMat (L.getD i []) = true) ∧ TabSound (litV L) tab
  | [], n, hb, _, _ => ⟨by simpa using hb, fun _ hp => by simp at hp⟩
  | (x, y, z) :: t, n, hb, ho, htab => by
    simp only [ordOK, Bool.and_eq_true] at ho
    obtain ⟨⟨⟨hz, hx⟩, hy⟩, ho⟩ := ho
    have hz := Nat.eq_of_beq_eq_true hz
    have hx := Nat.le_of_ble_eq_true hx
    have hy := Nat.le_of_ble_eq_true hy
    subst hz
    obtain ⟨hs, htab⟩ := htab
    have hwz : wfMat (L.getD z []) = true := wfMat_of_allStrips (hb x (by omega)) hs
    have hb' : ∀ i < z + 1, wfMat (L.getD i []) = true := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hb i hi
      · exact hwz
    obtain ⟨hw, hsnd⟩ := tab_sound t (z + 1) hb' ho htab
    refine ⟨fun i hi => hw i (by simp at hi; omega), ?_⟩
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact stripMat_mul1 (hb x (by omega)) (hb y (by omega)) hs
    · exact hsnd p hp

theorem finOK_spec {σ : ℕ → Option ℕ} {regs : ℕ → ℕ} {B : ℕ} : ∀ (is : List ℕ) (k₀ : ℕ),
    finOK σ regs B k₀ is = true → ∀ k < is.length, σ (regs (k₀ + k)) = some (is.getD k 0) ∧
      is.getD k 0 < B
  | [], _, _, k, hk => by simp at hk
  | i :: is, k₀, h, k, hk => by
    simp only [finOK, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases k with
    | zero =>
      have := oeq_eq h1
      simp only [Option.some.injEq] at this
      simpa [this] using Nat.le_of_ble_eq_true h2
    | succ k =>
      have := finOK_spec is (k₀ + 1) h3 k (by simpa using hk)
      rw [show k₀ + (k + 1) = k₀ + 1 + k by omega]
      simpa using this

theorem progCert {L : List (List ℕ)} {tab : List (ℕ × ℕ × ℕ)} {prog : List Ins}
    {outs : List (Option ℕ)} {regs : ℕ → ℕ} {tgt : List (List ℕ)} (idx : List ℕ)
    (h0 : wfMat (L.getD 0 []) = true) (h1 : wfMat (L.getD 1 []) = true)
    (hord : ordOK 2 tab = true) (htab : TabOK L tab) (hrun : runOK tab prog outs init2 = true)
    (hfin : finOK (finSt prog outs init2) regs (2 + tab.length) 0 idx = true)
    (hL : idx.map (fun i => L.getD i []) = tgt) :
    ∀ k < tgt.length, runM prog (stripMat (L.getD 0 [])) (stripMat (L.getD 1 [])) (regs k) =
      stripMat (tgt.getD k []) ∧ wfMat (tgt.getD k []) = true := by
  have hb : ∀ i < 2, wfMat (L.getD i []) = true := by
    intro i hi
    interval_cases i
    · exact h0
    · exact h1
  obtain ⟨hw, hs⟩ := tab_sound tab 2 hb hord htab
  have hr := runOK_sound hs prog outs init2 hrun
  rw [valO_init2 (stripMat (L.getD 0 [])) (stripMat (L.getD 1 [])) rfl rfl] at hr
  intro k hk
  have hlen : idx.length = tgt.length := by rw [← hL, List.length_map]
  obtain ⟨e1, e2⟩ := finOK_spec idx 0 hfin k (by omega)
  rw [Nat.zero_add] at e1
  have ht : tgt.getD k [] = L.getD (idx.getD k 0) [] := by
    have hk' : k < idx.length := by omega
    rw [← hL, List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map,
      List.getD_eq_getElem _ _ hk']
  refine ⟨?_, by rw [ht]; exact hw _ e2⟩
  unfold runM
  rw [hr]
  beta_reduce
  rw [e1, ht]
  rfl

example : runOK [(0, 1, 2)] [.mu 1 2 3] [some 2] init2 = true := by decide
example : runOK [(0, 1, 2)] [.mu 1 2 3] [some 3] init2 = false := by decide
example : runOK [(0, 1, 2)] [.mu 2 1 3] [some 2] init2 = false := by decide
example : runOK [] [.iv 1 3] [none] init2 = false := by decide
example : runOK [(0, 0, 2), (0, 2, 3)] [.pwr 3 1 4] [some 3] init2 = true := by decide
example : runOK [(0, 0, 2), (0, 2, 3)] [.pwr 3 1 4] [some 2] init2 = false := by decide
example : ordOK 2 [(0, 1, 2)] = true := by decide
example : ordOK 2 [(0, 1, 3)] = false := by decide
example : ordOK 2 [(0, 2, 2)] = false := by decide
example : finOK (finSt [.mu 1 2 3] [some 2] init2) (fun _ => 3) 3 0 [2] = true := by decide
example : finOK (finSt [.mu 1 2 3] [some 2] init2) (fun _ => 3) 3 0 [1] = false := by decide

end CFSG.KC.BM.Run

end
