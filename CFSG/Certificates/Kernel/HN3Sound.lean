module

public import Certificates.Data.Kernel.HN3K
public import CFSG.Certificates.Kernel.HNF26729Sound
public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.KS.HN3

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HN3 CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KS.HNF26720
  CFSG.KS.HNF26729 CFSG.KS.HNLocal CFSG.KC.LQT.SecS CFSG.Sporadic.GLQ Matrix

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem forceLB_eq : ∀ (l : List Nat) (k : List Nat → Bool), forceLB l k = k l
  | [], _ => rfl
  | x :: l, k => by
    change strictB x (fun a => forceLB l fun t => k (a :: t)) = _
    rw [CFSG.KS.HNF26720.strictB_eq]
    exact forceLB_eq l fun t => k (x :: t)

theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, i + 1 => by
    change getN d l i = _
    rw [getN_eq d l i, List.getD_cons_succ]

theorem getL_eq : ∀ (l : List (List Nat)) (i : Nat), getL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, i + 1 => by
    change getL l i = _
    rw [getL_eq l i, List.getD_cons_succ]

theorem setN_eq : ∀ (l : List Nat) (i x : Nat), setN l i x = l.set i x
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | m :: t, i + 1, x => by
    change m :: setN t i x = _
    rw [setN_eq t i x]
    rfl

theorem headN_eq (l : List Nat) : headN l = l.getD 0 0 := by
  cases l <;> rfl

theorem tailN_getD (l : List Nat) (j : Nat) : (tailN l).getD j 0 = l.getD (j + 1) 0 := by
  cases l with
  | nil => rfl
  | cons x t => rfl

theorem getD_set {l : List Nat} {i : Nat} (hi : i < l.length) (x d j : Nat) :
    (l.set i x).getD j d = if j = i then x else l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h
    simp [hi]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem regM_setR {R : List Nat} {k x y : Nat} (hk : 2 * k + 1 < R.length) (r : Nat) :
    regM (setR R k x y) r = if r = k then x else regM R r := by
  unfold regM setR
  simp only [Nat.mul_eq, Nat.add_eq]
  rw [setN_eq, setN_eq, getN_eq, getN_eq, getD_set (by rw [List.length_set]; omega),
    getD_set (by omega)]
  split_ifs <;> first | rfl | omega

theorem regI_setR {R : List Nat} {k x y : Nat} (hk : 2 * k + 1 < R.length) (r : Nat) :
    regI (setR R k x y) r = if r = k then y else regI R r := by
  unfold regI setR
  simp only [Nat.mul_eq, Nat.add_eq]
  rw [setN_eq, setN_eq, getN_eq, getN_eq, getD_set (by rw [List.length_set]; omega),
    getD_set (by omega)]
  split_ifs <;> first | rfl | omega

theorem length_setR (R : List Nat) (k x y : Nat) : (setR R k x y).length = R.length := by
  unfold setR
  rw [setN_eq, setN_eq, List.length_set, List.length_set]

@[expose] def codeHN3 : Instr → List Nat
  | .mu i j k => [0, i, j, k]
  | .iv i k => [1, i, k]
  | .pwr e i k => [2, e, i, k]

@[expose] def isPwr : Instr → Bool
  | .pwr _ _ _ => true
  | _ => false

section Sound

variable {L H CM RM ONE LV HV : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem wordG_sound {G : List Nat} :
    ∀ (w : List Nat), (∀ c ∈ w, Canon 5 133 13 (getN 0 G c)) → ∀ (acc : Nat), Canon 5 133 13 acc →
      Canon 5 133 13 (wordG (mulR 5 13 1729 133 9 L H CM RM) G w acc) ∧
        OM (wordG (mulR 5 13 1729 133 9 L H CM RM) G w acc) =
          OM acc * (w.map fun c => OM (getN 0 G c)).prod
  | [], _, acc, h => ⟨h, by rw [List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | c :: w, hw, acc, h => by
    obtain ⟨h1, h2⟩ := mul_sound hc h (hw c List.mem_cons_self)
    have e : wordG (mulR 5 13 1729 133 9 L H CM RM) G (c :: w) acc =
        wordG (mulR 5 13 1729 133 9 L H CM RM) G w
          (mulR 5 13 1729 133 9 L H CM RM acc (getN 0 G c)) :=
      CFSG.KS.HNF26720.strictN_eq _ _
    obtain ⟨h3, h4⟩ := wordG_sound w (fun x hx => hw x (List.mem_cons_of_mem c hx)) _ h1
    rw [e]
    exact ⟨h3, by rw [h4, h2, List.map_cons, List.prod_cons, mul_assoc]⟩

theorem wordG_one {G : List Nat} {w : List Nat} (hw : ∀ c ∈ w, Canon 5 133 13 (getN 0 G c)) :
    Canon 5 133 13 (wordG (mulR 5 13 1729 133 9 L H CM RM) G w ONE) ∧
      OM (wordG (mulR 5 13 1729 133 9 L H CM RM) G w ONE) =
        (w.map fun c => OM (getN 0 G c)).prod := by
  obtain ⟨c1, e1⟩ := one_sound hc
  obtain ⟨h1, h2⟩ := wordG_sound hc w hw ONE c1
  refine ⟨h1, ?_⟩
  rw [h2]
  change ordMat 5 133 13 1729 ONE * _ = _
  rw [e1, one_mul]

theorem relsK_sound {G : List Nat} {rels : List (List Nat)}
    (hG : ∀ r ∈ rels, ∀ c ∈ r, Canon 5 133 13 (getN 0 G c))
    (h : relsK (mulR 5 13 1729 133 9 L H CM RM) G ONE rels = true) :
    ∀ r ∈ rels, (r.map fun c => OM (getN 0 G c)).prod = 1 := by
  induction rels with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons r0 rels ih =>
    obtain ⟨h1, h2⟩ := andB_true h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · obtain ⟨-, e⟩ := wordG_one hc (hG r List.mem_cons_self)
      rw [← e, Nat.eq_of_beq_eq_true h1]
      exact (one_sound hc).2
    · exact ih (fun r' hr' => hG r' (List.mem_cons_of_mem _ hr')) h2 r hr

variable {Γ : Type*} [Group Γ] (ρ : Γ →* Matrix (Fin 133) (Fin 133) (ZMod 5))

@[expose] def RegOK (R : List Nat) (Rg : ℕ → Γ) : Prop :=
  R.length = 28 ∧ ∀ r < 14, Canon 5 133 13 (regM R r) ∧ Canon 5 133 13 (regI R r) ∧
    OM (regM R r) = ρ (Rg r) ∧ OM (regI R r) = ρ (Rg r)⁻¹

omit hc in
theorem stepM_mu (mul : Nat → Nat → Nat) (R : List Nat) (i j k : Nat) :
    stepM mul R (codeHN3 (.mu i j k)) =
      setR R k (mul (regM R i) (regM R j)) (mul (regI R j) (regI R i)) := rfl

omit hc in
theorem stepM_iv (mul : Nat → Nat → Nat) (R : List Nat) (i k : Nat) :
    stepM mul R (codeHN3 (.iv i k)) = setR R k (regI R i) (regM R i) := rfl

theorem step_ok {R : List Nat} {Rg : ℕ → Γ} (hR : RegOK ρ R Rg) (ins : Instr)
    (hlt : ins.lt 14 = true) (hp : isPwr ins = false) :
    RegOK ρ (stepM (mulR 5 13 1729 133 9 L H CM RM) R (codeHN3 ins)) (ins.run Rg) := by
  obtain ⟨hl, hr⟩ := hR
  cases ins with
  | mu i j k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨⟨hi, hj⟩, hk⟩ := hlt
    rw [stepM_mu]
    have hk' : 2 * k + 1 < R.length := by omega
    obtain ⟨ci, ci', ei, ei'⟩ := hr i hi
    obtain ⟨cj, cj', ej, ej'⟩ := hr j hj
    obtain ⟨c1, e1⟩ := mul_sound hc ci cj
    obtain ⟨c2, e2⟩ := mul_sound hc cj' ci'
    refine ⟨by rw [length_setR, hl], fun r hr' => ?_⟩
    rw [regM_setR hk', regI_setR hk']
    change _ ∧ _ ∧ _ = ρ (Function.update Rg k (Rg i * Rg j) r) ∧
      _ = ρ (Function.update Rg k (Rg i * Rg j) r)⁻¹
    rw [Function.update_apply]
    by_cases h : r = k
    · rw [if_pos h, if_pos h, if_pos h]
      refine ⟨c1, c2, ?_, ?_⟩
      · rw [e1, ei, ej, map_mul]
      · rw [e2, ei', ej', _root_.mul_inv_rev, map_mul]
    · rw [if_neg h, if_neg h, if_neg h]
      exact hr r hr'
  | iv i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨hi, hk⟩ := hlt
    rw [stepM_iv]
    have hk' : 2 * k + 1 < R.length := by omega
    obtain ⟨ci, ci', ei, ei'⟩ := hr i hi
    refine ⟨by rw [length_setR, hl], fun r hr' => ?_⟩
    rw [regM_setR hk', regI_setR hk']
    change _ ∧ _ ∧ _ = ρ (Function.update Rg k (Rg i)⁻¹ r) ∧
      _ = ρ (Function.update Rg k (Rg i)⁻¹ r)⁻¹
    rw [Function.update_apply]
    by_cases h : r = k
    · rw [if_pos h, if_pos h, if_pos h]
      exact ⟨ci', ci, ei', by rw [inv_inv, ei]⟩
    · rw [if_neg h, if_neg h, if_neg h]
      exact hr r hr'
  | pwr e i k => exact absurd hp (by simp [isPwr])

theorem runM_sound :
    ∀ (prog : List Instr) (R : List Nat) (Rg : ℕ → Γ) (k : List Nat → Bool),
      prog.all (Instr.lt 14) = true → prog.all (fun ins => !isPwr ins) = true → RegOK ρ R Rg →
      runM (mulR 5 13 1729 133 9 L H CM RM) (prog.map codeHN3) R k = true →
      ∃ R', RegOK ρ R' (runProg Rg prog) ∧ k R' = true
  | [], R, Rg, k, _, _, hR, h => ⟨R, hR, h⟩
  | ins :: prog, R, Rg, k, hlt, hp, hR, h => by
    have e : runM (mulR 5 13 1729 133 9 L H CM RM) ((ins :: prog).map codeHN3) R k =
        runM (mulR 5 13 1729 133 9 L H CM RM) (prog.map codeHN3)
          (stepM (mulR 5 13 1729 133 9 L H CM RM) R (codeHN3 ins)) k := by
      change forceLB (stepM (mulR 5 13 1729 133 9 L H CM RM) R (codeHN3 ins))
        (fun R' => runM (mulR 5 13 1729 133 9 L H CM RM) (prog.map codeHN3) R' k) = _
      rw [forceLB_eq]
    rw [e] at h
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hlt hp
    exact runM_sound prog _ (ins.run Rg) k hlt.2 hp.2 (step_ok hc ρ hR ins hlt.1 hp.1) h

omit hc in
theorem inv_of_mul {x : Γ} {M : Matrix (Fin 133) (Fin 133) (ZMod 5)} (h : ρ x * M = 1) :
    ρ x⁻¹ = M := by
  calc ρ x⁻¹ = ρ x⁻¹ * (ρ x * M) := by rw [h, mul_one]
    _ = M := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem progK_sound {A B : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B) {a b : Γ}
    (ea : ρ a = OM A) (eb : ρ b = OM B) {prog : List Instr} {regs : List Nat}
    (hlt : prog.all (Instr.lt 14) = true) (hp : prog.all (fun ins => !isPwr ins) = true)
    (h : progK (mulR 5 13 1729 133 9 L H CM RM) A B ONE (prog.map codeHN3) regs = true) :
    ∀ t < 3, Canon 5 133 13 (getN 0 regs (2 * t)) ∧ Canon 5 133 13 (getN 0 regs (2 * t + 1)) ∧
      OM (getN 0 regs (2 * t)) = ρ (runProg (initRegs a b) prog (11 + t)) ∧
      OM (getN 0 regs (2 * t + 1)) = ρ (runProg (initRegs a b) prog (11 + t))⁻¹ := by
  unfold progK at h
  rw [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨hAA, h⟩ := andB_true h
  obtain ⟨hBB, h⟩ := andB_true h
  obtain ⟨c1, e1⟩ := one_sound hc
  obtain ⟨cBi, eBi⟩ := mul_sound hc cB cB
  set Bi := mulR 5 13 1729 133 9 L H CM RM B B with hBi
  have eA2 : OM A * OM A = 1 := by
    rw [← (mul_sound hc cA cA).2, Nat.eq_of_beq_eq_true hAA]
    exact e1
  have eB3 : OM B * OM Bi = 1 := by
    rw [← (mul_sound hc cB cBi).2, Nat.eq_of_beq_eq_true hBB]
    exact e1
  have ia : ρ a⁻¹ = OM A := inv_of_mul ρ (by rw [ea, eA2])
  have ib : ρ b⁻¹ = OM Bi := inv_of_mul ρ (by rw [eb, eB3])
  have h0 : RegOK ρ (initM ONE A B Bi) (initRegs a b) := by
    refine ⟨rfl, fun r hr => ?_⟩
    have one_ok : Canon 5 133 13 ONE ∧ Canon 5 133 13 ONE ∧ OM ONE = ρ 1 ∧ OM ONE = ρ 1⁻¹ :=
      ⟨c1, c1, by rw [map_one]; exact e1, by rw [inv_one, map_one]; exact e1⟩
    interval_cases r
    · exact one_ok
    · exact ⟨cA, cA, ea.symm, ia.symm⟩
    · exact ⟨cB, cBi, eb.symm, ib.symm⟩
    all_goals exact one_ok
  obtain ⟨R, ⟨-, hR⟩, hk⟩ := runM_sound hc ρ prog _ _ _ hlt hp h0 h
  obtain ⟨h22, hk⟩ := andB_true hk
  obtain ⟨h23, hk⟩ := andB_true hk
  obtain ⟨h24, hk⟩ := andB_true hk
  obtain ⟨h25, hk⟩ := andB_true hk
  obtain ⟨h26, h27⟩ := andB_true hk
  intro t ht
  have key : ∀ r, r < 14 → ∀ x y, getN 0 R (2 * r) = x → getN 0 R (2 * r + 1) = y →
      Canon 5 133 13 x ∧ Canon 5 133 13 y ∧ OM x = ρ (runProg (initRegs a b) prog r) ∧
        OM y = ρ (runProg (initRegs a b) prog r)⁻¹ := by
    intro r hr x y hx hy
    obtain ⟨q1, q2, q3, q4⟩ := hR r hr
    have ex : regM R r = x := hx
    have ey : regI R r = y := hy
    rw [ex] at q1 q3
    rw [ey] at q2 q4
    exact ⟨q1, q2, q3, q4⟩
  interval_cases t
  · exact key 11 (by norm_num) _ _ (Nat.eq_of_beq_eq_true h22) (Nat.eq_of_beq_eq_true h23)
  · exact key 12 (by norm_num) _ _ (Nat.eq_of_beq_eq_true h24) (Nat.eq_of_beq_eq_true h25)
  · exact key 13 (by norm_num) _ _ (Nat.eq_of_beq_eq_true h26) (Nat.eq_of_beq_eq_true h27)

end Sound

end CFSG.KS.HN3

end
