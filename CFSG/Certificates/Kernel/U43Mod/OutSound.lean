
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43F3Base
public import Certificates.Data.Kernel.U43Mod.OutDefs
public import CFSG.Certificates.Kernel.U43Mod.InvSound

public section

namespace CFSG.KS.U43Out

open CFSG.KC.Enum CFSG.KC.U43Inv CFSG.KC.U43Out CFSG.KS CFSG.KS.U43Mod CFSG.KS.U43Inv
  CFSG.LieType.Multipliers.U43 CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out

@[expose] def KeyOf4 (r : ℕ) (g : Gp) : Prop :=
  kf r 0 = (g ⟨0, by norm_num⟩ : ℕ) ∧ kf r 1 = (g ⟨1, by norm_num⟩ : ℕ) ∧
    kf r 2 = (g ⟨9, by norm_num⟩ : ℕ) ∧ f4 r = (g ⟨84, by norm_num⟩ : ℕ)

@[expose] noncomputable def sFP (gs : List Gp) (l : ℕ) : Gp :=
  if l % 2 = 0 then gs.getD (l / 2) 1 else (gs.getD (l / 2) 1)⁻¹

theorem mulStepP_eq (gs : List Gp) (g : Gp) (l : ℕ) : mulStepP gs g l = g * sFP gs l := by
  unfold mulStepP sFP
  split_ifs <;> rfl

theorem treeP_induction_of_depth {root : Gp} {step : Gp → ℕ → Gp} {par lab : Array ℕ}
    {nl n : ℕ} {dep : ℕ → ℕ} {Q : ℕ → Gp → Prop} (h0 : Q 0 root)
    (hs : ∀ k < n, k ≠ 0 → par[k]! < n ∧ dep par[k]! < dep k ∧
      ∀ g, Q par[k]! g → Q k (step g (lab[k]! % nl))) :
    ∀ f, ∀ k < n, dep k ≤ f → Q k (treeP root step par lab nl f k) := by
  intro f
  induction f with
  | zero =>
    intro k hk hd
    by_cases hk0 : k = 0
    · rw [hk0]
      exact h0
    · have := (hs k hk hk0).2.1
      omega
  | succ f ih =>
    intro k hk hd
    by_cases hk0 : k = 0
    · rw [hk0]
      exact h0
    · obtain ⟨hp, hdp, hv⟩ := hs k hk hk0
      rw [treeP, if_neg hk0]
      exact hv _ (ih _ hp (by omega))

@[expose] def WalkOfP (R : ℕ → ℕ) (Gr Gk : ℕ → ℕ → ℕ) (k : ℕ) (g : Gp) : Prop :=
  ∀ f, kdep (R k) ≤ f → ∀ q (hq : q < 820), eW R Gr f k q = (g ⟨q, hq⟩ : ℕ) ∧
    eWi R Gk f k q = (g⁻¹ ⟨q, hq⟩ : ℕ)

theorem k4Rec_zero {R : ℕ → ℕ} {Gk : ℕ → ℕ → ℕ} (h : k4Rec R Gk 0 = true) : f4 (R 0) = 84 := by
  unfold k4Rec at h
  rw [strictB_eq] at h
  exact beq_iff.1 h

theorem k4Rec_succ {R : ℕ → ℕ} {Gk : ℕ → ℕ → ℕ} {k : ℕ} (hk : k ≠ 0) (h : k4Rec R Gk k = true) :
    f4 (R k) = Gk (klab (R k)) (f4 (R (kpar (R k)))) := by
  unfold k4Rec at h
  simp only [strictB_eq, beq_false hk, bIf_f] at h
  exact beq_iff.1 h

theorem key_tree4 {R : ℕ → ℕ} {n nl : ℕ} {Gk Gr : ℕ → ℕ → ℕ} {gs : List Gp} {par lab : Array ℕ}
    (hG : ∀ l < nl, ∀ q (hq : q < 820), Gk l q = ((sFP gs l)⁻¹ ⟨q, hq⟩ : ℕ) ∧
      Gr l q = (sFP gs l ⟨q, hq⟩ : ℕ))
    (hn : 0 < n) (hT : kTree R n nl Gk = true) (h4 : k4Tree R n Gk = true)
    (hP : ∀ k < n, par[k]! = kpar (R k)) (hL : ∀ k < n, lab[k]! = klab (R k)) :
    ∀ k < n, KeyOf4 (R k) (treeP 1 (mulStepP gs) par lab nl fuel k)⁻¹ ∧
      WalkOfP R Gr Gk k (treeP 1 (mulStepP gs) par lab nl fuel k) := by
  have hR : ∀ k < n, kRecOK R n nl Gk k = true := allN_spec hT
  have hR4 : ∀ k < n, k4Rec R Gk k = true := allN_spec h4
  obtain ⟨hd0, k0, k1, k2⟩ := kRecOK_zero (hR 0 hn)
  have k3 := k4Rec_zero (hR4 0 hn)
  have h0 : KeyOf4 (R 0) (1 : Gp)⁻¹ ∧ WalkOfP R Gr Gk 0 1 := by
    refine ⟨⟨by rw [k0]; simp, by rw [k1]; simp, by rw [k2]; simp, by rw [k3]; simp⟩,
      fun f _ q hq => ?_⟩
    cases f with
    | zero => exact ⟨rfl, by rw [inv_one]; rfl⟩
    | succ f =>
      rw [eW_succ, eWi_succ, hd0]
      exact ⟨rfl, by rw [inv_one]; rfl⟩
  have hs : ∀ k < n, k ≠ 0 → par[k]! < n ∧ kdep (R par[k]!) < kdep (R k) ∧
      ∀ g, (KeyOf4 (R par[k]!) g⁻¹ ∧ WalkOfP R Gr Gk par[k]! g) →
        KeyOf4 (R k) (mulStepP gs g (lab[k]! % nl))⁻¹ ∧
          WalkOfP R Gr Gk k (mulStepP gs g (lab[k]! % nl)) := by
    intro k hk hk0
    obtain ⟨hp, hl, hdp, -, hks⟩ := kRecOK_succ hk0 (hR k hk)
    have e3 := k4Rec_succ hk0 (hR4 k hk)
    rw [hP k hk, hL k hk, Nat.mod_eq_of_lt hl]
    refine ⟨hp, hdp, fun g ⟨⟨g0, g1, g9, g84⟩, hw⟩ => ?_⟩
    rw [mulStepP_eq]
    obtain ⟨e0, e1, e2⟩ := keys3_spec hks
    have hGk : ∀ (x : Fin 820), Gk (klab (R k)) x = ((sFP gs (klab (R k)))⁻¹ x : ℕ) :=
      fun x => (hG _ hl x x.2).1
    have hmul : ∀ x : Fin 820, ((g * sFP gs (klab (R k)))⁻¹ x : ℕ) =
        ((sFP gs (klab (R k)))⁻¹ (g⁻¹ x) : ℕ) := fun x => by
      rw [mul_inv_rev, Equiv.Perm.mul_apply]
    refine ⟨⟨by rw [e0, g0, hGk, hmul], by rw [e1, g1, hGk, hmul], by rw [e2, g9, hGk, hmul],
      by rw [e3, g84, hGk, hmul]⟩, fun f hf q hq => ?_⟩
    cases f with
    | zero => omega
    | succ f =>
      have hd : kdep (R k) ≠ 0 := by omega
      rw [eW_succ, eWi_succ, beq_false hd]
      dsimp only
      have hq' : (sFP gs (klab (R k)) ⟨q, hq⟩ : ℕ) < 820 := Fin.is_lt _
      obtain ⟨w1, -⟩ := hw f (by omega) _ hq'
      obtain ⟨-, w2⟩ := hw f (by omega) q hq
      refine ⟨?_, ?_⟩
      · rw [(hG _ hl q hq).2, w1, Fin.eta, Equiv.Perm.mul_apply]
      · rw [w2, hGk, ← hmul]
  intro k hk
  refine treeP_induction_of_depth (Q := fun k g => KeyOf4 (R k) g⁻¹ ∧ WalkOfP R Gr Gk k g)
    (dep := fun k => kdep (R k)) h0 hs fuel k hk ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · change kdep (R 0) ≤ 32
    omega
  · have := (kRecOK_succ (by omega) (hR k hk)).2.2.2.1
    change kdep (R k) ≤ 32
    omega

theorem key_clos4 {R : ℕ → ℕ} {n nl : ℕ} {Gk : ℕ → ℕ → ℕ} {e s : ℕ → Gp} {tbl : Array ℕ}
    {Q : Gp → Prop} (hnl : 0 < nl) (hK : ∀ k < n, KeyOf4 (R k) (e k)⁻¹)
    (hG : ∀ l < nl, ∀ q (hq : q < 820), Gk l q = ((s l)⁻¹ ⟨q, hq⟩ : ℕ))
    (hQ : ∀ k < n, Q (e k)) (hQs : ∀ k < n, ∀ l < nl, Q (e k * s l))
    (hsep : ∀ g h : Gp, Q g → Q h → (g⁻¹ ⟨0, by norm_num⟩ : ℕ) = h⁻¹ ⟨0, by norm_num⟩ →
      (g⁻¹ ⟨1, by norm_num⟩ : ℕ) = h⁻¹ ⟨1, by norm_num⟩ →
      (g⁻¹ ⟨9, by norm_num⟩ : ℕ) = h⁻¹ ⟨9, by norm_num⟩ →
      (g⁻¹ ⟨84, by norm_num⟩ : ℕ) = h⁻¹ ⟨84, by norm_num⟩ → g = h)
    (hC : tClos R n nl Gk tbl.toList = true) :
    ∀ k < n, ∀ l < nl, tbl[k * nl + l]! < n ∧ e tbl[k * nl + l]! = e k * s l := by
  intro k hk l hl
  have hi : k * nl + l < Nat.mul n nl := by
    change k * nl + l < n * nl
    nlinarith
  have h := (lwalk_spec hC).2 _ hi
  have h1 : Nat.div (k * nl + l) nl = k := by
    change (k * nl + l) / nl = k
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnl, Nat.div_eq_of_lt hl, Nat.zero_add]
  have h2 : Nat.mod (k * nl + l) nl = l := by
    change (k * nl + l) % nl = l
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  rw [h1, h2, Array.getElem!_toList, bAnd_iff, blt_iff, bAnd_iff, beq_iff] at h
  obtain ⟨hx, hks, h4⟩ := h
  refine ⟨hx, ?_⟩
  obtain ⟨e0, e1, e2⟩ := keys3_spec hks
  obtain ⟨k0, k1, k9, k84⟩ := hK k hk
  obtain ⟨x0, x1, x9, x84⟩ := hK _ hx
  have hmul : ∀ x : Fin 820, ((e k * s l)⁻¹ x : ℕ) = Gk l ((e k)⁻¹ x : ℕ) := fun x => by
    rw [hG l hl _ (Fin.is_lt _), mul_inv_rev, Equiv.Perm.mul_apply]
  exact hsep _ _ (hQ _ hx) (hQs k hk l hl) (by rw [← x0, e0, k0, hmul])
    (by rw [← x1, e1, k1, hmul]) (by rw [← x9, e2, k9, hmul]) (by rw [← x84, h4, k84, hmul])

theorem key_inj4 {R O : ℕ → ℕ} {n : ℕ} {e : ℕ → Gp} (hn : 2 ≤ n)
    (hK : ∀ k < n, KeyOf4 (R k) (e k)⁻¹) (hO : kOrd R n O = true) {i j : ℕ} (hi : i < n)
    (hj : j < n) (h0 : ((e i)⁻¹ ⟨0, by norm_num⟩ : ℕ) = (e j)⁻¹ ⟨0, by norm_num⟩)
    (h1 : ((e i)⁻¹ ⟨1, by norm_num⟩ : ℕ) = (e j)⁻¹ ⟨1, by norm_num⟩)
    (h9 : ((e i)⁻¹ ⟨9, by norm_num⟩ : ℕ) = (e j)⁻¹ ⟨9, by norm_num⟩) : i = j := by
  refine oOrd_inj hn hO i hi j hj ?_
  obtain ⟨a0, a1, a9, -⟩ := hK i hi
  obtain ⟨b0, b1, b9, -⟩ := hK j hj
  exact kkey_eq (by rw [a0, b0, h0]) (by rw [a1, b1, h1]) (by rw [a9, b9, h9])

theorem bNot_true {b : Bool} (h : bNot b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem orbOK_spec {f : ℕ → ℕ} {q : ℕ} :
    ∀ (n p : ℕ), orbOK f q n p = true → ∀ e < n, f^[e + 1] p ≠ q
  | 0, _, _ => fun e he => absurd he (Nat.not_lt_zero _)
  | n + 1, p, h => by
    have h' : strictB (f p) (fun p' => bAnd(bNot (Nat.beq p' q), orbOK f q n p')) = true := h
    rw [strictB_eq, bAnd_iff] at h'
    obtain ⟨h1, h2⟩ := h'
    have h1' := bNot_true h1
    intro e he
    cases e with
    | zero =>
      intro hfq
      rw [Function.iterate_one] at hfq
      rw [beq_iff.2 hfq] at h1'
      exact Bool.noConfusion h1'
    | succ e =>
      rw [Function.iterate_succ_apply]
      exact orbOK_spec n (f p) h2 e (by omega)

theorem pwv_mem {Lp : ℕ → ℕ → ℕ}
    (hLp : ∀ l < 4, ∀ q (hq : q < 820), Lp l q = (psi (letElt l) ⟨q, hq⟩ : ℕ)) (W : ℕ) :
    ∀ len, ∃ x : X₀, ∀ q (hq : q < 820), pwv Lp W len q = (psi x ⟨q, hq⟩ : ℕ)
  | 0 => ⟨1, fun q hq => by simp [pwv]⟩
  | len + 1 => by
    obtain ⟨x, hx⟩ := pwv_mem hLp W len
    have hl : fld(W, Nat.shiftLeft len (nat_lit 1), nat_lit 3) < 4 :=
      Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
    refine ⟨x * letElt (fld(W, Nat.shiftLeft len (nat_lit 1), nat_lit 3)), fun q hq => ?_⟩
    change pwv Lp W len (Lp (fld(W, Nat.shiftLeft len (nat_lit 1), nat_lit 3)) q) = _
    rw [hLp _ hl q hq, hx _ (Fin.is_lt _), Fin.eta, map_mul, Equiv.Perm.mul_apply]

theorem wordP_cons (l : ℕ) (w : List ℕ) : wordP (l :: w) = letP l * wordP w := by
  have key : ∀ (w : List ℕ) (h : Gp), w.foldl (fun g l => g * letP l) h =
      h * w.foldl (fun g l => g * letP l) 1 := by
    intro w
    induction w with
    | nil => intro h; simp
    | cons l w ih =>
      intro h
      rw [List.foldl_cons, List.foldl_cons, ih (h * letP l), ih (1 * letP l)]
      group
  unfold wordP
  rw [List.foldl_cons, key, one_mul]

theorem mwvP_eq {Lp : ℕ → ℕ → ℕ}
    (hLp : ∀ l q (hq : q < 820), Lp l q = (letP l ⟨q, hq⟩ : ℕ)) :
    ∀ (w : List ℕ) q (hq : q < 820), mwv Lp w q = (wordP w ⟨q, hq⟩ : ℕ)
  | [], q, hq => by simp [mwv, wordP]
  | l :: w, q, hq => by
    change Lp l (mwv Lp w q) = _
    rw [mwvP_eq hLp w q hq, hLp l _ (Fin.is_lt _), Fin.eta, wordP_cons, Equiv.Perm.mul_apply]

end CFSG.KS.U43Out

end
