module

public import Certificates.Data.Kernel.T75M23.L2K7F
public import CFSG.Certificates.Kernel.T75JM.L2KFSound
public import CFSG.Certificates.Kernel.T75M23.L2K7Sound

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable
open CFSG.KC.N0K (S4 NormS allZ allZ_spec code_div code_mod conj_eq_iff conj_inv_iff)

variable {L : Int → Nat} (hL : LetterRd L) (h1 : n7InvCheck = true) (h2 : n7RelCheck = true)
  (hok : n7kOk L = true)

def Rp (g : N7) (P : Nat) : Prop := ∀ x < 23, idx 23 (phiK h1 h2 g) x = fd 5 P x

include hL in
theorem rp_pw (w : List (Fin 6 × Bool)) : Rp h1 h2 (n7 w) (pw L w) :=
  fun _ hx => idxK_pw hL w hx

include hL in
theorem rp_elem (a : Nat) {k : Nat} (hk : k < 16) :
    Rp h1 h2 (n7 (a7W a ++ tw7 k)) (pc (ak L a) (tk L k)) := fun x hx => by
  rw [idxK_elem hL a hk hx, fd_pc _ _ hx]

include hL in
theorem rp_tk {l : Nat} (hl : l < 16) : Rp h1 h2 (n7 (tw7 l)) (tk L l) := fun _ hx => by
  rw [phiK_n7]
  exact idx_tk h1 hL hl hx

theorem rp_one : Rp h1 h2 1 idn := fun x hx => by
  rw [map_one, idx_one, hid x hx]

theorem rp_mul {g h : N7} {P Q : Nat} (hg : Rp h1 h2 g P) (hh : Rp h1 h2 h Q) :
    Rp h1 h2 (g * h) (pc P Q) := fun x hx => by
  have hb : fd 5 Q x < 23 := hh x hx ▸ idx_lt _ hx
  rw [map_mul, idx_mul, hh x hx, hg _ hb, fd_pc _ _ hx]

include hL hok in
theorem eqP_iff {g h : N7} {P Q : Nat} (hg : Rp h1 h2 g P)
    (hh : Rp h1 h2 h Q) : eqP P Q = true ↔ g = h := by
  constructor
  · intro e
    refine phiK_injective hL h1 h2 hok (eq_of_idx fun x hx => ?_)
    rw [hg x hx, hh x hx]
    have := List.all_eq_true.1 e x (List.mem_range.2 hx)
    rw [fdN_eq, fdN_eq] at this
    exact Nat.eq_of_beq_eq_true this
  · rintro rfl
    refine List.all_eq_true.2 fun x hx => ?_
    have hx' := List.mem_range.1 hx
    rw [fdN_eq, fdN_eq, ← hg x hx', ← hh x hx']
    exact Nat.beq_refl _

include hL hok in
theorem conjAt_iff {b l : Nat} (hl : l < 16) {g y : N7}
    {P Y : Nat} (hg : Rp h1 h2 g P) (hy : Rp h1 h2 y Y) :
    conjAt (ak L b) (tk L l) P Y = true ↔
      n7 (a7W b ++ tw7 l) * g = y * n7 (a7W b ++ tw7 l) := by
  have hn := rp_elem hL h1 h2 b hl
  have e1 := eqP_iff hL h1 h2 hok (rp_mul h1 h2 hn hg) (rp_mul h1 h2 hy hn)
  have key : ∀ x ∈ List.range 23,
      Nat.beq (fdN 5 (ak L b) (fdN 5 (tk L l) (fdN 5 P x)))
          (fdN 5 Y (fdN 5 (ak L b) (fdN 5 (tk L l) x))) =
        Nat.beq (fdN 5 (pc (pc (ak L b) (tk L l)) P) x)
          (fdN 5 (pc Y (pc (ak L b) (tk L l))) x) := by
    intro x hx
    have hx' := List.mem_range.1 hx
    have hP : fd 5 P x < 23 := hg x hx' ▸ idx_lt _ hx'
    simp only [fdN_eq, fd_pc _ _ hx', fd_pc _ _ hP]
  rw [← e1]
  unfold conjAt eqP
  rw [List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun x hx => by rw [key x hx]

include hL hok in
theorem comAll_iff {b l : Nat} (hl : l < 16) {g : N7} {P : Nat}
    (hg : Rp h1 h2 g P) :
    comAll (ak L b) (tk L l) P = true ↔ n7 (a7W b ++ tw7 l) * g = g * n7 (a7W b ++ tw7 l) := by
  rw [← conjAt_iff hL h1 h2 hok hl hg hg]
  rfl

include hL hok in
theorem inSAt_iff {b l : Nat} (hl : l < 16)
    {v s1 s2 s3 s4 : N7} {P Y1 Y2 Y3 Y4 : Nat} (hv : Rp h1 h2 v P) (r1 : Rp h1 h2 s1 Y1)
    (r2 : Rp h1 h2 s2 Y2) (r3 : Rp h1 h2 s3 Y3) (r4 : Rp h1 h2 s4 Y4) :
    inSAt (ak L b) (tk L l) P [Y1, Y2, Y3, Y4] = true ↔
      (n7 (a7W b ++ tw7 l) * v * (n7 (a7W b ++ tw7 l))⁻¹ = s1 ∨
        n7 (a7W b ++ tw7 l) * v * (n7 (a7W b ++ tw7 l))⁻¹ = s2 ∨
        n7 (a7W b ++ tw7 l) * v * (n7 (a7W b ++ tw7 l))⁻¹ = s3 ∨
        n7 (a7W b ++ tw7 l) * v * (n7 (a7W b ++ tw7 l))⁻¹ = s4) := by
  unfold inSAt
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    conjAt_iff hL h1 h2 hok hl hv r1, conjAt_iff hL h1 h2 hok hl hv r2,
    conjAt_iff hL h1 h2 hok hl hv r3, conjAt_iff hL h1 h2 hok hl hv r4, conj_eq_iff]

include hL hok in
theorem inSAtI_iff {b l : Nat} (hl : l < 16)
    {v s1 s2 s3 s4 : N7} {P Y1 Y2 Y3 Y4 : Nat} (hv : Rp h1 h2 v P) (r1 : Rp h1 h2 s1 Y1)
    (r2 : Rp h1 h2 s2 Y2) (r3 : Rp h1 h2 s3 Y3) (r4 : Rp h1 h2 s4 Y4) :
    inSAtI (ak L b) (tk L l) P [Y1, Y2, Y3, Y4] = true ↔
      ((n7 (a7W b ++ tw7 l))⁻¹ * v * n7 (a7W b ++ tw7 l) = s1 ∨
        (n7 (a7W b ++ tw7 l))⁻¹ * v * n7 (a7W b ++ tw7 l) = s2 ∨
        (n7 (a7W b ++ tw7 l))⁻¹ * v * n7 (a7W b ++ tw7 l) = s3 ∨
        (n7 (a7W b ++ tw7 l))⁻¹ * v * n7 (a7W b ++ tw7 l) = s4) := by
  unfold inSAtI
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    conjAt_iff hL h1 h2 hok hl r1 hv, conjAt_iff hL h1 h2 hok hl r2 hv,
    conjAt_iff hL h1 h2 hok hl r3 hv, conjAt_iff hL h1 h2 hok hl r4 hv, conj_inv_iff]

include hL hok in
theorem anyEq_iff {v s1 s2 s3 s4 : N7} {P Y1 Y2 Y3 Y4 : Nat}
    (hv : Rp h1 h2 v P) (r1 : Rp h1 h2 s1 Y1) (r2 : Rp h1 h2 s2 Y2) (r3 : Rp h1 h2 s3 Y3)
    (r4 : Rp h1 h2 s4 Y4) :
    ([Y1, Y2, Y3, Y4].any fun Y => eqP P Y) = true ↔ (v = s1 ∨ v = s2 ∨ v = s3 ∨ v = s4) := by
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    eqP_iff hL h1 h2 hok hv r1, eqP_iff hL h1 h2 hok hv r2, eqP_iff hL h1 h2 hok hv r3,
    eqP_iff hL h1 h2 hok hv r4]

include hL hok in
theorem inTP_iff {v : N7} {P : Nat} (hv : Rp h1 h2 v P) :
    inTP L P = true ↔ ∃ l < 16, v = n7 (tw7 l) := by
  unfold inTP
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, e⟩
    have hl' := List.mem_range.1 hl
    exact ⟨l, hl', (eqP_iff hL h1 h2 hok hv (rp_tk hL h1 h2 hl')).1 e⟩
  · rintro ⟨l, hl, e⟩
    exact ⟨l, List.mem_range.2 hl, (eqP_iff hL h1 h2 hok hv (rp_tk hL h1 h2 hl)).2 e⟩

include hL h1 h2 in
theorem invAt_of (a : Nat) {k : Nat} (hk : k < 16)
    (hsq : n7 (a7W a ++ tw7 k) * n7 (a7W a ++ tw7 k) = 1) : invAt (ak L a) (tk L k) = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  have hx' := List.mem_range.1 hx
  have e := congrArg (fun g => idx 23 (phiK h1 h2 g) x) hsq
  simp only [map_mul, idx_mul, map_one, idx_one] at e
  rw [idxK_elem hL a hk (idx_lt _ hx'), idxK_elem hL a hk hx'] at e
  rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq, e]
  exact Nat.beq_refl _

theorem rp_evP3 {u : Fin 3 → N7} {U0 U1 U2 : Nat} (r0 : Rp h1 h2 (u 0) U0)
    (r1 : Rp h1 h2 (u 1) U1) (r2 : Rp h1 h2 (u 2) U2) (w : List (Fin 3)) :
    Rp h1 h2 (w.map u).prod (evP3 U0 U1 U2 w) := by
  have key : ∀ (w : List (Fin 3)) (acc : Nat) (g : N7), Rp h1 h2 g acc →
      Rp h1 h2 (g * (w.map u).prod)
        (w.foldl (fun acc i => pc acc (if i = 0 then U0 else if i = 1 then U1 else U2)) acc) := by
    intro w
    induction w with
    | nil => intro acc g h; simpa using h
    | cons i w ih =>
      intro acc g h
      have hi : Rp h1 h2 (u i) (if i = 0 then U0 else if i = 1 then U1 else U2) := by
        fin_cases i
        · exact r0
        · exact r1
        · exact r2
      have := ih _ _ (rp_mul h1 h2 h hi)
      simpa [mul_assoc] using this
  simpa [evP3] using key w idn 1 (rp_one h1 h2)

theorem idx_evX {u : Fin 3 → N7} {U0 U1 U2 : Nat} (r0 : Rp h1 h2 (u 0) U0)
    (r1 : Rp h1 h2 (u 1) U1) (r2 : Rp h1 h2 (u 2) U2) :
    ∀ (w : List (Fin 3)) {x : Nat}, x < 23 →
      idx 23 (phiK h1 h2 (w.map u).prod) x = evX U0 U1 U2 w x
  | [], x, _ => by rw [List.map_nil, List.prod_nil, map_one, idx_one]; rfl
  | i :: w, x, hx => by
    have ih := idx_evX r0 r1 r2 w hx
    have hlt : evX U0 U1 U2 w x < 23 := ih ▸ idx_lt _ hx
    have hi : Rp h1 h2 (u i) (if i = 0 then U0 else if i = 1 then U1 else U2) := by
      fin_cases i
      · exact r0
      · exact r1
      · exact r2
    rw [List.map_cons, List.prod_cons, map_mul, idx_mul, ih, hi _ hlt]
    rfl

theorem relAt_of {u : Fin 3 → N7} {U0 U1 U2 : Nat} (r0 : Rp h1 h2 (u 0) U0)
    (r1 : Rp h1 h2 (u 1) U1) (r2 : Rp h1 h2 (u 2) U2) {w : List (Fin 3)}
    (h : (w.map u).prod = 1) : relAt U0 U1 U2 w = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  have hx' := List.mem_range.1 hx
  rw [← idx_evX h1 h2 r0 r1 r2 w hx', h, map_one, idx_one]
  exact Nat.beq_refl _

theorem idx_evL {gs : List N7} {Ps : List Nat} (h : List.Forall₂ (Rp h1 h2) gs Ps) {x : Nat}
    (hx : x < 23) : idx 23 (phiK h1 h2 gs.prod) x = evL Ps x := by
  induction h with
  | nil => rw [List.prod_nil, map_one, idx_one]; rfl
  | @cons g P gs Ps hg _ ih =>
    have hlt : evL Ps x < 23 := ih ▸ idx_lt _ hx
    rw [List.prod_cons, map_mul, idx_mul, ih, hg _ hlt]
    rfl

theorem pts23_eq : pts23 = List.range 23 := by decide

theorem memL_of {gs : List N7} {Ps : List Nat} (h : List.Forall₂ (Rp h1 h2) gs Ps) {g : N7}
    {Y : Nat} (r : Rp h1 h2 g Y) {Ys : List Nat} (hY : Y ∈ Ys) (e : gs.prod = g) :
    memL Ps Ys = true := by
  unfold memL
  refine List.any_eq_true.2 ⟨Y, hY, ?_⟩
  rw [pts23_eq]
  refine List.all_eq_true.2 fun x hx => ?_
  have hx' := List.mem_range.1 hx
  rw [← idx_evL h1 h2 h hx', e, fdN_eq, ← r x hx']
  exact Nat.beq_refl _

theorem dRels7_eq : dRels7 = [0, 1, 0, 1, 0, 1] :: relsT7 := rfl

theorem mem_take_or_drop {l : List Nat} {c : Nat} (h : c ∈ l) (n : Nat) :
    c ∈ l.take n ∨ c ∈ l.drop n :=
  List.mem_append.1 (by rw [List.take_append_drop]; exact h)

theorem zipAll_spec {β : Type} {d : β} {g : Nat → β → Bool} :
    ∀ {l : List Nat} {rs : List β}, zipAll d g l rs = true → ∀ c ∈ l, ∃ r, g c r = true
  | [], _, _, c, hc => absurd hc (by simp)
  | c' :: l, [], h, c, hc => by
    have e : zipAll d g (c' :: l) [] = (g c' d && zipAll d g l []) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨_, h.1⟩
    · exact zipAll_spec h.2 c hc
  | c' :: l, r :: rs, h, c, hc => by
    have e : zipAll d g (c' :: l) (r :: rs) = (g c' r && zipAll d g l rs) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨_, h.1⟩
    · exact zipAll_spec h.2 c hc

theorem forceL_eq (f : Nat → Nat) :
    ∀ (l : List Nat) (k : List Nat → Bool), forceL f l k = k (l.map f)
  | [], _ => rfl
  | c :: l, k => by
    have e : forceL f (c :: l) k = strictB (f c) fun P => forceL f l fun Ps => k (P :: Ps) := rfl
    rw [e, sB_eq, forceL_eq f l]
    rfl

include hL h1 h2 hok in
theorem swap7_of {s2 s3 : List Nat} {P : Nat → Prop}
    (hpass : swPassK L s2 s3 = true)
    (hrows : ∀ c ∈ s2, P c → ∃ (r2 : List Nat) (sw : List (List (List Nat))), c ∈ r2 ∧
      swRowsK L s2 s3 r2 sw = true) (u : Fin 3 → N7)
    (hP : ∀ a < 2520, ∀ k < 16, u 0 = n7 (a7W a ++ tw7 k) → P (16 * a + k))
    (hD : ∀ i, NormS (n7 (bGen7 0)) (n7 (bGen7 1)) (u i))
    (q0 : (([0, 0] : List (Fin 3)).map u).prod = 1)
    (q1 : (([1, 1] : List (Fin 3)).map u).prod = 1)
    (q2 : (([2, 2, 2] : List (Fin 3)).map u).prod = 1)
    (hR : ∀ w ∈ dRels7, (w.map u).prod = 1)
    (hA : ∀ w ∈ aWords7, S4 (n7 (bGen7 0)) (n7 (bGen7 1)) (w.map u).prod ∧ (w.map u).prod ≠ 1)
    (hB : ∀ w ∈ bWords7, (∃ k < 16, (w.map u).prod = n7 (tw7 k)) ∧ (w.map u).prod ≠ 1) :
    ∃ j : N7, NormS (n7 (bGen7 0)) (n7 (bGen7 1)) j ∧
      ∃ k : Fin 2, ∀ i : Fin 3, j * u i * j⁻¹ = n7 (thetaW7 k i) := by
  unfold swPassK at hpass
  rw [withL_eq] at hpass
  simp only [sB_eq] at hpass
  unfold swPass7 at hpass
  have rB0 := rp_pw hL h1 h2 (bGen7 0)
  have rB1 := rp_pw hL h1 h2 (bGen7 1)
  have rB01 : Rp h1 h2 (n7 (bGen7 0) * n7 (bGen7 1)) (pw L (bGen7 0 ++ bGen7 1)) := by
    rw [← n7_append]
    exact rp_pw hL h1 h2 _
  have r1' := rp_one h1 h2
  have hcode : ∀ i : Fin 3, ∃ a < 2520, ∃ k < 16, Rp h1 h2 (u i) (pc (ak L a) (tk L k)) ∧
      u i = n7 (a7W a ++ tw7 k) ∧
      (inDS (ak L a) (tk L k) (pw L (bGen7 0)) (pw L (bGen7 1))
        [idn, pw L (bGen7 0), pw L (bGen7 1), pw L (bGen7 0 ++ bGen7 1)] = true) := by
    intro i
    obtain ⟨a, ha, k, hk, e⟩ := n7K_surj hL h1 h2 hok (u i)
    refine ⟨a, ha, k, hk, by rw [e]; exact rp_elem hL h1 h2 a hk, e, ?_⟩
    unfold inDS
    rw [Bool.and_eq_true, inSAt_iff hL h1 h2 hok hk rB0 r1' rB0 rB1 rB01,
      inSAt_iff hL h1 h2 hok hk rB1 r1' rB0 rB1 rB01, ← e]
    exact ⟨(hD i).1, (hD i).2.1⟩
  obtain ⟨a0, ha0, k0, hk0, rp0, e0, hd0⟩ := hcode 0
  obtain ⟨a1, ha1, k1, hk1, rp1, e1, hd1⟩ := hcode 1
  obtain ⟨a2, ha2, k2, hk2, rp2, e2, hd2⟩ := hcode 2
  have rsq : ∀ {g : N7} {P : Nat}, Rp h1 h2 g P → Rp h1 h2 (g * g) (pc P P) :=
    fun hr => rp_mul h1 h2 hr hr
  have hs2 : ∀ i : Fin 3, ∀ {a k : Nat}, a < 2520 → k < 16 → u i = n7 (a7W a ++ tw7 k) →
      inDS (ak L a) (tk L k) (pw L (bGen7 0)) (pw L (bGen7 1))
        [idn, pw L (bGen7 0), pw L (bGen7 1), pw L (bGen7 0 ++ bGen7 1)] = true →
      ((u i * u i = 1 → 16 * a + k ∈ s2) ∧ (u i * u i * u i = 1 → 16 * a + k ∈ s3)) := by
    intro i a k ha hk e hd
    have hp := allAT_spec hpass ha hk
    rw [hd, Bool.not_true, Bool.false_or, sB_eq, sB_eq, Bool.and_eq_true] at hp
    have rE := rp_elem hL h1 h2 a hk
    rw [← e] at rE
    refine ⟨fun hsq => ?_, fun hcu => ?_⟩
    · have hq := hp.1
      rw [(eqP_iff hL h1 h2 hok (rsq rE) r1').2 hsq] at hq
      exact List.elem_iff.1 (by simpa using hq)
    · have hq := hp.2
      rw [(eqP_iff hL h1 h2 hok (rp_mul h1 h2 (rsq rE) rE) r1').2 hcu] at hq
      exact List.elem_iff.1 (by simpa using hq)
  have m0 : 16 * a0 + k0 ∈ s2 := (hs2 0 ha0 hk0 e0 hd0).1 (by simpa using q0)
  have m1 : 16 * a1 + k1 ∈ s2 := (hs2 1 ha1 hk1 e1 hd1).1 (by simpa using q1)
  have m2 : 16 * a2 + k2 ∈ s3 := (hs2 2 ha2 hk2 e2 hd2).2 (by simpa [mul_assoc] using q2)
  have el_eq : ∀ {a k : Nat}, k < 16 → el L (16 * a + k) = pc (ak L a) (tk L k) := by
    intro a k hk
    unfold el
    rw [code_div _ _ hk, code_mod _ _ hk]
  obtain ⟨r2, sw, hm0, hpairs⟩ := hrows _ m0 (hP a0 ha0 k0 hk0 e0)
  unfold swRowsK at hpairs
  rw [withL_eq] at hpairs
  simp only [sB_eq] at hpairs
  rw [forceL_eq, forceL_eq, forceL_eq, forceL_eq] at hpairs
  unfold swRows7 at hpairs
  obtain ⟨r, hr⟩ := zipAll_spec hpairs _ (List.mem_map.2 ⟨_, hm0, rfl⟩)
  obtain ⟨r', hr'⟩ := zipAll_spec hr _ (List.mem_map.2 ⟨_, m1, rfl⟩)
  rw [el_eq hk0, el_eq hk1] at hr'
  have hpair : (strictB (pc (pc (ak L a0) (tk L k0)) (pc (ak L a1) (tk L k1))) fun P =>
      eqP (pc P (pc P P)) idn) = true := by
    rw [sB_eq]
    have r01 := rp_mul h1 h2 rp0 rp1
    refine (eqP_iff hL h1 h2 hok (rp_mul h1 h2 r01 (rp_mul h1 h2 r01 r01)) r1').2 ?_
    have := hR _ (by rw [dRels7_eq]; exact List.mem_cons_self)
    simpa [mul_assoc] using this
  rw [hpair, Bool.not_true, Bool.false_or] at hr'
  obtain ⟨j, hj⟩ := zipAll_spec hr' _ (List.mem_map.2 ⟨_, m2, rfl⟩)
  rw [el_eq hk2] at hj
  have hmA : memL [pc (ak L a1) (tk L k1), pc (ak L a2) (tk L k2), pc (ak L a1) (tk L k1),
      pc (ak L a2) (tk L k2)] [pw L (bGen7 0), pw L (bGen7 1), pw L (bGen7 0 ++ bGen7 1)] =
      true := by
    have hw : ([1, 2, 1, 2] : List (Fin 3)) ∈ aWords7 := by decide
    have hf : List.Forall₂ (Rp h1 h2) (([1, 2, 1, 2] : List (Fin 3)).map u)
        [pc (ak L a1) (tk L k1), pc (ak L a2) (tk L k2), pc (ak L a1) (tk L k1),
          pc (ak L a2) (tk L k2)] := by
      simp only [List.map_cons, List.map_nil]
      exact .cons rp1 (.cons rp2 (.cons rp1 (.cons rp2 .nil)))
    rcases (hA _ hw).1 with e | e | e | e
    · exact absurd e (hA _ hw).2
    · exact memL_of h1 h2 hf rB0 (by simp) e
    · exact memL_of h1 h2 hf rB1 (by simp) e
    · exact memL_of h1 h2 hf rB01 (by simp) e
  have hmB : memL [pc (ak L a0) (tk L k0), pc (ak L a1) (tk L k1), pc (ak L a2) (tk L k2),
      pc (ak L a2) (tk L k2), pc (ak L a1) (tk L k1), pc (ak L a0) (tk L k0),
      pc (ak L a2) (tk L k2)] ((List.range 16).map (tk L)) = true := by
    have hw : ([0, 1, 2, 2, 1, 0, 2] : List (Fin 3)) ∈ bWords7 := by decide
    have hf : List.Forall₂ (Rp h1 h2) (([0, 1, 2, 2, 1, 0, 2] : List (Fin 3)).map u)
        [pc (ak L a0) (tk L k0), pc (ak L a1) (tk L k1), pc (ak L a2) (tk L k2),
          pc (ak L a2) (tk L k2), pc (ak L a1) (tk L k1), pc (ak L a0) (tk L k0),
          pc (ak L a2) (tk L k2)] := by
      simp only [List.map_cons, List.map_nil]
      exact .cons rp0 (.cons rp1 (.cons rp2 (.cons rp2 (.cons rp1 (.cons rp0 (.cons rp2 .nil))))))
    obtain ⟨k, hk, e⟩ := (hB _ hw).1
    exact memL_of h1 h2 hf (rp_tk hL h1 h2 hk) (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩) e
  have hcond : swCond7 L [idn, pw L (bGen7 0), pw L (bGen7 1), pw L (bGen7 0 ++ bGen7 1)]
      (pc (ak L a0) (tk L k0)) (pc (ak L a1) (tk L k1)) (pc (ak L a2) (tk L k2)) = true := by
    have rw' := rp_evP3 h1 h2 rp0 rp1 rp2
    unfold swCond7
    simp only [Bool.and_eq_true, List.all_eq_true, sB_eq]
    refine ⟨⟨fun w hw => relAt_of h1 h2 rp0 rp1 rp2
      (hR w (by rw [dRels7_eq]; exact List.mem_cons_of_mem _ hw)), fun w hw => ⟨?_, ?_⟩⟩,
      fun w hw => ⟨?_, ?_⟩⟩
    · exact (anyEq_iff hL h1 h2 hok (rw' w) r1' rB0 rB1 rB01).2 (hA w hw).1
    · rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact fun e => (hA w hw).2 ((eqP_iff hL h1 h2 hok (rw' w) r1').1 e)
    · exact (inTP_iff hL h1 h2 hok (rw' w)).2 (hB w hw).1
    · rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact fun e => (hB w hw).2 ((eqP_iff hL h1 h2 hok (rw' w) r1').1 e)
  simp only [List.tail_cons] at hj
  rw [hmA, hmB, hcond, Bool.and_self, Bool.and_self, Bool.not_true, Bool.false_or] at hj
  unfold swWit7 inDS at hj
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hj
  obtain ⟨⟨⟨⟨hf0, hf1⟩, hi0⟩, hi1⟩, hc⟩ := hj
  have hl : j % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rw [inSAt_iff hL h1 h2 hok hl rB0 r1' rB0 rB1 rB01] at hf0
  rw [inSAt_iff hL h1 h2 hok hl rB1 r1' rB0 rB1 rB01] at hf1
  rw [inSAtI_iff hL h1 h2 hok hl rB0 r1' rB0 rB1 rB01] at hi0
  rw [inSAtI_iff hL h1 h2 hok hl rB1 r1' rB0 rB1 rB01] at hi1
  refine ⟨_, ⟨hf0, hf1, hi0, hi1⟩, ?_⟩
  have hk : ∀ k : Fin 2, conj3 (ak L (j / 16)) (tk L (j % 16)) (pc (ak L a0) (tk L k0))
      (pc (ak L a1) (tk L k1)) (pc (ak L a2) (tk L k2)) (pw L (thetaW7 k 0))
      (pw L (thetaW7 k 1)) (pw L (thetaW7 k 2)) = true →
      ∀ i : Fin 3, n7 (a7W (j / 16) ++ tw7 (j % 16)) * u i * (n7 (a7W (j / 16) ++ tw7 (j % 16)))⁻¹ =
        n7 (thetaW7 k i) := by
    intro k hc i
    unfold conj3 at hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨c0, c1⟩, c2⟩ := hc
    fin_cases i
    · exact (conj_eq_iff _ _ _).1
        ((conjAt_iff hL h1 h2 hok hl rp0 (rp_pw hL h1 h2 (thetaW7 k 0))).1 c0)
    · exact (conj_eq_iff _ _ _).1
        ((conjAt_iff hL h1 h2 hok hl rp1 (rp_pw hL h1 h2 (thetaW7 k 1))).1 c1)
    · exact (conj_eq_iff _ _ _).1
        ((conjAt_iff hL h1 h2 hok hl rp2 (rp_pw hL h1 h2 (thetaW7 k 2))).1 c2)
  rcases hc with hc | hc
  · exact ⟨0, hk 0 hc⟩
  · exact ⟨1, hk 1 hc⟩

include hL h1 h2 hok in
theorem klein7_of {kc : List Nat} {kw : List (List Nat)}
    (h : klK7 L kc kw = true) (c : N7) (hcc : c * c = 1)
    (hcb : c * n7 (bGen7 0) = n7 (bGen7 0) * c)
    (hcT : ∀ k < 16, c ≠ n7 (tw7 k)) (hbcT : ∀ k < 16, n7 (bGen7 0) * c ≠ n7 (tw7 k))
    (hcb0 : c ≠ n7 (bGen7 0))
    (hcent : ∀ y : N7, (y * n7 (bGen7 0) = n7 (bGen7 0) * y ∨ y * c = c * y ∨
      y * (n7 (bGen7 0) * c) = n7 (bGen7 0) * c * y) → NormS (n7 (bGen7 0)) c y) :
    ∃ n : N7, S4 (n7 (bGen7 0)) c (n * n7 (bGen7 0) * n⁻¹) ∧
      S4 (n7 (bGen7 0)) c (n * n7 (bGen7 1) * n⁻¹) := by
  unfold klK7 at h
  rw [withL_eq] at h
  simp only [sB_eq] at h
  unfold klE7 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpass, hlist⟩ := h
  have rB0 := rp_pw hL h1 h2 (bGen7 0)
  have rB1 := rp_pw hL h1 h2 (bGen7 1)
  have r1' := rp_one h1 h2
  obtain ⟨a, ha, k, hk, rfl⟩ := n7K_surj hL h1 h2 hok c
  have rC := rp_elem hL h1 h2 a hk
  have rBC := rp_mul h1 h2 rB0 rC
  have hpre : klPre7 L (pw L (bGen7 0)) (ak L a) (tk L k) = true := by
    have t1 : inTP L (pc (ak L a) (tk L k)) = false := Bool.eq_false_iff.2 fun e => by
      obtain ⟨l, hl, e'⟩ := (inTP_iff hL h1 h2 hok rC).1 e
      exact hcT l hl e'
    have t2 : inTP L (pc (pw L (bGen7 0)) (pc (ak L a) (tk L k))) = false :=
      Bool.eq_false_iff.2 fun e => by
        obtain ⟨l, hl, e'⟩ := (inTP_iff hL h1 h2 hok rBC).1 e
        exact hbcT l hl e'
    have t3 : eqP (pc (ak L a) (tk L k)) (pw L (bGen7 0)) = false :=
      Bool.eq_false_iff.2 fun e => hcb0 ((eqP_iff hL h1 h2 hok rC rB0).1 e)
    unfold klPre7
    rw [sB_eq, invAt_of hL h1 h2 a hk hcc, (comAll_iff hL h1 h2 hok hk rB0).2 hcb, t1, t2, t3]
    rfl
  have hm := allAT_spec hpass ha hk
  rw [hpre, Bool.not_true, Bool.false_or] at hm
  obtain ⟨r, hr⟩ := allZ_spec hlist _ (List.elem_iff.1 hm)
  rw [sB_eq] at hr
  have elc : el L (16 * a + k) = pc (ak L a) (tk L k) := by
    unfold el
    rw [code_div _ _ hk, code_mod _ _ hk]
  rw [elc] at hr
  unfold klOne7 at hr
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hr
  have hl : r.getD 1 0 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rcases hr with ⟨-, hbad⟩ | ⟨-, hn⟩
  · exfalso
    unfold klBad7 at hbad
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, comAll_iff hL h1 h2 hok hl rB0,
      comAll_iff hL h1 h2 hok hl rC, comAll_iff hL h1 h2 hok hl rBC] at hbad
    obtain ⟨hcom, hnot⟩ := hbad
    have hN := hcent _ (by
      rcases hcom with (e | e) | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e))
    have hyes : (inDS (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) (pw L (bGen7 0))
        (pc (ak L a) (tk L k))
        [idn, pw L (bGen7 0), pc (ak L a) (tk L k), pc (pw L (bGen7 0)) (pc (ak L a) (tk L k))] &&
        inSAtI (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) (pw L (bGen7 0))
          [idn, pw L (bGen7 0), pc (ak L a) (tk L k),
            pc (pw L (bGen7 0)) (pc (ak L a) (tk L k))] &&
        inSAtI (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) (pc (ak L a) (tk L k))
          [idn, pw L (bGen7 0), pc (ak L a) (tk L k),
            pc (pw L (bGen7 0)) (pc (ak L a) (tk L k))]) = true := by
      unfold inDS
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨(inSAt_iff hL h1 h2 hok hl rB0 r1' rB0 rC rBC).2 hN.1,
        (inSAt_iff hL h1 h2 hok hl rC r1' rB0 rC rBC).2 hN.2.1⟩,
        (inSAtI_iff hL h1 h2 hok hl rB0 r1' rB0 rC rBC).2 hN.2.2.1⟩,
        (inSAtI_iff hL h1 h2 hok hl rC r1' rB0 rC rBC).2 hN.2.2.2⟩
    rw [hyes] at hnot
    exact absurd hnot (by decide)
  · unfold inDS at hn
    rw [Bool.and_eq_true, inSAt_iff hL h1 h2 hok hl rB0 r1' rB0 rC rBC,
      inSAt_iff hL h1 h2 hok hl rB1 r1' rB0 rC rBC] at hn
    exact ⟨_, hn⟩

end CFSG.KC.N7K

end
