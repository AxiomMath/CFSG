module

public import Certificates.Data.Kernel.T75JM.L2KF
public import CFSG.Certificates.Kernel.T75JM.L2KSound

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable

@[expose] def S4 {G : Type*} [Group G] (b c y : G) : Prop := y = 1 ∨ y = b ∨ y = c ∨ y = b * c

@[expose] def NormS {G : Type*} [Group G] (b c y : G) : Prop :=
  S4 b c (y * b * y⁻¹) ∧ S4 b c (y * c * y⁻¹) ∧ S4 b c (y⁻¹ * b * y) ∧ S4 b c (y⁻¹ * c * y)

variable {L : Int → Nat} (hL : LetterRd L) (h1 : n0InvCheck = true) (hok : n0kOk L = true)

def Rp (g : N0) (P : Nat) : Prop :=
  ∀ x < 22, idx 22 (phiK h1 (n0RelCheck_of hL (n0kOk_parts hok).1) g) x = fd 5 P x

include hL in
theorem rp_pw (w : List (Fin 6 × Bool)) : Rp hL h1 hok (n0 w) (pw L w) :=
  fun _ hx => idx_pw hL w hx

include hL in
theorem rp_elem (a : Nat) {k : Nat} (hk : k < 16) :
    Rp hL h1 hok (n0 (a6W a ++ tw k)) (pc (ak L a) (tk L k)) := fun x hx => by
  rw [idx_elem hL a hk hx, fd_pc _ _ hx]

include hL in
theorem rp_el (c : Nat) : Rp hL h1 hok (n0 (a6W (c / 16) ++ tw (c % 16))) (el L c) :=
  rp_elem hL h1 hok _ (Nat.mod_lt _ (by norm_num))

include hL in
theorem rp_tk {l : Nat} (hl : l < 16) : Rp hL h1 hok (n0 (tw l)) (tk L l) :=
  fun _ hx => idx_tk hL hl hx

theorem rp_one : Rp hL h1 hok 1 idn := fun x hx => by
  rw [map_one, idx_one, hid x hx]

theorem rp_mul {g h : N0} {P Q : Nat} (hg : Rp hL h1 hok g P) (hh : Rp hL h1 hok h Q) :
    Rp hL h1 hok (g * h) (pc P Q) := fun x hx => by
  have hb : fd 5 Q x < 22 := hh x hx ▸ idx_lt _ hx
  rw [map_mul, idx_mul, hh x hx, hg _ hb, fd_pc _ _ hx]

theorem eqP_iff {g h : N0} {P Q : Nat} (hg : Rp hL h1 hok g P)
    (hh : Rp hL h1 hok h Q) : eqP P Q = true ↔ g = h := by
  constructor
  · intro e
    refine phiK_injective (h2 := n0RelCheck_of hL (n0kOk_parts hok).1) hL h1 hok
      (eq_of_idx fun x hx => ?_)
    rw [hg x hx, hh x hx]
    have := List.all_eq_true.1 e x (List.mem_range.2 hx)
    rw [fdN_eq, fdN_eq] at this
    exact Nat.eq_of_beq_eq_true this
  · rintro rfl
    refine List.all_eq_true.2 fun x hx => ?_
    have hx' := List.mem_range.1 hx
    rw [fdN_eq, fdN_eq, ← hg x hx', ← hh x hx']
    exact Nat.beq_refl _

theorem conjAt_iff {b l : Nat} (hl : l < 16) {g y : N0}
    {P Y : Nat} (hg : Rp hL h1 hok g P) (hy : Rp hL h1 hok y Y) :
    conjAt (ak L b) (tk L l) P Y = true ↔
      n0 (a6W b ++ tw l) * g = y * n0 (a6W b ++ tw l) := by
  have hn := rp_elem hL h1 hok b hl
  have e1 := eqP_iff hL h1 hok (rp_mul hL h1 hok hn hg) (rp_mul hL h1 hok hy hn)
  have key : ∀ x ∈ List.range 22,
      Nat.beq (fdN 5 (ak L b) (fdN 5 (tk L l) (fdN 5 P x)))
          (fdN 5 Y (fdN 5 (ak L b) (fdN 5 (tk L l) x))) =
        Nat.beq (fdN 5 (pc (pc (ak L b) (tk L l)) P) x)
          (fdN 5 (pc Y (pc (ak L b) (tk L l))) x) := by
    intro x hx
    have hx' := List.mem_range.1 hx
    have hP : fd 5 P x < 22 := hg x hx' ▸ idx_lt _ hx'
    simp only [fdN_eq, fd_pc _ _ hx', fd_pc _ _ hP]
  rw [← e1]
  unfold conjAt eqP
  rw [List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun x hx => by rw [key x hx]

theorem comAll_iff {b l : Nat} (hl : l < 16) {g : N0} {P : Nat}
    (hg : Rp hL h1 hok g P) :
    comAll (ak L b) (tk L l) P = true ↔ n0 (a6W b ++ tw l) * g = g * n0 (a6W b ++ tw l) :=
  conjAt_iff hL h1 hok hl hg hg

theorem conj_eq_iff {G : Type*} [Group G] (n g y : G) : n * g = y * n ↔ n * g * n⁻¹ = y :=
  mul_inv_eq_iff_eq_mul.symm

theorem conj_inv_iff {G : Type*} [Group G] (n g y : G) : n * y = g * n ↔ n⁻¹ * g * n = y := by
  constructor
  · intro h
    rw [mul_assoc, ← h]
    group
  · intro h
    rw [← h]
    group

theorem inSAt_iff {b l : Nat} (hl : l < 16) {v s1 s2 s3 s4 : N0}
    {P Y1 Y2 Y3 Y4 : Nat} (hv : Rp hL h1 hok v P) (r1 : Rp hL h1 hok s1 Y1)
    (r2 : Rp hL h1 hok s2 Y2) (r3 : Rp hL h1 hok s3 Y3) (r4 : Rp hL h1 hok s4 Y4) :
    inSAt (ak L b) (tk L l) P [Y1, Y2, Y3, Y4] = true ↔
      (n0 (a6W b ++ tw l) * v * (n0 (a6W b ++ tw l))⁻¹ = s1 ∨
        n0 (a6W b ++ tw l) * v * (n0 (a6W b ++ tw l))⁻¹ = s2 ∨
        n0 (a6W b ++ tw l) * v * (n0 (a6W b ++ tw l))⁻¹ = s3 ∨
        n0 (a6W b ++ tw l) * v * (n0 (a6W b ++ tw l))⁻¹ = s4) := by
  unfold inSAt
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    conjAt_iff hL h1 hok hl hv r1, conjAt_iff hL h1 hok hl hv r2, conjAt_iff hL h1 hok hl hv r3,
    conjAt_iff hL h1 hok hl hv r4, conj_eq_iff]

theorem inSAtI_iff {b l : Nat} (hl : l < 16) {v s1 s2 s3 s4 : N0}
    {P Y1 Y2 Y3 Y4 : Nat} (hv : Rp hL h1 hok v P) (r1 : Rp hL h1 hok s1 Y1)
    (r2 : Rp hL h1 hok s2 Y2) (r3 : Rp hL h1 hok s3 Y3) (r4 : Rp hL h1 hok s4 Y4) :
    inSAtI (ak L b) (tk L l) P [Y1, Y2, Y3, Y4] = true ↔
      ((n0 (a6W b ++ tw l))⁻¹ * v * n0 (a6W b ++ tw l) = s1 ∨
        (n0 (a6W b ++ tw l))⁻¹ * v * n0 (a6W b ++ tw l) = s2 ∨
        (n0 (a6W b ++ tw l))⁻¹ * v * n0 (a6W b ++ tw l) = s3 ∨
        (n0 (a6W b ++ tw l))⁻¹ * v * n0 (a6W b ++ tw l) = s4) := by
  unfold inSAtI
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    conjAt_iff hL h1 hok hl r1 hv, conjAt_iff hL h1 hok hl r2 hv, conjAt_iff hL h1 hok hl r3 hv,
    conjAt_iff hL h1 hok hl r4 hv, conj_inv_iff]

theorem anyEq_iff {v s1 s2 s3 s4 : N0} {P Y1 Y2 Y3 Y4 : Nat}
    (hv : Rp hL h1 hok v P) (r1 : Rp hL h1 hok s1 Y1) (r2 : Rp hL h1 hok s2 Y2)
    (r3 : Rp hL h1 hok s3 Y3) (r4 : Rp hL h1 hok s4 Y4) :
    ([Y1, Y2, Y3, Y4].any fun Y => eqP P Y) = true ↔ (v = s1 ∨ v = s2 ∨ v = s3 ∨ v = s4) := by
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    eqP_iff hL h1 hok hv r1, eqP_iff hL h1 hok hv r2, eqP_iff hL h1 hok hv r3,
    eqP_iff hL h1 hok hv r4]

theorem inTP_iff {v : N0} {P : Nat} (hv : Rp hL h1 hok v P) :
    inTP L P = true ↔ ∃ l < 16, v = n0 (tw l) := by
  unfold inTP
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, e⟩
    have hl' := List.mem_range.1 hl
    exact ⟨l, hl', (eqP_iff hL h1 hok hv (rp_tk hL h1 hok hl')).1 e⟩
  · rintro ⟨l, hl, e⟩
    exact ⟨l, List.mem_range.2 hl, (eqP_iff hL h1 hok hv (rp_tk hL h1 hok hl)).2 e⟩

include hL h1 hok in
theorem invAt_of (a : Nat) {k : Nat} (hk : k < 16)
    (hsq : n0 (a6W a ++ tw k) * n0 (a6W a ++ tw k) = 1) : invAt (ak L a) (tk L k) = true := by
  have hn := rp_elem hL h1 hok a hk
  have e := (eqP_iff hL h1 hok (rp_mul hL h1 hok hn hn) (rp_one hL h1 hok)).2 hsq
  refine List.all_eq_true.2 fun x hx => ?_
  have hx' := List.mem_range.1 hx
  have e' := List.all_eq_true.1 e x hx
  have hAT : fd 5 (ak L a) (fd 5 (tk L k) x) < 22 := by
    rw [← fd_pc _ _ hx', ← hn x hx']
    exact idx_lt _ hx'
  rw [fdN_eq, fdN_eq, fd_pc _ _ hx', fd_pc (ak L a) (tk L k) hx', fd_pc _ _ hAT, hid x hx'] at e'
  rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq]
  exact e'

theorem allZ_spec {β : Type} {d : β} {g : Nat → β → Bool} :
    ∀ {l : List Nat} {rs : List β}, allZ d g l rs = true → ∀ c ∈ l, ∃ r, g c r = true
  | [], _, _, c, hc => absurd hc (by simp)
  | c' :: l, rs, h, c, hc => by
    have e : allZ d g (c' :: l) rs = (g c' (rs.headD d) && allZ d g l rs.tail) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨_, h.1⟩
    · exact allZ_spec h.2 c hc

theorem code_div (a k : Nat) (hk : k < 16) : (16 * a + k) / 16 = a := by omega

theorem code_mod (a k : Nat) (hk : k < 16) : (16 * a + k) % 16 = k := by omega

theorem rp_evP {u : Fin 2 → N0} {U0 U1 : Nat} (r0 : Rp hL h1 hok (u 0) U0)
    (r1 : Rp hL h1 hok (u 1) U1) (w : List (Fin 2)) : Rp hL h1 hok (w.map u).prod (evP U0 U1 w) := by
  have key : ∀ (w : List (Fin 2)) (acc : Nat) (g : N0), Rp hL h1 hok g acc →
      Rp hL h1 hok (g * (w.map u).prod)
        (w.foldl (fun acc i => pc acc (if i = 0 then U0 else U1)) acc) := by
    intro w
    induction w with
    | nil => intro acc g h; simpa using h
    | cons i w ih =>
      intro acc g h
      have hi : Rp hL h1 hok (u i) (if i = 0 then U0 else U1) := by
        fin_cases i
        · exact r0
        · exact r1
      have := ih _ _ (rp_mul hL h1 hok h hi)
      simpa [mul_assoc] using this
  simpa [evP] using key w idn 1 (rp_one hL h1 hok)

include hL h1 hok in
theorem swap_of {su0 su1 : List Nat} {sj : List (List Nat)}
    (h : swK L su0 su1 sj = true) (u : Fin 2 → N0)
    (hD : ∀ i, NormS (n0 (bGen 0)) (n0 (bGen 1)) (u i))
    (r1 : (([0, 0, 0, 0] : List (Fin 2)).map u).prod = 1)
    (r2 : (([1, 1, 1, 1] : List (Fin 2)).map u).prod = 1)
    (r3 : (([0, 1, 0, 1, 0, 1] : List (Fin 2)).map u).prod = 1)
    (hA : ∀ w ∈ aWords, S4 (n0 (bGen 0)) (n0 (bGen 1)) (w.map u).prod ∧ (w.map u).prod ≠ 1)
    (hB : ∀ w ∈ bWords, (∃ k < 16, (w.map u).prod = n0 (tw k)) ∧ (w.map u).prod ≠ 1) :
    ∃ j : N0, NormS (n0 (bGen 0)) (n0 (bGen 1)) j ∧
      ∀ i : Fin 2, j * u i * j⁻¹ = n0 (dTheta i) := by
  unfold swK at h
  rw [withL_eq] at h
  simp only [sB_eq] at h
  unfold swE at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpass, hpairs⟩ := h
  have rB0 := rp_pw hL h1 hok (bGen 0)
  have rB1 := rp_pw hL h1 hok (bGen 1)
  have rB01 : Rp hL h1 hok (n0 (bGen 0) * n0 (bGen 1)) (pw L (bGen 0 ++ bGen 1)) := by
    rw [← n0_append]
    exact rp_pw hL h1 hok _
  have r1' := rp_one hL h1 hok
  have hcode : ∀ i : Fin 2, ∃ a < 360, ∃ k < 16, Rp hL h1 hok (u i) (pc (ak L a) (tk L k)) ∧
      (inDS (ak L a) (tk L k) (pw L (bGen 0)) (pw L (bGen 1))
        [idn, pw L (bGen 0), pw L (bGen 1), pw L (bGen 0 ++ bGen 1)] = true) := by
    intro i
    obtain ⟨a, ha, k, hk, e⟩ := n0K_surj hL h1 hok (u i)
    refine ⟨a, ha, k, hk, by rw [e]; exact rp_elem hL h1 hok a hk, ?_⟩
    unfold inDS
    rw [Bool.and_eq_true, inSAt_iff hL h1 hok hk rB0 r1' rB0 rB1 rB01,
      inSAt_iff hL h1 hok hk rB1 r1' rB0 rB1 rB01, ← e]
    exact ⟨(hD i).1, (hD i).2.1⟩
  obtain ⟨a0, ha0, k0, hk0, rp0, hd0⟩ := hcode 0
  obtain ⟨a1, ha1, k1, hk1, rp1, hd1⟩ := hcode 1
  have rsq : ∀ i : Fin 2, ∀ {a k : Nat}, Rp hL h1 hok (u i) (pc (ak L a) (tk L k)) →
      Rp hL h1 hok (([i, i] : List (Fin 2)).map u).prod
        (pc (pc (ak L a) (tk L k)) (pc (ak L a) (tk L k))) := by
    intro i a k hr
    have := rp_mul hL h1 hok hr hr
    simpa using this
  have hne : ∀ {g : N0} {P : Nat}, Rp hL h1 hok g P → g ≠ 1 → (!(eqP P idn)) = true := by
    intro g P hg hg1
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro e
    exact hg1 ((eqP_iff hL h1 hok hg r1').1 e)
  have hp0 := allAT_spec hpass ha0 hk0
  rw [hd0, Bool.not_true, Bool.false_or, sB_eq, sB_eq, Bool.and_eq_true] at hp0
  have m0 : 16 * a0 + k0 ∈ su0 := by
    have hb := hB [0, 0] (by simp [bWords])
    have hq := hp0.1
    rw [(inTP_iff hL h1 hok (rsq 0 rp0)).2 hb.1, hne (rsq 0 rp0) hb.2] at hq
    simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hq
    exact List.elem_iff.1 hq
  have hp1 := allAT_spec hpass ha1 hk1
  rw [hd1, Bool.not_true, Bool.false_or, sB_eq, sB_eq, Bool.and_eq_true] at hp1
  have m1 : 16 * a1 + k1 ∈ su1 := by
    have ha := hA [1, 1] (by simp [aWords])
    have hq := hp1.2
    rw [(anyEq_iff hL h1 hok (rsq 1 rp1) r1' rB0 rB1 rB01).2 ha.1, hne (rsq 1 rp1) ha.2] at hq
    simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hq
    exact List.elem_iff.1 hq
  obtain ⟨r, hr⟩ := allZ_spec hpairs _ m0
  rw [sB_eq] at hr
  obtain ⟨j, hj⟩ := allZ_spec hr _ m1
  rw [sB_eq] at hj
  have el0 : el L (16 * a0 + k0) = pc (ak L a0) (tk L k0) := by
    unfold el
    rw [code_div _ _ hk0, code_mod _ _ hk0]
  have el1 : el L (16 * a1 + k1) = pc (ak L a1) (tk L k1) := by
    unfold el
    rw [code_div _ _ hk1, code_mod _ _ hk1]
  rw [el0, el1] at hj
  have hcond : swCond L [idn, pw L (bGen 0), pw L (bGen 1), pw L (bGen 0 ++ bGen 1)]
      (pc (ak L a0) (tk L k0)) (pc (ak L a1) (tk L k1)) = true := by
    have rw' := rp_evP hL h1 hok rp0 rp1
    unfold swCond
    simp only [Bool.and_eq_true, List.all_eq_true, sB_eq]
    refine ⟨⟨⟨⟨(eqP_iff hL h1 hok (rw' _) r1').2 r1, (eqP_iff hL h1 hok (rw' _) r1').2 r2⟩,
      (eqP_iff hL h1 hok (rw' _) r1').2 r3⟩, fun w hw => ⟨?_, ?_⟩⟩, fun w hw => ⟨?_, ?_⟩⟩
    · exact (anyEq_iff hL h1 hok (rw' w) r1' rB0 rB1 rB01).2 (hA w hw).1
    · exact hne (rw' w) (hA w hw).2
    · exact (inTP_iff hL h1 hok (rw' w)).2 (hB w hw).1
    · exact hne (rw' w) (hB w hw).2
  rw [hcond, Bool.not_true, Bool.or_false] at hj
  unfold swWit inDS at hj
  simp only [Bool.and_eq_true] at hj
  obtain ⟨⟨⟨⟨⟨hf0, hf1⟩, hi0⟩, hi1⟩, hc0⟩, hc1⟩ := hj
  have hl : j % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rw [inSAt_iff hL h1 hok hl rB0 r1' rB0 rB1 rB01] at hf0
  rw [inSAt_iff hL h1 hok hl rB1 r1' rB0 rB1 rB01] at hf1
  rw [inSAtI_iff hL h1 hok hl rB0 r1' rB0 rB1 rB01] at hi0
  rw [inSAtI_iff hL h1 hok hl rB1 r1' rB0 rB1 rB01] at hi1
  rw [conjAt_iff hL h1 hok hl rp0 (rp_pw hL h1 hok (dTheta 0)), conj_eq_iff] at hc0
  rw [conjAt_iff hL h1 hok hl rp1 (rp_pw hL h1 hok (dTheta 1)), conj_eq_iff] at hc1
  refine ⟨_, ⟨hf0, hf1, hi0, hi1⟩, fun i => ?_⟩
  fin_cases i
  · exact hc0
  · exact hc1

include hL h1 hok in
theorem klein_of {kc : List Nat} {kw : List (List Nat)}
    (h : klK L kc kw = true) (c : N0) (hcc : c * c = 1) (hcb : c * n0 (bGen 0) = n0 (bGen 0) * c)
    (hcT : ∀ k < 16, c ≠ n0 (tw k)) (hbcT : ∀ k < 16, n0 (bGen 0) * c ≠ n0 (tw k))
    (hcb0 : c ≠ n0 (bGen 0))
    (hcent : ∀ y : N0, (y * n0 (bGen 0) = n0 (bGen 0) * y ∨ y * c = c * y ∨
      y * (n0 (bGen 0) * c) = n0 (bGen 0) * c * y) → NormS (n0 (bGen 0)) c y) :
    ∃ n : N0, (S4 (n0 (bGen 0)) c (n * n0 (bGen 0) * n⁻¹) ∧
        S4 (n0 (bGen 0)) c (n * n0 (bGen 1) * n⁻¹)) ∨
      (S4 (n0 (bGen 0)) c (n * n0 (substWord (bGen 0)) * n⁻¹) ∧
        S4 (n0 (bGen 0)) c (n * n0 (substWord (bGen 1)) * n⁻¹)) := by
  unfold klK at h
  rw [withL_eq] at h
  simp only [sB_eq] at h
  unfold klE at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpass, hlist⟩ := h
  have rB0 := rp_pw hL h1 hok (bGen 0)
  have rB1 := rp_pw hL h1 hok (bGen 1)
  have r1' := rp_one hL h1 hok
  obtain ⟨a, ha, k, hk, rfl⟩ := n0K_surj hL h1 hok c
  have rC := rp_elem hL h1 hok a hk
  have rBC := rp_mul hL h1 hok rB0 rC
  have hpre : klPre L (pw L (bGen 0)) (ak L a) (tk L k) = true := by
    have t1 : inTP L (pc (ak L a) (tk L k)) = false := Bool.eq_false_iff.2 fun e => by
      obtain ⟨l, hl, e'⟩ := (inTP_iff hL h1 hok rC).1 e
      exact hcT l hl e'
    have t2 : inTP L (pc (pw L (bGen 0)) (pc (ak L a) (tk L k))) = false :=
      Bool.eq_false_iff.2 fun e => by
        obtain ⟨l, hl, e'⟩ := (inTP_iff hL h1 hok rBC).1 e
        exact hbcT l hl e'
    have t3 : eqP (pc (ak L a) (tk L k)) (pw L (bGen 0)) = false :=
      Bool.eq_false_iff.2 fun e => hcb0 ((eqP_iff hL h1 hok rC rB0).1 e)
    unfold klPre
    rw [sB_eq, invAt_of hL h1 hok a hk hcc, (comAll_iff hL h1 hok hk rB0).2 hcb, t1, t2, t3]
    rfl
  have hm := allAT_spec hpass ha hk
  rw [hpre, Bool.not_true, Bool.false_or] at hm
  obtain ⟨r, hr⟩ := allZ_spec hlist _ (List.elem_iff.1 hm)
  rw [sB_eq] at hr
  have elc : el L (16 * a + k) = pc (ak L a) (tk L k) := by
    unfold el
    rw [code_div _ _ hk, code_mod _ _ hk]
  rw [elc] at hr
  unfold klOne at hr
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hr
  have hl : r.getD 1 0 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rcases hr with (⟨-, hbad⟩ | ⟨-, hn⟩) | ⟨-, hn⟩
  · exfalso
    unfold klBad at hbad
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, comAll_iff hL h1 hok hl rB0,
      comAll_iff hL h1 hok hl rC, comAll_iff hL h1 hok hl rBC] at hbad
    obtain ⟨hcom, hnot⟩ := hbad
    have hN := hcent _ (by
      rcases hcom with (e | e) | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e))
    have hyes : (inDS (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) (pw L (bGen 0))
        (pc (ak L a) (tk L k))
        [idn, pw L (bGen 0), pc (ak L a) (tk L k), pc (pw L (bGen 0)) (pc (ak L a) (tk L k))] &&
        inSAtI (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) (pw L (bGen 0))
          [idn, pw L (bGen 0), pc (ak L a) (tk L k), pc (pw L (bGen 0)) (pc (ak L a) (tk L k))] &&
        inSAtI (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) (pc (ak L a) (tk L k))
          [idn, pw L (bGen 0), pc (ak L a) (tk L k), pc (pw L (bGen 0)) (pc (ak L a) (tk L k))]) =
        true := by
      unfold inDS
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨(inSAt_iff hL h1 hok hl rB0 r1' rB0 rC rBC).2 hN.1,
        (inSAt_iff hL h1 hok hl rC r1' rB0 rC rBC).2 hN.2.1⟩,
        (inSAtI_iff hL h1 hok hl rB0 r1' rB0 rC rBC).2 hN.2.2.1⟩,
        (inSAtI_iff hL h1 hok hl rC r1' rB0 rC rBC).2 hN.2.2.2⟩
    rw [hyes] at hnot
    exact absurd hnot (by decide)
  · unfold inDS at hn
    rw [Bool.and_eq_true, inSAt_iff hL h1 hok hl rB0 r1' rB0 rC rBC,
      inSAt_iff hL h1 hok hl rB1 r1' rB0 rC rBC] at hn
    exact ⟨_, Or.inl hn⟩
  · unfold inDS at hn
    rw [Bool.and_eq_true, inSAt_iff hL h1 hok hl (rp_pw hL h1 hok _) r1' rB0 rC rBC,
      inSAt_iff hL h1 hok hl (rp_pw hL h1 hok _) r1' rB0 rC rBC] at hn
    exact ⟨_, Or.inr hn⟩

end CFSG.KC.N0K

end
