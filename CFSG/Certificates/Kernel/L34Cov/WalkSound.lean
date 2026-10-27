module

public import Certificates.Data.Kernel.L34Cov.Walk
public import CFSG.Certificates.Kernel.Multipliers.MonoSoundProved
import all CFSG.Certificates.Kernel.Multipliers.MonoSoundProved

public section

namespace CFSG.Certificates.L34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.Loop CFSG.LieType.Multipliers.L34 CFSG.Fischer
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable

theorem rwalk_nil (V v : ℕ) : rwalk V [] v = v := rfl

theorem rwalk_cons (V c : ℕ) (w : List ℕ) (v : ℕ) : rwalk V (c :: w) v = rwalk V w (vtOf V v c) :=
  Mono.MonoP.strictN_eq _ _

theorem vecMulM_mul (x : F4 × F4 × F4) (M N : Mat3) :
    vecMulM (vecMulM x M) N = vecMulM x (M.mul N) := by
  obtain ⟨a, b, c⟩ := x
  simp only [vecMulM, Mat3.mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem vecMulM_one (x : F4 × F4 × F4) : vecMulM x Mat3.one = x := by
  obtain ⟨a, b, c⟩ := x
  simp [vecMulM, Mat3.one, Mat3.scalar]

theorem decV_encV (x : F4 × F4 × F4) : decV (encV x) = x := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := x
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [decV, encV, Prod.mk.injEq, F4.mk.injEq]
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [] <;> omega

theorem encV_lt (x : F4 × F4 × F4) : encV x < 64 := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := x
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [encV]
  omega

theorem encV_inj {x y : F4 × F4 × F4} (h : encV x = encV y) : x = y := by
  rw [← decV_encV x, h, decV_encV]

theorem codeMat_letterCode (l : Fin 2 × Bool) : codeMat (letterCode l) = letterMat l := by
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b <;> rfl

theorem letterCode_lt (l : Fin 2 × Bool) : letterCode l < 4 := by
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b <;> decide

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem vtOf_spec {V : ℕ} (hV : vtOK V = true) (x : F4 × F4 × F4) (l : Fin 2 × Bool) :
    vtOf V (encV x) (letterCode l) = encV (vecMulM x (letterMat l)) := by
  have h1 := Mono.allR_spec hV (encV x) (Nat.zero_le _) (encV_lt x)
  have h2 := Mono.allR_spec h1 (letterCode l) (Nat.zero_le _) (letterCode_lt l)
  rw [Nat.eq_of_beq_eq_true h2, decV_encV, codeMat_letterCode]

theorem rwalk_spec {V : ℕ} (hV : vtOK V = true) (w : List (Fin 2 × Bool)) (x : F4 × F4 × F4) :
    rwalk V (w.map letterCode) (encV x) = encV (vecMulM x (wordMat w)) := by
  induction w generalizing x with
  | nil => rw [List.map_nil, rwalk_nil, wordMat, List.foldr_nil, vecMulM_one]
  | cons l w ih =>
    rw [List.map_cons, rwalk_cons, vtOf_spec hV x l, ih, vecMulM_mul]
    rfl

theorem wordMat_eq_scalar {V : ℕ} (hV : vtOK V = true) {w : List (Fin 2 × Bool)} {s : ℕ}
    (hs : s < 4) (h : rowsOK V (w.map letterCode) s = true) :
    wordMat w = Mat3.scalar ⟨⟨s, hs⟩⟩ := by
  unfold rowsOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2⟩ := h
  have r0 := rwalk_spec hV w (1, 0, 0)
  have r1 := rwalk_spec hV w (0, 1, 0)
  have r2 := rwalk_spec hV w (0, 0, 1)
  have e0 : encV ((1, 0, 0) : F4 × F4 × F4) = 1 := rfl
  have e1 : encV ((0, 1, 0) : F4 × F4 × F4) = 4 := rfl
  have e2 : encV ((0, 0, 1) : F4 × F4 × F4) = 16 := rfl
  have hz : (0 : F4).code.val = 0 := rfl
  have f0 : encV ((⟨⟨s, hs⟩⟩, 0, 0) : F4 × F4 × F4) = s := by simp [encV, hz]
  have f1 : encV ((0, ⟨⟨s, hs⟩⟩, 0) : F4 × F4 × F4) = Nat.mul 4 s := by simp [encV, hz]
  have f2 : encV ((0, 0, ⟨⟨s, hs⟩⟩) : F4 × F4 × F4) = Nat.mul 16 s := by simp [encV, hz]
  rw [e0, Nat.eq_of_beq_eq_true h0, ← f0] at r0
  rw [e1, Nat.eq_of_beq_eq_true h1, ← f1] at r1
  rw [e2, Nat.eq_of_beq_eq_true h2, ← f2] at r2
  have g0 := encV_inj r0.symm
  have g1 := encV_inj r1.symm
  have g2 := encV_inj r2.symm
  generalize wordMat w = W at g0 g1 g2
  obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ := W
  simp only [vecMulM, one_mul, zero_mul, add_zero, zero_add, Prod.mk.injEq] at g0 g1 g2
  obtain ⟨rfl, rfl, rfl⟩ := g0
  obtain ⟨rfl, rfl, rfl⟩ := g1
  obtain ⟨rfl, rfl, rfl⟩ := g2
  rfl

open CFSG.KC.Mono Mono.MonoP in
theorem mono_model {m N n : ℕ} (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool))
    {Rc Wc : List (List ℕ)} (hR : codes R = Rc)
    (hW : codes ((List.finRange m).map fun i => (i, false) :: w i) = Wc)
    {T C : ℕ → ℕ} (hp : paramsOK N n C R.length = true)
    (h : ∀ x < N, pointOK T m N n C Rc Wc x = true) :
    ∃ ψ : PG m (CFSG.LieType.Multipliers.coverWords R w) →* (Equiv.Perm (Fin N × ZMod n))ᵐᵒᵖ,
      (∀ k (hk : k < R.length) (p : Fin N × ZMod n),
        (ψ (PresentedGroup.mk _ (FreeGroup.mk R[k]))).unop p = (p.1, p.2 + (C k : ZMod n))) ∧
      ∀ (u : List (Fin m × Bool)) (x : Fin N),
        walk T (m + m) n (u.map letterCode) x.val =
          ((ψ (PresentedGroup.mk _ (FreeGroup.mk u))).unop (x, 0)).1.val +
            Nat.shiftLeft ((ψ (PresentedGroup.mk _ (FreeGroup.mk u))).unop (x, 0)).2.val 16 := by
  unfold paramsOK at hp
  simp only [Mono.MonoP.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hp
  obtain ⟨hN0, hN, hn0, hC⟩ := hp
  have hC' := Mono.allR_spec hC
  have : NeZero N := ⟨by omega⟩
  have : NeZero n := ⟨by omega⟩
  have hpt : ∀ x : Fin N, _ := fun x => h x.val x.isLt
  simp only [pointOK, Mono.MonoP.andB_eq, Bool.and_eq_true, Nat.add_eq] at hpt
  have hr : ∀ x : Fin N, ∀ c < m + m, img (ent T (m + m) x c) < N := by
    intro x c hc
    have := Mono.allR_spec (hpt x).1 c (Nat.zero_le _) (by change c < 0 + (m + m); omega)
    rw [Mono.MonoP.andB_eq, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1
  have hcodes : ∀ u : List (Fin m × Bool), ∀ c ∈ u.map letterCode, c < m + m := by
    intro u c hc
    obtain ⟨⟨i, b⟩, -, rfl⟩ := List.mem_map.1 hc
    simp only [letterCode]
    split <;> omega
  have hwalk := walk_enc (T := T) (m := m) (n := n) hN hr
  have hfix : ∀ v : List ℕ, (∀ c ∈ v, c < m + m) → (∀ x : Fin N, walk T (m + m) n v x = x) →
      ∀ p, wk T m N n v p = p := by
    intro v hv hx p
    have e := hwalk v hv (p.1, 0)
    rw [enc_zero, hx] at e
    have e2 : wk T m N n v (p.1, 0) = (p.1, 0) := enc_inj hN (by rw [← e, enc_zero])
    rw [show p = (p.1, 0 + p.2) by simp, wk_add, e2]
  have hinv : ∀ i : Fin m, ∀ p, lmap T m N n (2 * i + 1) (lmap T m N n (2 * i) p) = p ∧
      lmap T m N n (2 * i) (lmap T m N n (2 * i + 1) p) = p := by
    intro i p
    have h2 : ∀ x : Fin N, walk T (m + m) n [2 * i, 2 * i + 1] x = x ∧
        walk T (m + m) n [2 * i + 1, 2 * i] x = x := by
      intro x
      have := Mono.allR_spec (hpt x).2.1 i.val (Nat.zero_le _) (by omega)
      rw [Mono.MonoP.andB_eq, Bool.and_eq_true] at this
      obtain ⟨a, b⟩ := this
      unfold pairOK at a b
      rw [two_mul]
      exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩
    have hl : ∀ c ∈ [2 * i.val, 2 * i.val + 1], c < m + m := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    have hl' : ∀ c ∈ [2 * i.val + 1, 2 * i.val], c < m + m := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    exact ⟨hfix _ hl (fun x => (h2 x).1) p, hfix _ hl' (fun x => (h2 x).2) p⟩
  let σ : Fin m → Equiv.Perm (Fin N × ZMod n) := fun i =>
    ⟨lmap T m N n (2 * i), lmap T m N n (2 * i + 1), fun p => (hinv i p).1, fun p => (hinv i p).2⟩
  let ψ0 : FreeGroup (Fin m) →* (Equiv.Perm (Fin N × ZMod n))ᵐᵒᵖ :=
    FreeGroup.lift fun i => MulOpposite.op (σ i)
  have heval : ∀ (u : List (Fin m × Bool)) p,
      (ψ0 (FreeGroup.mk u)).unop p = wk T m N n (u.map letterCode) p := by
    intro u
    induction u with
    | nil => intro p; rfl
    | cons a u ih =>
      intro p
      rw [show FreeGroup.mk (a :: u) = FreeGroup.mk [a] * FreeGroup.mk u by
        rw [FreeGroup.mul_mk]; rfl, map_mul, MulOpposite.unop_mul, Equiv.Perm.mul_apply, ih]
      change _ = wk T m N n (u.map letterCode) (lmap T m N n (letterCode a) p)
      congr 1
      obtain ⟨i, b⟩ := a
      cases b with
      | true =>
        change (ψ0 (FreeGroup.of i)).unop p = _
        rw [FreeGroup.lift_apply_of]
        simp [σ, letterCode]
      | false =>
        rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of, MulOpposite.unop_inv]
        simp [σ, letterCode]
  have hrel : ∀ k (hk : k < R.length), ψ0 (FreeGroup.mk R[k]) = MulOpposite.op (tr N n (C k)) := by
    intro k hk
    apply MulOpposite.unop_injective
    ext1 p
    rw [heval]
    have hkR : k < Rc.length := by rw [← hR]; simpa [codes] using hk
    have hw := relsGo (T := T) (n := n) (x := p.1.val) (C := C) Rc 0 (hpt p.1).2.2.1 k hkR
    subst hR
    have hck : ((C k : ZMod n)).val = C k := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.blt_eq.mp (hC' k (Nat.zero_le _) (by omega)))]
    have e := hwalk (R[k].map letterCode) (hcodes _) (p.1, 0)
    simp only [codes, List.getElem_map, Nat.zero_add] at hw
    rw [enc_zero, hw] at e
    have e2 : wk T m N n (R[k].map letterCode) (p.1, 0) = (p.1, (C k : ZMod n)) :=
      enc_inj hN (by rw [← e]; simp only [enc, hck])
    rw [show p = (p.1, 0 + p.2) by simp, wk_add, e2]
    change _ = (p.1, (0 + p.2) + (C k : ZMod n))
    rw [zero_add, add_comm]
  have hcomm : ∀ (i : Fin m) β, σ i * tr N n β = tr N n β * σ i := by
    intro i β
    ext1 p
    change lmap T m N n (2 * i) (p.1, p.2 + β) = ((lmap T m N n (2 * i) p).1,
      (lmap T m N n (2 * i) p).2 + β)
    rw [lmap_add]
  have hkill : ∀ r ∈ (CFSG.LieType.Multipliers.coverWords R w).map FreeGroup.mk, ψ0 r = 1 := by
    intro r hr'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr'
    simp only [CFSG.LieType.Multipliers.coverWords, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and] at hu
    rcases hu with ⟨i, v, hv, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
      rw [CFSG.LieType.Multipliers.mk_commWord, map_commutatorElement, hrel k hk,
        commutatorElement_eq_one_iff_mul_comm]
      change ψ0 (FreeGroup.of i) * _ = _ * ψ0 (FreeGroup.of i)
      rw [FreeGroup.lift_apply_of]
      apply MulOpposite.unop_injective
      simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
      exact (hcomm i (C k)).symm
    · apply MulOpposite.unop_injective
      ext1 p
      rw [heval]
      refine congrArg (fun q => q) (hfix _ (hcodes _) (fun x => ?_) p)
      refine wordsGo Wc (hpt x).2.2.2 _ ?_
      rw [← hW]
      simp only [codes, List.mem_map, List.mem_finRange, true_and]
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
  refine ⟨PresentedGroup.toGroup hkill, fun k hk p => ?_, fun u x => ?_⟩
  · change (ψ0 (FreeGroup.mk R[k])).unop p = _
    rw [hrel k hk]
    rfl
  · change walk T (m + m) n (u.map letterCode) x.val =
      ((ψ0 (FreeGroup.mk u)).unop (x, 0)).1.val + Nat.shiftLeft ((ψ0 (FreeGroup.mk u)).unop (x, 0)).2.val 16
    rw [heval, ← enc_zero x, hwalk _ (hcodes u)]
    rfl

end CFSG.Certificates.L34Cov

end
