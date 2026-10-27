module

public import CFSG.Certificates.Kernel.Multipliers.MonoAllR
public import CFSG.LieType.Multipliers.CoverWords

namespace CFSG.Certificates.Mono

open CFSG.KC.Mono CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace MonoP

variable {T : ℕ → ℕ} {m N n : ℕ}

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem andB_eq (a b : Bool) : CFSG.KC.andB a b = (a && b) := by
  cases a <;> rfl

theorem land_lo {x : ℕ} (a : ℕ) (hx : x < 65536) : Nat.land (x + Nat.shiftLeft a 16) 65535 = x := by
  have e : Nat.land (x + Nat.shiftLeft a 16) 65535 = (x + Nat.shiftLeft a 16) &&& (2 ^ 16 - 1) :=
    rfl
  have hs : Nat.shiftLeft a 16 = a * 2 ^ 16 := Nat.shiftLeft_eq a 16
  rw [e, Nat.and_two_pow_sub_one_eq_mod, hs, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (lt_of_lt_of_eq hx (by norm_num))]

theorem shr_hi {x : ℕ} (a : ℕ) (hx : x < 65536) : Nat.shiftRight (x + Nat.shiftLeft a 16) 16 = a := by
  change (x + Nat.shiftLeft a 16) >>> 16 = a
  have hs : Nat.shiftLeft a 16 = a * 2 ^ 16 := Nat.shiftLeft_eq a 16
  rw [Nat.shiftRight_eq_div_pow, hs, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (lt_of_lt_of_eq hx (by norm_num)), Nat.zero_add]

noncomputable def lmap (T : ℕ → ℕ) (m N n : ℕ) [NeZero N] (c : ℕ) (p : Fin N × ZMod n) :
    Fin N × ZMod n :=
  (⟨img (ent T (m + m) p.1 c) % N, Nat.mod_lt _ (NeZero.pos N)⟩,
    p.2 + (lab (ent T (m + m) p.1 c) : ZMod n))

noncomputable def wk (T : ℕ → ℕ) (m N n : ℕ) [NeZero N] (w : List ℕ) (p : Fin N × ZMod n) :
    Fin N × ZMod n :=
  w.foldl (fun q c => lmap T m N n c q) p

def enc {N n : ℕ} (p : Fin N × ZMod n) : ℕ := p.1.val + Nat.shiftLeft p.2.val 16

variable [NeZero N]

theorem lmap_add (c : ℕ) (x : Fin N) (α β : ZMod n) :
    lmap T m N n c (x, α + β) = ((lmap T m N n c (x, α)).1, (lmap T m N n c (x, α)).2 + β) := by
  simp only [lmap, Prod.mk.injEq, true_and]
  exact add_right_comm _ _ _

theorem wk_add : ∀ (w : List ℕ) (x : Fin N) (α β : ZMod n),
    wk T m N n w (x, α + β) = ((wk T m N n w (x, α)).1, (wk T m N n w (x, α)).2 + β)
  | [], _, _, _ => rfl
  | c :: w, x, α, β => by
    change wk T m N n w (lmap T m N n c (x, α + β)) = ((wk T m N n w (lmap T m N n c (x, α))).1,
      (wk T m N n w (lmap T m N n c (x, α))).2 + β)
    rw [lmap_add, wk_add w]

theorem wk_zero (w : List ℕ) (x : Fin N) (α : ZMod n) :
    wk T m N n w (x, α) = ((wk T m N n w (x, 0)).1, (wk T m N n w (x, 0)).2 + α) := by
  rw [← wk_add, zero_add]

omit [NeZero N] in
theorem enc_inj [NeZero n] (hN : N ≤ 65536) {p q : Fin N × ZMod n} (h : enc p = enc q) : p = q := by
  have hp : p.1.val < 65536 := by omega
  have hq : q.1.val < 65536 := by omega
  have h1 := congrArg (fun s => Nat.land s 65535) h
  have h2 := congrArg (fun s => Nat.shiftRight s 16) h
  simp only [enc] at h1 h2
  rw [land_lo _ hp, land_lo _ hq] at h1
  rw [shr_hi _ hp, shr_hi _ hq] at h2
  exact Prod.ext (Fin.ext h1) (ZMod.val_injective n h2)

theorem step_enc [NeZero n] (hN : N ≤ 65536) {c : ℕ} {p : Fin N × ZMod n}
    (hc : img (ent T (m + m) p.1 c) < N) :
    step T (m + m) n (enc p) c = enc (lmap T m N n c p) := by
  have hp : p.1.val < 65536 := by omega
  unfold step
  rw [strictN_eq]
  simp only [enc]
  rw [land_lo _ hp, shr_hi _ hp]
  simp only [lmap]
  rw [Nat.mod_eq_of_lt hc, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  rfl

theorem walk_enc [NeZero n] (hN : N ≤ 65536)
    (hr : ∀ x : Fin N, ∀ c < m + m, img (ent T (m + m) x c) < N) :
    ∀ (w : List ℕ), (∀ c ∈ w, c < m + m) → ∀ p : Fin N × ZMod n,
      walk T (m + m) n w (enc p) = enc (wk T m N n w p)
  | [], _, _ => rfl
  | c :: w, hw, p => by
    change CFSG.KC.Loop.strictN (step T (m + m) n (enc p) c) (walk T (m + m) n w) =
      enc (wk T m N n w (lmap T m N n c p))
    rw [strictN_eq, step_enc hN (hr p.1 c (hw c List.mem_cons_self))]
    exact walk_enc hN hr w (fun c' h => hw c' (List.mem_cons_of_mem _ h)) _

theorem relsGo {L x : ℕ} {C : ℕ → ℕ} : ∀ (Rc : List (List ℕ)) (k : ℕ),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun r _ ih k => CFSG.KC.andB (Nat.beq (walk T L n r x)
        (Nat.add x (Nat.shiftLeft (C k) (nat_lit 16)))) (ih (Nat.succ k))) Rc k = true →
    ∀ j (hj : j < Rc.length), walk T L n Rc[j] x = x + Nat.shiftLeft (C (k + j)) 16
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | r :: Rc, k, h, j, hj => by
    change CFSG.KC.andB _ _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases j with _ | j
    · exact Nat.eq_of_beq_eq_true h.1
    · have := relsGo Rc (Nat.succ k) h.2 j (by simpa using hj)
      rw [show k + (j + 1) = Nat.succ k + j by omega]
      exact this

theorem wordsGo {L x : ℕ} : ∀ (W : List (List ℕ)), wordsOK T L n W x = true →
    ∀ w ∈ W, walk T L n w x = x
  | [], _, _, hw => absurd hw List.not_mem_nil
  | v :: W, h, w, hw => by
    change CFSG.KC.andB _ _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact Nat.eq_of_beq_eq_true h.1
    · exact wordsGo W h.2 w hw

def tr (N n : ℕ) (β : ZMod n) : Equiv.Perm (Fin N × ZMod n) where
  toFun p := (p.1, p.2 + β)
  invFun p := (p.1, p.2 - β)
  left_inv p := by simp
  right_inv p := by simp

omit [NeZero N] in
theorem enc_zero {n : ℕ} (x : Fin N) : enc ((x, 0) : Fin N × ZMod n) = x.val := by
  simp [enc, ZMod.val_zero]

end MonoP

open MonoP in
public theorem mono_sound_proved {m N n : ℕ} (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool))
    {Rc Wc : List (List ℕ)} (hR : codes R = Rc)
    (hW : codes ((List.finRange m).map fun i => (i, false) :: w i) = Wc)
    {T C : ℕ → ℕ} (hp : paramsOK N n C R.length = true)
    (h : ∀ x < N, pointOK T m N n C Rc Wc x = true) :
    ∃ (E : Type) (_ : Group E) (ψ : PG m (CFSG.LieType.Multipliers.coverWords R w) →* E)
      (τ : Multiplicative (ZMod n) →* E), Function.Injective τ ∧
        ∀ k (hk : k < R.length), ψ (PresentedGroup.mk _ (FreeGroup.mk R[k])) =
          τ (Multiplicative.ofAdd (C k : ZMod n)) := by
  unfold paramsOK at hp
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hp
  obtain ⟨hN0, hN, hn0, hC⟩ := hp
  have hC' := allR_spec hC
  have : NeZero N := ⟨by omega⟩
  have : NeZero n := ⟨by omega⟩
  have hpt : ∀ x : Fin N, _ := fun x => h x.val x.isLt
  simp only [pointOK, andB_eq, Bool.and_eq_true, Nat.add_eq] at hpt
  have hr : ∀ x : Fin N, ∀ c < m + m, img (ent T (m + m) x c) < N := by
    intro x c hc
    have := allR_spec (hpt x).1 c (Nat.zero_le _) (by change c < 0 + (m + m); omega)
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at this
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
      have := allR_spec (hpt x).2.1 i.val (Nat.zero_le _) (by omega)
      rw [andB_eq, Bool.and_eq_true] at this
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
  let τ : Multiplicative (ZMod n) →* (Equiv.Perm (Fin N × ZMod n))ᵐᵒᵖ :=
    { toFun := fun t => MulOpposite.op (tr N n t.toAdd)
      map_one' := by
        apply MulOpposite.unop_injective
        ext1 p
        simp [tr]
      map_mul' := by
        intro a b
        apply MulOpposite.unop_injective
        ext1 p
        simp only [MulOpposite.unop_op, MulOpposite.unop_mul, Equiv.Perm.mul_apply, toAdd_mul]
        simp only [tr, Equiv.coe_fn_mk, Prod.mk.injEq, true_and]
        ring }
  refine ⟨(Equiv.Perm (Fin N × ZMod n))ᵐᵒᵖ, inferInstance, PresentedGroup.toGroup hkill, τ, ?_, ?_⟩
  · intro a b e
    have e1 := congrArg (fun t => t.unop (⟨0, NeZero.pos N⟩, 0)) e
    simp only [τ, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, tr, Equiv.coe_fn_mk,
      zero_add, Prod.mk.injEq, true_and] at e1
    exact Multiplicative.toAdd.injective e1
  · intro k hk
    exact hrel k hk

end CFSG.Certificates.Mono
