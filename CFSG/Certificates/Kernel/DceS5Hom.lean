module

public import CFSG.Certificates.Kernel.DceS5Rc

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Loop CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord
open scoped Classical

set_option exponentiation.threshold 400

variable {G : Type*} [Group G] {LT LI TL VL NL : ℕ}

theorem relOK_spec {RR : ℕ → ℕ} {r : ℕ} (h : relOK RR LT TL VL NL r = true) :
    (∀ i < bits (RR r) 2 10, byte (Nat.shiftRight (RR r) 12) i < NL) ∧
      (nOnly TL VL NL (RR r) → segProd LT TL VL NL (Nat.shiftRight (RR r) 12) 0 (bits (RR r) 2 10) =
        ONE7) := by
  unfold relOK at h
  beta_reduce at h
  obtain ⟨h1, h2⟩ := andL_iff.1 h
  refine ⟨fun i hi => Nat.blt_eq.mp ((allL_iff (fun i => Nat.blt (byte (Nat.shiftRight (RR r) 12) i) NL)
    _).1 h1 i hi), fun hN => ?_⟩
  rcases orL_iff.1 h2 with h3 | h3
  · rw [notL_eq] at h3
    have : Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (isN TL VL NL
        (byte (Nat.shiftRight (RR r) 12) i))) (bits (RR r) 2 10) = true :=
      (allL_iff (fun i => isN TL VL NL (byte (Nat.shiftRight (RR r) 12) i)) _).2 hN
    rw [h3] at this
    exact absurd this Bool.false_ne_true
  · exact Nat.eq_of_beq_eq_true h3

theorem relsOK_spec {RR : ℕ → ℕ} {NR : ℕ} (h : relsOK RR LT TL VL NL NR = true) :
    ∀ r < NR, relOK RR LT TL VL NL r = true :=
  (allL_iff (fun r => relOK RR LT TL VL NL r) NR).1 h

@[expose] noncomputable def wordFG (e : ℕ) : FreeGroup ℕ :=
  ((List.range (bits e 2 10)).map fun i => FreeGroup.of (byte (Nat.shiftRight e 12) i)).prod

theorem lift_wordFG {H : Type*} [Group H] (y : ℕ → H) (e : ℕ) :
    FreeGroup.lift y (wordFG e) = rval y e := by
  unfold wordFG rval
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by simp

@[expose] def relSet (RR : ℕ → ℕ) (LI TL VL NL NR : ℕ) : Set (FreeGroup ℕ) :=
  {w | ∃ r < NR, nOnly TL VL NL (RR r) ∧ w = wordFG (RR r)} ∪
    {w | ∃ c < NL, isN TL VL NL c = true ∧ w = FreeGroup.of (byte LI c) * FreeGroup.of c}

theorem relSet_iff {RR : ℕ → ℕ} {NR : ℕ} {H : Type*} [Group H] (y : ℕ → H) :
    (∀ w ∈ relSet RR LI TL VL NL NR, FreeGroup.lift y w = 1) ↔
      (∀ r < NR, nOnly TL VL NL (RR r) → rval y (RR r) = 1) ∧
        ∀ c < NL, isN TL VL NL c = true → y (byte LI c) = (y c)⁻¹ := by
  constructor
  · intro h
    refine ⟨fun r hr hN => ?_, fun c hc hN => ?_⟩
    · rw [← lift_wordFG]
      exact h _ (Or.inl ⟨r, hr, hN, rfl⟩)
    · have := h _ (Or.inr ⟨c, hc, hN, rfl⟩)
      rw [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this
      exact eq_inv_of_mul_eq_one_left this
  · rintro ⟨h1, h2⟩ w (⟨r, hr, hN, rfl⟩ | ⟨c, hc, hN, rfl⟩)
    · rw [lift_wordFG]
      exact h1 r hr hN
    · rw [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, h2 c hc hN, inv_mul_cancel]

section Model

variable (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL)
include hc hL

theorem model_rels {RR : ℕ → ℕ} {NR : ℕ} (hrels : relsOK RR LT TL VL NL NR = true) :
    ∀ w ∈ relSet RR LI TL VL NL NR, FreeGroup.lift (Lm LT LI TL VL NL) w = 1 := by
  rw [relSet_iff]
  refine ⟨fun r hr hN => ?_, fun c hc' hN => ?_⟩
  · have hseg := (relOK_spec (relsOK_spec hrels r hr)).2 hN
    rcases segProd_spec hc hL (Nat.shiftRight (RR r) 12) 0 (bits (RR r) 2 10) with h0 | ⟨-, -, h3⟩
    · exact absurd (hseg.symm.trans h0) (one7_ne_zero hc)
    apply Units.ext
    rw [hseg, (one7 hc).2] at h3
    rw [Units.val_one, h3, rval, ← Units.coeHom_apply, map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
    simp only [Function.comp_apply, Units.coeHom_apply, Nat.zero_add]
    exact Lm_val hc hL (hN i (List.mem_range.1 hi))
  · have e : Lm LT LI TL VL NL (byte LI c) * Lm LT LI TL VL NL c = 1 := by
      apply Units.ext
      rw [Units.val_mul, Lm_val hc hL (hL.isN_inv hN), Lm_val hc hL hN, Units.val_one]
      have e := letter_inv hc hL (hL.isN_inv hN)
      rwa [(hL.inv c hc').1] at e
    exact eq_inv_of_mul_eq_one_left e

end Model

@[expose] noncomputable def Ncl (x : ℕ → G) (TL VL NL : ℕ) : Subgroup G :=
  Subgroup.closure (x '' Nset TL VL NL)

theorem model_hom (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL) {RR : ℕ → ℕ} {NR NORD : ℕ}
    (hrels : relsOK RR LT TL VL NL NR = true)
    (hN : ∀ (H : Type) [Group H] (y : ℕ → H),
      (∀ r < NR, nOnly TL VL NL (RR r) → rval y (RR r) = 1) →
      (∀ c < NL, isN TL VL NL c = true → y (byte LI c) = (y c)⁻¹) →
      Finite (Subgroup.closure (y '' {c | c < NL ∧ isN TL VL NL c = true})) ∧
        Nat.card (Subgroup.closure (y '' {c | c < NL ∧ isN TL VL NL c = true})) ≤ NORD)
    (hM : NORD ≤ Nat.card (Mg LT LI TL VL NL)) (x : ℕ → G)
    (hx : ∀ r < NR, nOnly TL VL NL (RR r) → rval x (RR r) = 1)
    (hxi : ∀ c < NL, isN TL VL NL c = true → x (byte LI c) = (x c)⁻¹) :
    ∃ φ : Mg LT LI TL VL NL →* G,
      (∀ c (h : c ∈ Nset TL VL NL),
        φ ⟨Lm LT LI TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c) ∧
      (∀ m, φ m ∈ Ncl x TL VL NL) ∧ ∀ n ∈ Ncl x TL VL NL, ∃ m, φ m = n :=
  DceTw.lift_hom (relSet RR LI TL VL NL NR) (Nset TL VL NL) NORD
    (fun H _ y hy => hN H y ((relSet_iff y).1 hy).1 ((relSet_iff y).1 hy).2)
    (Lm LT LI TL VL NL) (model_rels hc hL hrels) hM x ((relSet_iff x).2 ⟨hx, hxi⟩)

theorem usqOK_spec {RR : ℕ → ℕ} {NR USQ W Wi h : ℕ} (hu : usqOK RR LT LI TL VL NL NR USQ W Wi h = true) :
    h < NR ∧ W = segProd LT TL VL NL (Nat.shiftRight USQ 12) 0 (bits USQ 2 10) ∧ validM7 Wi = true ∧
      mul7 W Wi = ONE7 ∧ bits (RR h) 2 10 = bits USQ 2 10 + 2 ∧
      CFSG.KC.Th.isRot (Nat.shiftRight (RR h) 12) (bits USQ 2 10 + 2)
        (CFSG.KC.Th.wCat (Nat.lor TL (Nat.shiftLeft TL 8)) 2
          (CFSG.KC.Th.wInv LI (Nat.shiftRight USQ 12) (bits USQ 2 10))) = true := by
  unfold usqOK at hu
  beta_reduce at hu
  obtain ⟨e1, r⟩ := andL_iff.1 hu
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, r⟩ := andL_iff.1 r
  obtain ⟨e5, e6⟩ := andL_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, e3, Nat.eq_of_beq_eq_true e4,
    Nat.eq_of_beq_eq_true e5, e6⟩

theorem TT_eq {T : ℕ} (hT : T < 256) : Nat.lor T (Nat.shiftLeft T 8) = T + 256 * T := by
  have := lor_mul T T 1 (by simpa using hT)
  simpa using this

theorem TT_lt {T : ℕ} (hT : T < 256) : Nat.lor T (Nat.shiftLeft T 8) < 256 ^ 2 := by
  rw [TT_eq hT]
  norm_num
  omega

theorem wv_TT (f : ℕ → G) {T : ℕ} (hT : T < 256) : wv f (Nat.lor T (Nat.shiftLeft T 8)) 2 = f T * f T := by
  have e := TT_eq hT
  have b0 : byteG (Nat.lor T (Nat.shiftLeft T 8)) 0 = T := by
    rw [byteG_eq, e, CFSG.Certificates.KB.Sound.byte_eq']
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hT]
  have b1 : byteG (Nat.lor T (Nat.shiftLeft T 8)) 1 = T := by
    rw [byteG_eq, e, CFSG.Certificates.KB.Sound.byte_eq']
    rw [pow_one, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hT, Nat.zero_add,
      Nat.mod_eq_of_lt hT]
  unfold wv
  rw [show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [b0, b1]

section Usq

variable (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL) {x : ℕ → G}
  (φ : Mg LT LI TL VL NL →* G)
  (hφ : ∀ c (h : c ∈ Nset TL VL NL),
    φ ⟨Lm LT LI TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c)
  {RR : ℕ → ℕ} {NR : ℕ} (hrels : ∀ r < NR, rval x (RR r) = 1)
  (hnorm : CFSG.Certificates.LCE.relsNorm RR NR = true)
  (hxi : ∀ c < NL, isN TL VL NL c = true → x (byte LI c) = (x c)⁻¹)
include hc hL hφ hrels hnorm hxi

theorem usq_sem {USQ W Wi h : ℕ} (hu : usqOK RR LT LI TL VL NL NR USQ W Wi h = true) :
    InM LT LI TL VL NL W ∧ InM LT LI TL VL NL Wi ∧ mul7 W Wi = ONE7 ∧
      x TL * x TL = rc φ W ∧ rc φ Wi = (rc φ W)⁻¹ := by
  obtain ⟨hh, eW, hWi, hWW, hlen, hrot⟩ := usqOK_spec hu
  have hWne : W ≠ 0 := fun h0 => by
    rw [h0, mul7_zero_left hc (valid7 hc hWi)] at hWW
    exact one7_ne_zero hc hWW.symm
  rw [eW] at hWne
  obtain ⟨hN, hWm, vW⟩ := rc_segProd hc hL φ hφ _ 0 _ hWne
  rw [← eW] at hWm vW
  have hWim := InM_invR hc hWm (valid7 hc hWi) hWW
  refine ⟨hWm, hWim, hWW, ?_, rc_invR hc φ hWm (valid7 hc hWi) hWW⟩
  obtain ⟨s, -, hs⟩ := isRot_spec hrot
  have hval := wv_rot x (relsNorm_spec hnorm h hh) (hrels h hh) s
  rw [hlen, hs] at hval
  have hTL : TL < 256 := by have := hL.tl; have := hL.nl; omega
  rw [show bits USQ 2 10 + 2 = 2 + bits USQ 2 10 from Nat.add_comm _ _, wv_wCat x (TT_lt hTL)
    (wInv_lt _ _ _), wv_TT x hTL, wv_wInv x _ _ _ (fun q hq => by
      have h1 := hN q hq
      rw [Nat.zero_add] at h1
      exact hxi _ (isN_iff.1 h1).1 h1)] at hval
  rw [vW, eq_of_mul_inv_eq_one hval]
  unfold wv
  simp only [Nat.zero_add]
  rfl

end Usq

end CFSG.Certificates.DS5

end
