module

public import CFSG.Certificates.Kernel.DceS5Model
public import CFSG.Certificates.Kernel.DceWords
public import Certificates.Data.Kernel.LceSTab

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Loop CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord
open scoped Classical

set_option exponentiation.threshold 400

variable {G : Type*} [Group G] {LT LI TL VL NL : ℕ}

@[expose] noncomputable def rc (φ : Mg LT LI TL VL NL →* G) (A : ℕ) : G := φ (mEl LT LI TL VL NL A)

theorem byte_eq_byteG (x i : ℕ) : byte x i = byteG x i := rfl

theorem rval_eq (x : ℕ → G) (e : ℕ) : rval x e = wv x (Nat.shiftRight e 12) (bits e 2 10) := rfl

theorem relsNorm_spec {RR : ℕ → ℕ} {NR : ℕ} (h : CFSG.Certificates.LCE.relsNorm RR NR = true) :
    ∀ r < NR, Nat.shiftRight (RR r) 12 < 256 ^ bits (RR r) 2 10 := by
  have key : ∀ n, CFSG.Certificates.LCE.relsNorm RR n = true → ∀ r < n,
      Nat.blt (Nat.shiftRight (RR r) 12)
        (Nat.shiftLeft 1 (Nat.mul 8 (Nat.land (Nat.shiftRight (RR r) 2) 1023))) = true := by
    intro n
    induction n with
    | zero => exact fun _ r hr => absurd hr (Nat.not_lt_zero r)
    | succ n ih =>
      intro h r hr
      have h' : Bool.rec (motive := fun _ => Bool) false (CFSG.Certificates.LCE.relsNorm RR n)
          (Nat.blt (Nat.shiftRight (RR n) 12)
            (Nat.shiftLeft 1 (Nat.mul 8 (Nat.land (Nat.shiftRight (RR n) 2) 1023)))) = true := h
      rw [band_iff] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · exact ih h'.2 r hr
      · exact h'.1
  intro r hr
  have h1 := key NR h r hr
  rw [Nat.blt_eq] at h1
  have e : Nat.land (Nat.shiftRight (RR r) 2) 1023 = bits (RR r) 2 10 := rfl
  rw [e] at h1
  change Nat.shiftRight (RR r) 12 < 1 <<< (8 * bits (RR r) 2 10) at h1
  rw [Nat.one_shiftLeft, pow_mul] at h1
  norm_num at h1
  exact h1

section Rc

variable (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL) {x : ℕ → G}
  (φ : Mg LT LI TL VL NL →* G)
  (hφ : ∀ c (h : c ∈ Nset TL VL NL),
    φ ⟨Lm LT LI TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c)

theorem mEl_eq {A : ℕ} (y : Mg LT LI TL VL NL) (hA : C7 A) (hy : ((y : Mat7ˣ) : Mat7) = m7 A) :
    mEl LT LI TL VL NL A = y := by
  have h : InM LT LI TL VL NL A := ⟨hA, y, y.2, hy⟩
  apply Subtype.ext
  apply Units.ext
  rw [mEl_val h, hy]

theorem rc_eq {A : ℕ} (y : Mg LT LI TL VL NL) (hA : C7 A) (hy : ((y : Mat7ˣ) : Mat7) = m7 A) :
    rc φ A = φ y := by
  unfold rc
  rw [mEl_eq y hA hy]

theorem InM_ne_zero : ¬InM LT LI TL VL NL 0 := by
  rintro ⟨-, y, -, hy⟩
  rw [zero7.2] at hy
  have := y.val_inv
  rw [hy, zero_mul] at this
  have h1 : (1 : Mat7) 0 0 = 0 := by rw [← this]; rfl
  exact absurd h1 (by decide)

include hc

theorem rc_one : rc φ ONE7 = 1 := by
  rw [rc_eq φ 1 (one7 hc).1 (by rw [(one7 hc).2]; rfl), map_one]

theorem rc_mul {A B : ℕ} (hA : InM LT LI TL VL NL A) (hB : InM LT LI TL VL NL B) :
    rc φ (mul7 A B) = rc φ A * rc φ B := by
  have hAB := InM_mul hc hA hB
  rw [rc_eq φ (mEl LT LI TL VL NL A * mEl LT LI TL VL NL B) hAB.1 (by
    rw [Subgroup.coe_mul, Units.val_mul, mEl_val hA, mEl_val hB, (mul7_sound hc hA.1 hB.1).2]),
    map_mul]
  rfl

theorem rc_invR {A B : ℕ} (hA : InM LT LI TL VL NL A) (hB : C7 B) (h : mul7 A B = ONE7) :
    rc φ B = (rc φ A)⁻¹ := by
  have hB' := InM_invR hc hA hB h
  have e := rc_mul hc φ hA hB'
  rw [h, rc_one hc φ] at e
  exact (inv_eq_of_mul_eq_one_right e.symm).symm

include hL hφ

theorem rc_letter {c : ℕ} (hN : isN TL VL NL c = true) : rc φ (let7 LT c) = x c := by
  rw [rc_eq φ ⟨_, Lm_mem hN⟩ (letter_C7 hc hL hN) (Lm_val hc hL hN)]
  exact hφ c ⟨(isN_iff.1 hN).1, hN⟩

theorem rc_segProd (Wd o : ℕ) : ∀ m, segProd LT TL VL NL Wd o m ≠ 0 →
    (∀ k < m, isN TL VL NL (byte Wd (o + k)) = true) ∧ InM LT LI TL VL NL (segProd LT TL VL NL Wd o m) ∧
      rc φ (segProd LT TL VL NL Wd o m) = ((List.range m).map fun k => x (byte Wd (o + k))).prod
  | 0, _ => ⟨fun k hk => absurd hk (Nat.not_lt_zero k), InM_one hc, rc_one hc φ⟩
  | m + 1, hne => by
    have hs : segProd LT TL VL NL Wd o (m + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mul7 (segProd LT TL VL NL Wd o m) (let7 LT (byte Wd (o + m))))
        (isN TL VL NL (byte Wd (o + m))) := rfl
    rw [hs] at hne ⊢
    cases hN : isN TL VL NL (byte Wd (o + m))
    · rw [hN] at hne
      exact absurd rfl hne
    · rw [hN] at hne
      dsimp only at hne ⊢
      have hne' : segProd LT TL VL NL Wd o m ≠ 0 := fun h0 => by
        rw [h0, mul7_zero_left hc (letter_C7 hc hL hN)] at hne
        exact hne rfl
      obtain ⟨h1, h2, h3⟩ := rc_segProd Wd o m hne'
      refine ⟨fun k hk => ?_, InM_mul hc h2 (InM_letter hc hL hN), ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact h1 k hk
        · exact hN
      · rw [rc_mul hc φ h2 (InM_letter hc hL hN), h3, rc_letter hc hL φ hφ hN, List.range_succ,
          List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

end Rc

theorem relVisOK_spec {RR : ℕ → ℕ} {LT TL VL NL NR S P r s ns : ℕ}
    (h : relVisOK RR LT TL VL NL NR S P r s ns = true) :
    r < NR ∧ ns + 2 ≤ bits (RR r) 2 10 ∧
      byte (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) 0 = VL ∧
      byte (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) (ns + 1) = TL ∧
      S = segProd LT TL VL NL (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) 1 ns ∧
      mul7 P (segProd LT TL VL NL (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s)
        (ns + 2) (bits (RR r) 2 10 - (ns + 2))) = ONE7 := by
  unfold relVisOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andL_iff.1 h
  obtain ⟨-, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, r⟩ := andL_iff.1 r
  obtain ⟨e5, r⟩ := andL_iff.1 r
  obtain ⟨e6, e7⟩ := andL_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.le_of_ble_eq_true e3, Nat.eq_of_beq_eq_true e4,
    Nat.eq_of_beq_eq_true e5, Nat.eq_of_beq_eq_true e6, Nat.eq_of_beq_eq_true e7⟩

section Psi

variable (hc : constsOK7 = true) (hL : LetOK LT LI TL VL NL) {x : ℕ → G}
  (φ : Mg LT LI TL VL NL →* G)
  (hφ : ∀ c (h : c ∈ Nset TL VL NL),
    φ ⟨Lm LT LI TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c)
  {RR : ℕ → ℕ} {NR : ℕ} (hrels : ∀ r < NR, rval x (RR r) = 1)
  (hnorm : CFSG.Certificates.LCE.relsNorm RR NR = true) (hu : x VL = (x TL)⁻¹)
include hc hL hφ hrels hnorm hu

theorem relVis_sem {S P r s ns : ℕ} (h : relVisOK RR LT TL VL NL NR S P r s ns = true)
    (hS : InM LT LI TL VL NL S) (hP : validM7 P = true) :
    InM LT LI TL VL NL P ∧ (x TL)⁻¹ * rc φ S * x TL = rc φ P := by
  obtain ⟨hr, hn, h0, h1, eS, eP⟩ := relVisOK_spec h
  set n := bits (RR r) 2 10
  set Wd := CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) n s
  have hQne : segProd LT TL VL NL Wd (ns + 2) (n - (ns + 2)) ≠ 0 := fun h0' => by
    rw [h0', mul7_zero_right hc (valid7 hc hP)] at eP
    exact one7_ne_zero hc eP.symm
  obtain ⟨-, hQ, vQ⟩ := rc_segProd hc hL φ hφ Wd (ns + 2) _ hQne
  have hSne : S ≠ 0 := fun h0' => InM_ne_zero (h0' ▸ hS)
  rw [eS] at hSne hS ⊢
  obtain ⟨-, -, vS⟩ := rc_segProd hc hL φ hφ Wd 1 ns hSne
  have hPm : InM LT LI TL VL NL P := InM_invL hc hQ (valid7 hc hP) eP
  refine ⟨hPm, ?_⟩
  have hinv := rc_invR hc φ hPm hQ.1 eP
  have hval : wv x Wd n = 1 := wv_rot x (relsNorm_spec hnorm r hr) (hrels r hr) s
  have e2 : n = (ns + 2) + (n - (ns + 2)) := by omega
  rw [e2, wv_split, show ns + 2 = (1 + ns) + 1 by omega, wv_succ, wv_split] at hval
  have hw1 : wv x Wd 1 = x VL := by
    unfold wv
    simp only [List.range_one, List.map_singleton, List.prod_singleton]
    rw [← byte_eq_byteG, h0]
  rw [hw1, ← byte_eq_byteG, show 1 + ns = ns + 1 by omega, h1, hu] at hval
  have hP' : rc φ P = (rc φ (segProd LT TL VL NL Wd (ns + 2) (n - (ns + 2))))⁻¹ := by
    rw [hinv, inv_inv]
  rw [vS, hP', vQ]
  have hval' : (x TL)⁻¹ * ((List.range ns).map fun k => x (byte Wd (1 + k))).prod * x TL *
      ((List.range (n - (ns + 2))).map fun k => x (byte Wd (ns + 2 + k))).prod = 1 := hval
  exact eq_inv_of_mul_eq_one_left hval'

theorem psi_sem {TB OB : ℕ → ℕ} {nT I0 : ℕ} {Ct : List ℕ}
    (hT : runT TB OB RR LT TL VL NL NR nT I0 Ct 1 = nT + 1) (hθ : canonP (pt OB I0) = true) :
    ∀ e < nT, InM LT LI TL VL NL (tP TB e) ∧ (x TL)⁻¹ * rc φ (tS TB e) * x TL = rc φ (tP TB e) := by
  have htab := tab_mem hc hL hT hθ
  rw [runT_eq] at hT
  have hi := cntRun_spec (a := 0) hT
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    obtain ⟨J, ht⟩ := hi e (Nat.zero_le _) he
    obtain ⟨-, hP, -, hk⟩ := tOK_spec ht
    rcases hk with ⟨a, b, ha, hb, eS, eP⟩ | ⟨r, s, ns, hr, -⟩
    · obtain ⟨pa, ea⟩ := ih a ha (by omega)
      obtain ⟨pb, eb⟩ := ih b hb (by omega)
      have sa := (htab a (by omega)).1
      have sb := (htab b (by omega)).1
      refine ⟨eP ▸ InM_mul hc pa pb, ?_⟩
      rw [eS, eP, rc_mul hc φ sa sb, rc_mul hc φ pa pb, ← ea, ← eb]
      group
    · exact relVis_sem hc hL φ hφ hrels hnorm hu hr (htab e he).1 hP

end Psi

end CFSG.Certificates.DS5

end
