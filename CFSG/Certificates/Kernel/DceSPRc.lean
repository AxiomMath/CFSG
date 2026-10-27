module

public import CFSG.Certificates.Kernel.DceSPModel
public import CFSG.Certificates.Kernel.DceWords
import Mathlib.Tactic.Group
public import Certificates.Data.Kernel.LceSTab
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Certificates.DSP

open CFSG.KC.Loop CFSG.KC.HNA.DceS CFSG.Certificates.DceLoop CFSG.Certificates.DceWord
open scoped Classical

set_option exponentiation.threshold 400

variable {G : Type*} [Group G] {LT LI TL VL NL : ℕ}

@[expose] noncomputable def rc (φ : Mg LT TL VL NL →* G) (A : ℕ) : G := φ (mEl LT TL VL NL A)

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

variable (hL : LetOK LT LI TL VL NL) {x : ℕ → G}
  (φ : Mg LT TL VL NL →* G)
  (hφ : ∀ c (h : c ∈ Nset TL VL NL),
    φ ⟨Lm LT TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c)

theorem mEl_eq {A : ℕ} (y : Mg LT TL VL NL) (hA : PV A) (hy : (y : Equiv.Perm (Fin 55)) = mP A) :
    mEl LT TL VL NL A = y := by
  have h : InM LT TL VL NL A := ⟨hA, hy ▸ y.2⟩
  apply Subtype.ext
  rw [mEl_val h, hy]

theorem rc_eq {A : ℕ} (y : Mg LT TL VL NL) (hA : PV A) (hy : (y : Equiv.Perm (Fin 55)) = mP A) :
    rc φ A = φ y := by
  unfold rc
  rw [mEl_eq y hA hy]

theorem rc_one : rc φ ONEP = 1 := by
  rw [rc_eq φ 1 one_PV (by rw [mP_one]; rfl), map_one]

theorem rc_mul {A B : ℕ} (hA : InM LT TL VL NL A) (hB : InM LT TL VL NL B) :
    rc φ (mulP A B) = rc φ A * rc φ B := by
  have hAB := InM_mul hA hB
  rw [rc_eq φ (mEl LT TL VL NL A * mEl LT TL VL NL B) hAB.1 (by
    rw [Subgroup.coe_mul, mEl_val hA, mEl_val hB, mP_mul hA.1 hB.1]), map_mul]
  rfl

theorem rc_invR {A B : ℕ} (hA : InM LT TL VL NL A) (hB : PV B) (h : mulP A B = ONEP) :
    rc φ B = (rc φ A)⁻¹ := by
  have hB' := InM_invR hA hB h
  have e := rc_mul φ hA hB'
  rw [h, rc_one φ] at e
  exact (inv_eq_of_mul_eq_one_right e.symm).symm

include hL hφ

theorem rc_letter {c : ℕ} (hN : isN TL VL NL c = true) : rc φ (letP LT c) = x c := by
  rw [rc_eq φ ⟨_, Lm_mem hN⟩ (letter_PV hL hN) (Lm_val hN)]
  exact hφ c ⟨(isN_iff.1 hN).1, hN⟩

theorem rc_segProd (Wd o : ℕ) : ∀ m, ¬Cst (segProd LT TL VL NL Wd o m) →
    (∀ k < m, isN TL VL NL (byte Wd (o + k)) = true) ∧ InM LT TL VL NL (segProd LT TL VL NL Wd o m) ∧
      rc φ (segProd LT TL VL NL Wd o m) = ((List.range m).map fun k => x (byte Wd (o + k))).prod
  | 0, _ => ⟨fun k hk => absurd hk (Nat.not_lt_zero k), InM_one, rc_one φ⟩
  | m + 1, hne => by
    have hs : segProd LT TL VL NL Wd o (m + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (mulP (segProd LT TL VL NL Wd o m) (letP LT (byte Wd (o + m))))
        (isN TL VL NL (byte Wd (o + m))) := rfl
    rw [hs] at hne ⊢
    cases hN : isN TL VL NL (byte Wd (o + m))
    · rw [hN] at hne
      exact absurd cst_zero hne
    · rw [hN] at hne
      dsimp only at hne ⊢
      have hne' : ¬Cst (segProd LT TL VL NL Wd o m) := fun h0 => hne (cst_mul_left _ h0)
      obtain ⟨h1, h2, h3⟩ := rc_segProd Wd o m hne'
      refine ⟨fun k hk => ?_, InM_mul h2 (InM_letter hL hN), ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact h1 k hk
        · exact hN
      · rw [rc_mul φ h2 (InM_letter hL hN), h3, rc_letter hL φ hφ hN, List.range_succ,
          List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

end Rc

theorem relVisOK_spec {RR : ℕ → ℕ} {LT TL VL NL NR S P r s ns : ℕ}
    (h : relVisOK RR LT TL VL NL NR S P r s ns = true) :
    r < NR ∧ ns + 2 ≤ bits (RR r) 2 10 ∧
      byte (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) 0 = VL ∧
      byte (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) (ns + 1) = TL ∧
      S = segProd LT TL VL NL (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s) 1 ns ∧
      mulP P (segProd LT TL VL NL (CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) s)
        (ns + 2) (bits (RR r) 2 10 - (ns + 2))) = ONEP := by
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

variable (hL : LetOK LT LI TL VL NL) {x : ℕ → G}
  (φ : Mg LT TL VL NL →* G)
  (hφ : ∀ c (h : c ∈ Nset TL VL NL),
    φ ⟨Lm LT TL VL NL c, Subgroup.subset_closure ⟨c, h, rfl⟩⟩ = x c)
  {RR : ℕ → ℕ} {NR : ℕ} (hrels : ∀ r < NR, rval x (RR r) = 1)
  (hnorm : CFSG.Certificates.LCE.relsNorm RR NR = true) (hu : x VL = (x TL)⁻¹)
include hL hφ hrels hnorm hu

theorem relVis_sem {S P r s ns : ℕ} (h : relVisOK RR LT TL VL NL NR S P r s ns = true)
    (hS : InM LT TL VL NL S) (hP : validP P = true) :
    InM LT TL VL NL P ∧ (x TL)⁻¹ * rc φ S * x TL = rc φ P := by
  obtain ⟨hr, hn, h0, h1, eS, eP⟩ := relVisOK_spec h
  set n := bits (RR r) 2 10
  set Wd := CFSG.KC.Th.rot (Nat.shiftRight (RR r) 12) n s
  have hQne : ¬Cst (segProd LT TL VL NL Wd (ns + 2) (n - (ns + 2))) := fun h0' => by
    have := cst_mul_right (validP_spec hP) h0'
    rw [eP] at this
    exact not_cst one_PV this
  obtain ⟨-, hQ, vQ⟩ := rc_segProd hL φ hφ Wd (ns + 2) _ hQne
  have hSne : ¬Cst S := not_cst hS.1
  rw [eS] at hSne hS ⊢
  obtain ⟨-, -, vS⟩ := rc_segProd hL φ hφ Wd 1 ns hSne
  have hPm : InM LT TL VL NL P := InM_invL hQ (validP_spec hP) eP
  refine ⟨hPm, ?_⟩
  have hinv := rc_invR φ hPm hQ.1 eP
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
    ∀ e < nT, InM LT TL VL NL (tP TB e) ∧ (x TL)⁻¹ * rc φ (tS TB e) * x TL = rc φ (tP TB e) := by
  have htab := tab_mem hL hT hθ
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
      refine ⟨eP ▸ InM_mul pa pb, ?_⟩
      rw [eS, eP, rc_mul φ sa sb, rc_mul φ pa pb, ← ea, ← eb]
      group
    · exact relVis_sem hL φ hφ hrels hnorm hu hr (htab e he).1 hP

end Psi

end CFSG.Certificates.DSP

end
