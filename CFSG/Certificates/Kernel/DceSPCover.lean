module

import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.DceSPStep
public import Certificates.Data.Kernel.DceSP

public section

namespace CFSG.Certificates.DSP

open CFSG.KC.Loop CFSG.KC.HNA.DceS CFSG.Certificates.DceLoop CFSG.Certificates.DceWord
  CFSG.Certificates.DceTw
open scoped Classical

set_option exponentiation.threshold 400

variable {G : Type*} [Group G] {LT LI TL VL NL : ℕ}

theorem slotOK_spec {FB OB : ℕ → ℕ} {sh wd NF AL D w x : ℕ}
    (hs : slotOK FB OB sh wd NF AL D w x = true) :
    x >>> 1 < NF ∧
      ((rD (rec FB sh wd (x >>> 1)) = D ∧ rJ (rec FB sh wd (x >>> 1)) = w + 1 ∧
          AL.testBit (rDp (rec FB sh wd (x >>> 1))) = true) ∨
        (rDp (rec FB sh wd (x >>> 1)) = D ∧ 0 < rJ (rec FB sh wd (x >>> 1)) ∧
          AL.testBit (rD (rec FB sh wd (x >>> 1))) = true ∧
          actOK (pt OB w) (rPi (rec FB sh wd (x >>> 1)))
            (pt OB (rJ (rec FB sh wd (x >>> 1)) - 1)) = true)) := by
  unfold slotOK at hs
  beta_reduce at hs
  obtain ⟨e1, e2⟩ := andL_iff.1 hs
  refine ⟨Nat.blt_eq.mp e1, ?_⟩
  revert e2
  cases Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1)
  · intro e2
    obtain ⟨f1, r⟩ := andL_iff.1 e2
    obtain ⟨f2, f3⟩ := andL_iff.1 r
    exact Or.inl ⟨Nat.eq_of_beq_eq_true f1, Nat.eq_of_beq_eq_true f2, (aliveD_iff _ _).1 f3⟩
  · intro e2
    obtain ⟨f1, r⟩ := andL_iff.1 e2
    obtain ⟨f2, r⟩ := andL_iff.1 r
    obtain ⟨f3, f4⟩ := andL_iff.1 r
    exact Or.inr ⟨Nat.eq_of_beq_eq_true f1, Nat.blt_eq.mp f2, (aliveD_iff _ _).1 f3, f4⟩

theorem stabGen_spec (FB : ℕ → ℕ) (sh wd NF D SG s : ℕ) :
    stabGen FB sh wd NF D SG s = 0 ∨ ∃ g < NF, rD (rec FB sh wd g) = D ∧ rJ (rec FB sh wd g) = 0 ∧
      rDp (rec FB sh wd g) = D ∧ stabGen FB sh wd NF D SG s = rPi (rec FB sh wd g) := by
  unfold stabGen
  beta_reduce
  generalize bits SG (Nat.add (nat_lit 5) (Nat.mul (nat_lit 20) s)) (nat_lit 20) = g
  cases hc : andB (Nat.blt s (Nat.land SG (nat_lit 31))) (andB (Nat.blt g NF)
      (andB (Nat.beq (rD (rec FB sh wd g)) D) (andB (Nat.beq (rJ (rec FB sh wd g)) (nat_lit 0))
        (Nat.beq (rDp (rec FB sh wd g)) D))))
  · exact Or.inl rfl
  · obtain ⟨-, r⟩ := andL_iff.1 hc
    obtain ⟨f1, r⟩ := andL_iff.1 r
    obtain ⟨f2, r⟩ := andL_iff.1 r
    obtain ⟨f3, f4⟩ := andL_iff.1 r
    exact Or.inr ⟨g, Nat.blt_eq.mp f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3,
      Nat.eq_of_beq_eq_true f4, rfl⟩

theorem stabOne_spec {FB : ℕ → ℕ} {sh wd NF MD D : ℕ} {EB : ℕ → ℕ} {SG mD : ℕ} {C1 : List ℕ}
    {X0 X1 : ℕ} {C2 : List ℕ} {Y0 Y1 : ℕ}
    (h : stabOne FB sh wd NF MD (D, EB, SG, mD, C1, X0, X1, C2, Y0, Y1) = true) :
    mD = mDP MD D ∧ mat EB 0 = ONEP ∧ runStab FB EB sh wd NF D SG C1 2 = mD + 1 ∧
      runSorted (mat EB) 19 mD C2 1 = Y1 ∧ sortedCount Y1 = mD := by
  unfold stabOne at h
  obtain ⟨e1, r⟩ := andL_iff.1 h
  obtain ⟨e2, r⟩ := andL_iff.1 r
  obtain ⟨e3, r⟩ := andL_iff.1 r
  obtain ⟨e4, r⟩ := andL_iff.1 r
  obtain ⟨e5, r⟩ := andL_iff.1 r
  obtain ⟨e6, r⟩ := andL_iff.1 r
  obtain ⟨e7, e8⟩ := andL_iff.1 r
  have hX0 : X0 = 2 := Nat.eq_of_beq_eq_true e3
  have hY0 : Y0 = 1 := Nat.eq_of_beq_eq_true e6
  subst hX0 hY0
  refine ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, ?_, Nat.eq_of_beq_eq_true e7,
    Nat.eq_of_beq_eq_true e8⟩
  rw [Nat.eq_of_beq_eq_true e4, Nat.eq_of_beq_eq_true e5]

theorem stabAll_spec {FB : ℕ → ℕ} {sh wd NF MD : ℕ}
    {L : List (ℕ × ((ℕ → ℕ) × (ℕ × (ℕ × (List ℕ × (ℕ × (ℕ × (List ℕ × (ℕ × ℕ)))))))))}
    (h : stabAll FB sh wd NF MD L = true) : ∀ s ∈ L, stabOne FB sh wd NF MD s = true := by
  induction L with
  | nil => exact fun s hs => absurd hs (List.not_mem_nil)
  | cons s L ih =>
    intro s' hs'
    change andB (stabOne FB sh wd NF MD s) (stabAll FB sh wd NF MD L) = true at h
    obtain ⟨h1, h2⟩ := andL_iff.1 h
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact h1
    · exact ih h2 s' hs'

theorem stabHas_spec {D : ℕ}
    {L : List (ℕ × ((ℕ → ℕ) × (ℕ × (ℕ × (List ℕ × (ℕ × (ℕ × (List ℕ × (ℕ × ℕ)))))))))}
    (h : stabHas D L = true) : ∃ s ∈ L, s.1 = D := by
  induction L with
  | nil => exact absurd h Bool.false_ne_true
  | cons s L ih =>
    change orB (Prod.rec (motive := fun _ => Bool) (fun D' _ => Nat.beq D' D) s) (stabHas D L) = true at h
    rcases orL_iff.1 h with h1 | h1
    · exact ⟨s, List.mem_cons_self, Nat.eq_of_beq_eq_true h1⟩
    · obtain ⟨s', hs', e⟩ := ih h1
      exact ⟨s', List.mem_cons_of_mem _ hs', e⟩

theorem stabCover_spec {MD ND AL : ℕ}
    {L : List (ℕ × ((ℕ → ℕ) × (ℕ × (ℕ × (List ℕ × (ℕ × (ℕ × (List ℕ × (ℕ × ℕ)))))))))}
    (h : stabCover MD ND AL L = true) :
    ∀ D < ND, D ≠ 0 → AL.testBit D = true → mDP MD D = 1 ∨ ∃ s ∈ L, s.1 = D := by
  intro D hD hD0 hA
  have key : ∀ n, stabCover MD n AL L = true → ∀ D < n, D = 0 ∨ aliveD AL D = false ∨
      mDP MD D = 1 ∨ stabHas D L = true := by
    intro n
    induction n with
    | zero => exact fun _ D hD => absurd hD (Nat.not_lt_zero D)
    | succ n ih =>
      intro h D hD
      change andB (orB (Nat.beq n (nat_lit 0)) (orB (notB (aliveD AL n))
        (orB (Nat.beq (bits MD (Nat.mul (nat_lit 24) n) (nat_lit 24)) (nat_lit 1)) (stabHas n L))))
        (stabCover MD n AL L) = true at h
      obtain ⟨h1, h2⟩ := andL_iff.1 h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hD with hD | rfl
      · exact ih h2 D hD
      · rcases orL_iff.1 h1 with e | e
        · exact Or.inl (Nat.eq_of_beq_eq_true e)
        rcases orL_iff.1 e with e | e
        · exact Or.inr (Or.inl ((notL_eq _).1 e))
        rcases orL_iff.1 e with e | e
        · exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true e)))
        · exact Or.inr (Or.inr (Or.inr e))
  rcases key ND h D hD with e | e | e | e
  · exact absurd e hD0
  · rw [(aliveD_iff AL D).2 hA] at e
    exact absurd e (by decide)
  · exact Or.inl e
  · exact Or.inr (stabHas_spec e)

section Stab

variable {HB GB TB FB : ℕ → ℕ} {NO nT W Wi ND sh wd NF : ℕ} {x : ℕ → G}
  {φ : Mg LT TL VL NL →* G} (w : ℕ → G)
  (hfacts : ∀ i < NF, RecGood ND NO (rec FB sh wd i) ∧ InM LT TL VL NL (rPi (rec FB sh wd i)) ∧
    FM φ HB GB x w (rec FB sh wd i))
include hfacts

theorem stab_sem {MD D : ℕ} {EB : ℕ → ℕ} {SG mD : ℕ} {C1 : List ℕ} {X0 X1 : ℕ} {C2 : List ℕ}
    {Y0 Y1 : ℕ} (hs : stabOne FB sh wd NF MD (D, EB, SG, mD, C1, X0, X1, C2, Y0, Y1) = true) :
    mD = mDP MD D ∧ (∀ k < mD, InM LT TL VL NL (mat EB k) ∧
      w D * rc φ (mat EB k) * (w D)⁻¹ ∈ Ncl x TL VL NL) ∧
      ∀ k < mD, ∀ k' < mD, mat EB k = mat EB k' → k = k' := by
  obtain ⟨hm, h0, hrun, hsort, hcnt⟩ := stabOne_spec hs
  obtain ⟨hpos, hinj⟩ := sortRun_spec (runSorted_eq _ _ _ _ _ ▸ hsort) hcnt
  refine ⟨hm, ?_, hinj⟩
  rw [runStab_eq] at hrun
  have hi := cntRun_spec (a := 1) hrun
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0]
      refine ⟨InM_one, ?_⟩
      rw [rc_one φ, mul_one, mul_inv_cancel]
      exact (Ncl x TL VL NL).one_mem
    obtain ⟨J, hJ⟩ := hi k hk0 hk
    obtain ⟨e1, e2⟩ := andL_iff.1 hJ
    have hp : bits J 0 19 < k := Nat.blt_eq.mp e1
    have he : mat EB k = mulP (mat EB (bits J 0 19)) (stabGen FB sh wd NF D SG (bits J 19 5)) :=
      Nat.eq_of_beq_eq_true e2
    obtain ⟨mp, np⟩ := ih _ hp (by omega)
    rcases stabGen_spec FB sh wd NF D SG (bits J 19 5) with h0' | ⟨g, hg, gD, gJ, gDp, hgv⟩
    · rw [h0', mulP_zero_right] at he
      have := hpos k hk
      rw [he] at this
      exact absurd this (Nat.lt_irrefl 0)
    · obtain ⟨-, gm', gFM⟩ := hfacts g hg
      rw [hgv] at he
      rw [he]
      refine ⟨InM_mul mp gm', ?_⟩
      rw [rc_mul φ mp gm']
      unfold FM at gFM
      rw [gD, gJ, gDp, uv, ite_eq_left rfl, mul_one] at gFM
      unfold RelT at gFM
      have e3 : w D * (rc φ (mat EB (bits J 0 19)) * rc φ (rPi (rec FB sh wd g))) * (w D)⁻¹ =
          (w D * rc φ (mat EB (bits J 0 19)) * (w D)⁻¹) * (w D * (w D * rc φ (rPi (rec FB sh wd g)))⁻¹)⁻¹ := by
        group
      rw [e3]
      exact (Ncl x TL VL NL).mul_mem np ((Ncl x TL VL NL).inv_mem gFM)

end Stab

end CFSG.Certificates.DSP

end
