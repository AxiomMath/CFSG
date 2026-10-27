module

public import Certificates.Data.Kernel.TwoM22.Check
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.TwoM22

open CFSG.KC.Enum

theorem wordId_sound {n w m a b ai bi W len : Nat} (h : wordId n w m a b ai bi W len = true) :
    ∀ p < n, wpt w m a b ai bi W len p = p := fun p hp =>
  Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h p hp)

theorem relOK_sound {n w m a b ai bi : Nat} {ws : List (Nat × Nat)}
    (h : relOK n w m a b ai bi ws = true) :
    ∀ d ∈ ws, ∀ p < n, wpt w m a b ai bi d.1 d.2 p = p := by
  induction ws with
  | nil => intro d hd; cases hd
  | cons d ws ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (relOK n w m a b ai bi ws)
        (wordId n w m a b ai bi d.1 d.2) = true := h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    intro d' hd'
    rcases List.mem_cons.1 hd' with rfl | hd'
    · exact wordId_sound h1
    · exact ih h2 d' hd'

theorem conjOK_sound {n w m a b ai bi t x W len : Nat}
    (h : conjOK n w m a b ai bi t x W len = true) :
    ∀ p < n, pg w m t (pg w m x (pg w m t p)) = wpt w m a b ai bi W len p := fun p hp =>
  Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h p hp)

theorem wordEqOK_sound {n w m a b ai bi g W len : Nat}
    (h : wordEqOK n w m a b ai bi g W len = true) :
    ∀ p < n, pg w m g p = wpt w m a b ai bi W len p := fun p hp =>
  Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h p hp)

theorem wordMulOK_sound {n w m a b ai bi g W len s : Nat}
    (h : wordMulOK n w m a b ai bi g W len s = true) :
    ∀ p < n, pg w m g p = wpt w m a b ai bi W len (pg w m s p) := fun p hp =>
  Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h p hp)

theorem treeOK_sound {n w m a b tr : Nat} (hn : 0 < n) (h : treeOK n w m a b tr = true) :
    trDep tr 0 = 0 ∧ ∀ p < n, p ≠ 0 → trPar tr p < n ∧ trDep tr (trPar tr p) + 1 = trDep tr p ∧
      pg w m (if trLab tr p = 0 then a else b) (trPar tr p) = p := by
  refine ⟨?_, ?_⟩
  · have hs := CFSG.KS.allN_spec h 0 hn
    rw [Nat.beq_refl 0] at hs
    exact Nat.eq_of_beq_eq_true hs
  · intro p hp hpne
    have hs := CFSG.KS.allN_spec h p hp
    have hp0 : Nat.beq p 0 = false :=
      Bool.eq_false_iff.2 fun hb => hpne (Nat.eq_of_beq_eq_true hb)
    rw [hp0, CFSG.KS.PF.strictB_eqP] at hs
    obtain ⟨hpar, hrest⟩ := (CFSG.KS.bAnd_iff _ _).1 hs
    obtain ⟨hdep, hpg⟩ := (CFSG.KS.bAnd_iff _ _).1 hrest
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.blt_eq] at hpar
      exact hpar
    · have := Nat.eq_of_beq_eq_true hdep
      omega
    · have hpg' := Nat.eq_of_beq_eq_true hpg
      cases hlab : Nat.beq (trLab tr p) 0 with
      | true =>
        have hl : trLab tr p = 0 := Nat.eq_of_beq_eq_true hlab
        rw [if_pos hl]
        rw [hlab] at hpg'
        exact hpg'
      | false =>
        have hl : trLab tr p ≠ 0 := Nat.ne_of_beq_eq_false hlab
        rw [if_neg hl]
        rw [hlab] at hpg'
        exact hpg'

private theorem fix2_branch (a b c : Bool) :
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true false c) false b)
      (Bool.rec (motive := fun _ => Bool) c true b) a = true ↔
    (a = true ↔ (b = true ∨ c = true)) := by
  cases a <;> cases b <;> cases c <;> simp

theorem fix2OK_sound {n w m a b ai bi W len x0 x1 : Nat}
    (h : fix2OK n w m a b ai bi W len x0 x1 = true) :
    ∀ p < n, (wpt w m a b ai bi W len p = p ↔ p = x0 ∨ p = x1) := by
  intro p hp
  have hs := CFSG.KS.allN_spec h p hp
  have hb := (fix2_branch (Nat.beq (wpt w m a b ai bi W len p) p) (Nat.beq p x0)
    (Nat.beq p x1)).1 hs
  simp only [Nat.beq_eq] at hb
  exact hb

private theorem allFix_iff (w m a b ai bi : Nat) (ks : List (Nat × Nat)) (p : Nat) :
    allFix w m a b ai bi ks p = true ↔
      ∀ d ∈ ks, wpt w m a b ai bi d.1 d.2 p = p := by
  induction ks with
  | nil =>
    constructor
    · intro _ d hd
      cases hd
    · intro _; rfl
  | cons d ks ih =>
    have hstep : allFix w m a b ai bi (d :: ks) p =
        Bool.rec (motive := fun _ => Bool) false (allFix w m a b ai bi ks p)
          (Nat.beq (wpt w m a b ai bi d.1 d.2 p) p) := rfl
    rw [hstep, CFSG.KS.bAnd_iff]
    constructor
    · rintro ⟨h1, h2⟩ d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact Nat.eq_of_beq_eq_true h1
      · exact ih.1 h2 d' hd'
    · intro h
      refine ⟨?_, ih.2 fun d' hd' => h d' (List.mem_cons_of_mem d hd')⟩
      rw [Nat.beq_eq]
      exact h d List.mem_cons_self

private theorem fix1_branch (a b : Bool) :
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true false b) b a = true ↔
    (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp

theorem fix1OK_sound {n w m a b ai bi : Nat} {ks : List (Nat × Nat)} {x0 : Nat}
    (h : fix1OK n w m a b ai bi ks x0 = true) :
    ∀ p < n, ((∀ d ∈ ks, wpt w m a b ai bi d.1 d.2 p = p) ↔ p = x0) := by
  intro p hp
  have hs := CFSG.KS.allN_spec h p hp
  have hb := (fix1_branch (allFix w m a b ai bi ks p) (Nat.beq p x0)).1 hs
  simp only [Nat.beq_eq, allFix_iff] at hb
  exact hb

theorem recRange_sound {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL : Nat}
    (h : ∀ c < 8, recRange F G G22 a b ai bi zW zL (64 * c) 64 = true) :
    ∀ k < 512, recOK F G G22 a b ai bi zW zL k = true := by
  intro k hk
  have hc : k / 64 < 8 := by omega
  have hj : k % 64 < 64 := Nat.mod_lt k (by omega)
  have hspec := CFSG.KS.allN_spec (h (k / 64) hc) (k % 64) hj
  have hk' : (64 * (k / 64)).add (k % 64) = k := Nat.div_add_mod k 64
  rw [hk'] at hspec
  exact hspec

private theorem land_pow_shr (x w : Nat) : (x &&& (2 ^ w - 1)) >>> w = 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))

private theorem pm660_eq : pm660 = 2 ^ 6600 - 1 := by
  change (1 <<< 6600) - 1 = 2 ^ 6600 - 1
  rw [Nat.one_shiftLeft]

private theorem rE_shr (F : Nat → Nat) (k : Nat) : rE F k >>> (660 * 10) = 0 := by
  have h := land_pow_shr (F k) 6600
  rw [← pm660_eq] at h
  exact h

private theorem beq_zero_eq_false {a : Nat} (h : a ≠ 0) :
    Nat.beq a (nat_lit 0) = false := by
  cases hb : Nat.beq a (nat_lit 0) with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem nIf_beq_eq_ite (a b : Nat) :
    nIf(Nat.beq a b, nat_lit 1, nat_lit 0) = if a = b then 1 else 0 := by
  cases hb : Nat.beq a b with
  | false => rw [if_neg (Nat.ne_of_beq_eq_false hb)]
  | true => rw [if_pos (Nat.eq_of_beq_eq_true hb)]

private theorem recOK_step {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL k : Nat}
    (h : recOK F G G22 a b ai bi zW zL k = true)
    (hk : Nat.beq k (nat_lit 0) = false) :
    Nat.blt (rE F (Nat.sub k (nat_lit 1))) (rE F k) = true := by
  unfold recOK at h
  simp only [CFSG.KS.PF.strictB_eqP, CFSG.KS.bAnd_iff] at h
  have h1 := h.1
  rw [hk] at h1
  exact h1

private theorem recOK_clos {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL k : Nat}
    (h : recOK F G G22 a b ai bi zW zL k = true) :
    closOK F G G22 k (rE F k) (rE22 F k) (nat_lit 5) = true := by
  unfold recOK at h
  simp only [CFSG.KS.PF.strictB_eqP, CFSG.KS.bAnd_iff] at h
  exact h.2.1

private theorem recOK_root {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL k : Nat}
    (h : recOK F G G22 a b ai bi zW zL k = true)
    (hd : Nat.beq (rDep F k) (nat_lit 0) = true) :
    Nat.beq (rE F k) (pidn (nat_lit 660) (nat_lit 10)) = true ∧
      Nat.beq (rE22 F k) (pidn (nat_lit 22) (nat_lit 5)) = true ∧
      Nat.beq (rOdd F k) (nat_lit 0) = true := by
  unfold recOK at h
  simp only [CFSG.KS.PF.strictB_eqP, CFSG.KS.bAnd_iff] at h
  have h3 := h.2.2.1
  rw [hd] at h3
  have h3' : bAnd(Nat.beq (rE F k) (pidn (nat_lit 660) (nat_lit 10)),
      bAnd(Nat.beq (rE22 F k) (pidn (nat_lit 22) (nat_lit 5)),
        Nat.beq (rOdd F k) (nat_lit 0))) = true := h3
  simp only [CFSG.KS.bAnd_iff] at h3'
  exact h3'

private theorem recOK_nonroot {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL k : Nat}
    (h : recOK F G G22 a b ai bi zW zL k = true)
    (hd : Nat.beq (rDep F k) (nat_lit 0) = false) :
    Nat.blt (rPar F k) (nat_lit 512) = true ∧
      Nat.blt (rLab F k) (nat_lit 5) = true ∧
      Nat.beq (Nat.succ (rDep F (rPar F k))) (rDep F k) = true ∧
      Nat.beq (rR F (rPar F k) (rLab F k)) k = true ∧
      Nat.beq (rOdd F k) (Nat.xor (rOdd F (rPar F k))
        (nIf(Nat.beq (rLab F k) (nat_lit 4), nat_lit 1, nat_lit 0))) = true := by
  unfold recOK at h
  simp only [CFSG.KS.PF.strictB_eqP, CFSG.KS.bAnd_iff] at h
  have h3 := h.2.2.1
  rw [hd] at h3
  have h3' : bAnd(Nat.blt (rPar F k) (nat_lit 512),
      bAnd(Nat.blt (rLab F k) (nat_lit 5),
        bAnd(Nat.beq (Nat.succ (rDep F (rPar F k))) (rDep F k),
          bAnd(Nat.beq (rR F (rPar F k) (rLab F k)) k,
            Nat.beq (rOdd F k) (Nat.xor (rOdd F (rPar F k))
              (nIf(Nat.beq (rLab F k) (nat_lit 4), nat_lit 1, nat_lit 0))))))) = true := h3
  simp only [CFSG.KS.bAnd_iff] at h3'
  exact h3'

private theorem recOK_odd {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL k : Nat}
    (h : recOK F G G22 a b ai bi zW zL k = true)
    (ho : Nat.beq (rOdd F k) (nat_lit 0) = false) :
    Nat.blt (rPt F k) (nat_lit 660) = true ∧
      Nat.beq (pg (nat_lit 10) (nat_lit 1023) (rE F k)
          (pg (nat_lit 10) (nat_lit 1023) (rE F k) (rPt F k)))
        (wpt (nat_lit 10) (nat_lit 1023) a b ai bi zW zL (rPt F k)) = false := by
  unfold recOK at h
  simp only [CFSG.KS.PF.strictB_eqP, CFSG.KS.bAnd_iff] at h
  have h4 := h.2.2.2
  rw [ho] at h4
  have h4s : bAnd(Nat.blt (rPt F k) (nat_lit 660),
      bIf(Nat.beq (pg (nat_lit 10) (nat_lit 1023) (rE F k)
          (pg (nat_lit 10) (nat_lit 1023) (rE F k) (rPt F k)))
        (wpt (nat_lit 10) (nat_lit 1023) a b ai bi zW zL (rPt F k)), false, true)) = true := h4
  simp only [CFSG.KS.bAnd_iff] at h4s
  refine ⟨h4s.1, ?_⟩
  cases hc : Nat.beq (pg (nat_lit 10) (nat_lit 1023) (rE F k)
      (pg (nat_lit 10) (nat_lit 1023) (rE F k) (rPt F k)))
      (wpt (nat_lit 10) (nat_lit 1023) a b ai bi zW zL (rPt F k)) with
  | false => rfl
  | true =>
      simp only [hc] at h4s
      exact (Bool.false_ne_true h4s.2).elim

private theorem closOK_succ (F : Nat → Nat) (G G22 : List Nat) (k e e22 g : Nat) :
    closOK F G G22 k e e22 (Nat.succ g) =
      bAnd(strictB (rR F k g) (fun R => bAnd(Nat.blt R 512,
        bAnd(Nat.beq (pcomp 660 10 1023 e (G.getD g 0)) (rE F R),
          Nat.beq (pcomp 22 5 31 e22 (G22.getD g 0)) (rE22 F R)))),
        closOK F G G22 k e e22 g) := rfl

private theorem closOK_spec {F : Nat → Nat} {G G22 : List Nat} {k e e22 g : Nat}
    (h : closOK F G G22 k e e22 g = true) :
    ∀ j < g, rR F k j < 512 ∧
      pcomp 660 10 (CFSG.KS.mask 10) e (G.getD j 0) = rE F (rR F k j) ∧
      pcomp 22 5 (CFSG.KS.mask 5) e22 (G22.getD j 0) = rE22 F (rR F k j) := by
  induction g with
  | zero =>
      intro j hj
      omega
  | succ g ih =>
      intro j hj
      rw [closOK_succ, CFSG.KS.bAnd_iff] at h
      obtain ⟨h1, h2⟩ := h
      simp only [CFSG.KS.PF.strictB_eqP] at h1
      rw [CFSG.KS.bAnd_iff] at h1
      obtain ⟨hA, h1⟩ := h1
      rw [CFSG.KS.bAnd_iff] at h1
      obtain ⟨hB, hC⟩ := h1
      rcases Nat.lt_or_ge j g with hj' | hj'
      · exact ih h2 j hj'
      · have hje : j = g := by omega
        subst hje
        exact ⟨Nat.blt_eq.mp hA, Nat.eq_of_beq_eq_true hB, Nat.eq_of_beq_eq_true hC⟩

private theorem lt_of_succ_lt_rec {f : Nat → Nat} {n : Nat}
    (hs : ∀ i, i + 1 < n → f i < f (i + 1)) :
    ∀ {i j : Nat}, i < j → j < n → f i < f j
  | _, 0, h, _ => absurd h (Nat.not_lt_zero _)
  | i, j + 1, h, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact Nat.lt_trans (lt_of_succ_lt_rec hs h (by omega)) (hs j hj)
    · exact hs i hj

private theorem rE_inj {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL : Nat}
    (h : ∀ k < 512, recOK F G G22 a b ai bi zW zL k = true)
    {k l : Nat} (hk : k < 512) (hl : l < 512) (he : rE F k = rE F l) : k = l := by
  have hs : ∀ i, i + 1 < 512 → rE F i < rE F (i + 1) := by
    intro i hi
    exact Nat.blt_eq.mp (recOK_step (h (i + 1) hi) (beq_zero_eq_false (by omega)))
  have hmono : ∀ {i j : Nat}, i < j → j < 512 → rE F i < rE F j :=
    lt_of_succ_lt_rec (f := rE F) (n := 512) hs
  rcases Nat.lt_trichotomy k l with hlt | heq | hgt
  · have := hmono hlt hl
    omega
  · exact heq
  · have := hmono hgt hk
    omega

theorem recOK_sound {F : Nat → Nat} {G G22 : List Nat} {a b ai bi zW zL : Nat}
    (h : ∀ k < 512, recOK F G G22 a b ai bi zW zL k = true) :
    (∀ k < 512, ∀ l < 512, k ≠ l → ∃ i < 660, pg 10 1023 (rE F k) i ≠ pg 10 1023 (rE F l) i) ∧
    (∀ k < 512, ∀ g < 5, rR F k g < 512 ∧
      (∀ i < 660,
        pg 10 1023 (rE F (rR F k g)) i = pg 10 1023 (rE F k) (pg 10 1023 (G.getD g 0) i)) ∧
      (∀ i < 22, pg 5 31 (rE22 F (rR F k g)) i = pg 5 31 (rE22 F k) (pg 5 31 (G22.getD g 0) i))) ∧
    (∀ k < 512, rDep F k = 0 → (∀ i < 660, pg 10 1023 (rE F k) i = i) ∧
      (∀ i < 22, pg 5 31 (rE22 F k) i = i) ∧ rOdd F k = 0) ∧
    (∀ k < 512, rDep F k ≠ 0 → rPar F k < 512 ∧ rLab F k < 5 ∧
      rDep F (rPar F k) + 1 = rDep F k ∧ rR F (rPar F k) (rLab F k) = k ∧
      rOdd F k = rOdd F (rPar F k) ^^^ (if rLab F k = 4 then 1 else 0)) ∧
    (∀ k < 512, rOdd F k ≠ 0 → rPt F k < 660 ∧
      pg 10 1023 (rE F k) (pg 10 1023 (rE F k) (rPt F k)) ≠
        wpt 10 1023 a b ai bi zW zL (rPt F k)) := by
  have hdist : ∀ k < 512, ∀ l < 512, k ≠ l →
      ∃ i < 660, pg 10 1023 (rE F k) i ≠ pg 10 1023 (rE F l) i := by
    intro k hk l hl hne
    apply Classical.byContradiction
    intro hall
    have hall' : ∀ i, i < 660 → pg 10 1023 (rE F k) i = pg 10 1023 (rE F l) i := by
      intro i hi
      apply Classical.byContradiction
      intro hne'
      exact hall ⟨i, hi, hne'⟩
    have heq : rE F k = rE F l :=
      CFSG.KS.PF.eq_of_fields (n := 660) (w := 10) (p := rE F k) (q := rE F l)
        (by omega) (rE_shr F k) (rE_shr F l) hall'
    exact hne (rE_inj h hk hl heq)
  refine ⟨hdist, ?_, ?_, ?_, ?_⟩
  · intro k hk g hg
    have hclos := recOK_clos (h k hk)
    obtain ⟨hR, he1, he2⟩ := closOK_spec hclos g hg
    refine ⟨hR, ?_, ?_⟩
    · intro i hi
      have hp := CFSG.KS.PF.pg_pcomp (n := 660) (w := 10)
        (p := rE F k) (q := G.getD g 0) (i := i) (by decide) hi
      rw [he1] at hp
      exact hp
    · intro i hi
      have hp := CFSG.KS.PF.pg_pcomp (n := 22) (w := 5)
        (p := rE22 F k) (q := G22.getD g 0) (i := i) (by decide) hi
      rw [he2] at hp
      exact hp
  · intro k hk hd
    have hb : Nat.beq (rDep F k) (nat_lit 0) = true := by
      rw [hd]
      rfl
    obtain ⟨he, he22, ho⟩ := recOK_root (h k hk) hb
    have he' : rE F k = pidn 660 10 := Nat.eq_of_beq_eq_true he
    have he22' : rE22 F k = pidn 22 5 := Nat.eq_of_beq_eq_true he22
    refine ⟨?_, ?_, Nat.eq_of_beq_eq_true ho⟩
    · intro i hi
      rw [he']
      exact CFSG.KS.PF.pg_pidn (n := 660) (w := 10) (by decide) (by decide) hi
    · intro i hi
      rw [he22']
      exact CFSG.KS.PF.pg_pidn (n := 22) (w := 5) (by decide) (by decide) hi
  · intro k hk hd
    have hb : Nat.beq (rDep F k) (nat_lit 0) = false := beq_zero_eq_false hd
    obtain ⟨hpar, hlab, hdep, hrR, hodd⟩ := recOK_nonroot (h k hk) hb
    have hpar' : rPar F k < 512 := Nat.blt_eq.mp hpar
    have hlab' : rLab F k < 5 := Nat.blt_eq.mp hlab
    have hdep' : rDep F (rPar F k) + 1 = rDep F k := Nat.eq_of_beq_eq_true hdep
    have hrR' : rR F (rPar F k) (rLab F k) = k := Nat.eq_of_beq_eq_true hrR
    have hodd' : rOdd F k = Nat.xor (rOdd F (rPar F k))
        (nIf(Nat.beq (rLab F k) (nat_lit 4), nat_lit 1, nat_lit 0)) :=
      Nat.eq_of_beq_eq_true hodd
    refine ⟨hpar', hlab', hdep', hrR', ?_⟩
    rw [nIf_beq_eq_ite] at hodd'
    exact hodd'
  · intro k hk ho
    have hb : Nat.beq (rOdd F k) (nat_lit 0) = false := beq_zero_eq_false ho
    obtain ⟨hx, hne⟩ := recOK_odd (h k hk) hb
    exact ⟨Nat.blt_eq.mp hx, Nat.ne_of_beq_eq_false hne⟩

end CFSG.KC.TwoM22

end
