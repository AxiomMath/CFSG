module

public import Certificates.Data.Kernel.Spor.RawSchF
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.RawSchPSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

section Abstract

variable {n : Nat} (β : Nat → Fin n) (c : Nat → Nat) (pos : Nat → Fin n → Nat)
  (TK : Nat → Nat → Equiv.Perm (Fin n))

def fwSift : Nat → Nat → Equiv.Perm (Fin n) → Prop
  | 0, _, g => g = 1
  | d + 1, l, g => pos l (g (β l)) < c l ∧ fwSift d (l + 1) ((TK l (pos l (g (β l))))⁻¹ * g)

theorem fwSift_zero (l : Nat) (g : Equiv.Perm (Fin n)) : fwSift β c pos TK 0 l g ↔ g = 1 :=
  Iff.rfl

theorem fwSift_succ (d l : Nat) (g : Equiv.Perm (Fin n)) : fwSift β c pos TK (d + 1) l g ↔
    pos l (g (β l)) < c l ∧ fwSift β c pos TK d (l + 1) ((TK l (pos l (g (β l))))⁻¹ * g) :=
  Iff.rfl

theorem fwSift_iff {nb : Nat} {Γ : Nat → Set (Equiv.Perm (Fin n))}
    (hpt : ∀ l < nb, ∀ k < c l, pos l (TK l k (β l)) = k)
    (hc0 : ∀ l < nb, 0 < c l) (hT0 : ∀ l < nb, TK l 0 = 1)
    (hTm : ∀ l < nb, ∀ k < c l, TK l k ∈ Subgroup.closure (Γ l))
    (hmono : ∀ l < nb, Γ (l + 1) ⊆ Γ l)
    (hfix : ∀ l < nb, ∀ g ∈ Γ (l + 1), g (β l) = β l)
    (hbot : ∀ g ∈ Γ nb, g = 1)
    (hfwd : ∀ l < nb, ∀ s ∈ Γ l, ∀ h < c l, fwSift β c pos TK (nb - l) l (s * TK l h)) :
    ∀ d l, l + d = nb → ∀ g, fwSift β c pos TK d l g ↔ g ∈ Subgroup.closure (Γ l) := by
  intro d
  induction d with
  | zero =>
    intro l hl g
    have hl' : l = nb := by omega
    subst hl'
    have e : Subgroup.closure (Γ l) = ⊥ :=
      Subgroup.closure_eq_bot_iff.2 fun x hx => Set.mem_singleton_iff.2 (hbot x hx)
    rw [fwSift_zero, e, Subgroup.mem_bot]
  | succ d ih =>
    intro l hl g
    have hlt : l < nb := by omega
    have IH := ih (l + 1) (by omega)
    have hHK : Subgroup.closure (Γ (l + 1)) ≤ Subgroup.closure (Γ l) :=
      Subgroup.closure_mono (hmono l hlt)
    have hle : Subgroup.closure (Γ (l + 1)) ≤ MulAction.stabilizer (Equiv.Perm (Fin n)) (β l) :=
      (Subgroup.closure_le _).2 fun x hx => by
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
        exact hfix l hlt x hx
    have hHfix : ∀ a ∈ Subgroup.closure (Γ (l + 1)), a (β l) = β l := fun a ha => by
      have h1 := hle ha
      rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h1
    have key : ∀ k < c l, ∀ a ∈ Subgroup.closure (Γ (l + 1)),
        fwSift β c pos TK (d + 1) l (TK l k * a) := by
      intro k hk a ha
      rw [fwSift_succ, Equiv.Perm.mul_apply, hHfix a ha, hpt l hlt k hk, inv_mul_cancel_left]
      exact ⟨hk, (IH a).2 ha⟩
    have dest : ∀ x, fwSift β c pos TK (d + 1) l x →
        ∃ k < c l, ∃ a ∈ Subgroup.closure (Γ (l + 1)), x = TK l k * a := by
      intro x hx
      rw [fwSift_succ] at hx
      exact ⟨_, hx.1, _, (IH _).1 hx.2, (mul_inv_cancel_left _ _).symm⟩
    constructor
    · intro hg
      obtain ⟨k, hk, a, ha, rfl⟩ := dest g hg
      exact Subgroup.mul_mem _ (hTm l hlt k hk) (hHK ha)
    · intro hg
      have hstep : ∀ s ∈ Γ l, ∀ x, fwSift β c pos TK (d + 1) l x →
          fwSift β c pos TK (d + 1) l (s * x) := by
        intro s hs x hx
        obtain ⟨k, hk, a, ha, rfl⟩ := dest x hx
        have hf := hfwd l hlt s hs k hk
        have e : nb - l = d + 1 := by omega
        rw [e] at hf
        obtain ⟨k', hk', b, hb, e'⟩ := dest _ hf
        rw [← mul_assoc, e', mul_assoc]
        exact key k' hk' _ (Subgroup.mul_mem _ hb ha)
      have hpow : ∀ s ∈ Γ l, ∀ m x, fwSift β c pos TK (d + 1) l x →
          fwSift β c pos TK (d + 1) l (s ^ m * x) := by
        intro s hs m
        induction m with
        | zero =>
          intro x hx
          rwa [pow_zero, one_mul]
        | succ m ihm =>
          intro x hx
          rw [pow_succ', mul_assoc]
          exact hstep s hs _ (ihm x hx)
      induction hg using Subgroup.closure_induction_left with
      | one =>
        have h1 := key 0 (hc0 l hlt) 1 (Subgroup.one_mem _)
        rwa [hT0 l hlt, mul_one] at h1
      | mul_left x hx y _ ihy => exact hstep x hx y ihy
      | inv_mul_cancel x hx y _ ihy =>
        have e : x⁻¹ = x ^ (orderOf x - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos x),
            pow_orderOf_eq_one]
        rw [e]
        exact hpow x hx _ y ihy

end Abstract

@[expose] noncomputable def fwG (n w : Nat) (PS : Nat → Nat) (j : Nat) : Equiv.Perm (Fin n) :=
  permOfArr n (unpack n w (PS j))

@[expose] noncomputable def fwT (n w : Nat) (LR TR : Nat → Nat) (l k : Nat) :
    Equiv.Perm (Fin n) :=
  permOfArr n (unpack n w (TR (roff n (n * w) (LR l) + k)))

@[expose] def fwGens (n w : Nat) (PS : Nat → Nat) (kS BP l : Nat) : Set (Equiv.Perm (Fin n)) :=
  {g | ∃ j < kS, fxK w PS BP l j = true ∧ g = fwG n w PS j}

@[expose] noncomputable def fwB {n : Nat} (hn : 0 < n) (w BP : Nat) (l : Nat) : Fin n :=
  toF hn (pg w (mask w) BP l)

@[expose] noncomputable def fwPos (n w : Nat) (LR : Nat → Nat) (l : Nat) (x : Fin n) : Nat :=
  rpos w (mask w) (n * w) (LR l) x

theorem fwB_val {n w BP l : Nat} (hn : 0 < n) (h : pg w (mask w) BP l < n) :
    (fwB hn w BP l : Nat) = pg w (mask w) BP l := by
  unfold fwB
  rw [toF_eq hn h]

theorem prep_fwG {n w kS : Nat} {PS PSI : Nat → Nat}
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) {j : Nat}
    (hj : j < kS) : PRep n w (PS j) (fwG n w PS j) ∧ PRep n w (PSI j) (fwG n w PS j)⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack (allN_iff.1 hp j hj))
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem stCnt_mod (T : Nat) : stCnt T = T % 256 := by
  unfold stCnt
  change T &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem fwdT_eq (T : Nat) : fwdT T = T / 256 * 256 + T % 256 / 2 := by
  have e : Nat.shiftRight (stCnt T) (nat_lit 1) = T % 256 / 2 := by
    rw [stCnt_mod, shr_eq]
    rfl
  unfold fwdT
  rw [e, stCnt_mod, Nat.sub_eq, Nat.sub_eq]
  omega

theorem stCnt_fwdT (T : Nat) : stCnt (fwdT T) = stCnt T / 2 := by
  rw [stCnt_mod, stCnt_mod, fwdT_eq]
  omega

theorem stAt_fwdT (T j : Nat) : stAt (fwdT T) j = stAt T j := by
  have e : ∀ X : Nat, Nat.shiftRight X (Nat.add 8 (Nat.mul 8 j)) =
      X / 256 / 2 ^ (8 * j) := fun X => by
    rw [shr_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  have e2 : (T / 256 * 256 + T % 256 / 2) / 256 = T / 256 := by omega
  unfold stAt
  rw [e, e, fwdT_eq, e2]

theorem fw_letter {n w kS BP l : Nat} {PS PSI : Nat → Nat} (hk : kS < 128)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) :
    ∀ j < stCnt (stepsAt n w PS kS BP l), ∃ ℓ ∈ Subgroup.closure (fwGens n w PS kS BP l),
      PRep n w (letterK PS PSI kS (stAt (stepsAt n w PS kS BP l) j)) ℓ := by
  intro j hj
  have hk2 : kS + kS < 256 := by omega
  have hT : stepsAt n w PS kS BP l = stepTab kS (fixMaskK w (mask w) PS kS BP l) := rfl
  rw [hT, stCnt_eq hk2] at hj
  rw [hT, stAt_eq hk2 hj]
  have hmem := List.getElem_mem hj
  rw [List.mem_filter, List.mem_range] at hmem
  obtain ⟨hx2, htab⟩ := hmem
  generalize ((List.range (kS + kS)).filter (tabP kS (fixMaskK w (mask w) PS kS BP l)))[j] = x
    at hx2 htab ⊢
  unfold tabP at htab
  rw [hasBit_eq] at htab
  by_cases hxk : x < kS
  · rw [if_pos hxk, fixMask_testBit] at htab
    simp only [hxk, decide_true, Bool.true_and] at htab
    have hL : letterK PS PSI kS x = PS x := by
      unfold letterK
      rw [nIf_eq, blt_dec]
      simp [hxk]
    rw [hL]
    exact ⟨_, Subgroup.subset_closure ⟨x, hxk, htab, rfl⟩, (prep_fwG hp hxk).1⟩
  · have hx' : x - kS < kS := by omega
    rw [if_neg hxk, fixMask_testBit, Nat.sub_eq] at htab
    simp only [hx', decide_true, Bool.true_and] at htab
    have hL : letterK PS PSI kS x = PSI (x - kS) := by
      unfold letterK
      rw [nIf_eq, blt_dec]
      simp [hxk, Nat.sub_eq]
    rw [hL]
    exact ⟨_, Subgroup.inv_mem _ (Subgroup.subset_closure ⟨x - kS, hx', htab, rfl⟩),
      (prep_fwG hp hx').2⟩

theorem fw_cover {n w kS BP l : Nat} {PS PSI : Nat → Nat} (hk : kS < 128) {g : Nat} (hg : g < kS)
    (hf : fxK w PS BP l g = true) :
    ∃ j < stCnt (fwdT (stepsAt n w PS kS BP l)),
      letterK PS PSI kS (stAt (fwdT (stepsAt n w PS kS BP l)) j) = PS g := by
  have hk2 : kS + kS < 256 := by omega
  have hsplit := tab_split (M := fixMaskK w (mask w) PS kS BP l) (f := fxK w PS BP l)
    fixMask_testBit
  have hT : stepsAt n w PS kS BP l = stepTab kS (fixMaskK w (mask w) PS kS BP l) := rfl
  set idx := (List.range kS).filter (fxK w PS BP l) with hidx
  have hgi : g ∈ idx := by
    rw [hidx, List.mem_filter, List.mem_range]
    exact ⟨hg, hf⟩
  obtain ⟨j, hj, hjg⟩ := List.mem_iff_getElem.1 hgi
  have hlen : stCnt (stepTab kS (fixMaskK w (mask w) PS kS BP l)) = idx.length + idx.length := by
    rw [stCnt_eq hk2, hsplit]
    simp
  have hjL : j < ((List.range (kS + kS)).filter (tabP kS (fixMaskK w (mask w) PS kS BP l))).length := by
    rw [hsplit]
    simp
    omega
  refine ⟨j, ?_, ?_⟩
  · rw [stCnt_fwdT, hT, hlen]
    omega
  · rw [stAt_fwdT, hT, stAt_eq hk2 hjL]
    simp only [hsplit]
    rw [List.getElem_append_left hj, hjg]
    unfold letterK
    rw [nIf_eq, blt_dec]
    simp [hg]

theorem fw_level {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {l : Nat} (hl' : l < nb) :
    0 < rcnt (LR l) ∧ rcnt (LR l) ≤ n ∧ pg w (mask w) BP l < n ∧
    (∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (fwT n w LR TR l k) ∧
      PRep n w (TRI (roff n (n * w) (LR l) + k)) (fwT n w LR TR l k)⁻¹) ∧
    fwT n w LR TR l 0 = 1 ∧
    ∀ k < rcnt (LR l), pg w (mask w) (TR (roff n (n * w) (LR l) + k)) (pg w (mask w) BP l) =
      rpt w (mask w) (LR l) k ∧ rpos w (mask w) (n * w) (LR l) (rpt w (mask w) (LR l) k) = k ∧
      fwT n w LR TR l k ∈ Subgroup.closure (fwGens n w PS kS BP l) := by
  have hL := hl l hl'
  obtain ⟨hsz, hk, hR, h0, hst, hperm⟩ := levelK_facts hL
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hcn : rcnt (LR l) ≤ n := by
    unfold levelK at hL
    rw [strictB_eq, strictB_eq, strictB_eq] at hL
    obtain ⟨_, hL⟩ := (bAnd_iff _ _).1 hL
    obtain ⟨_, hL⟩ := (bAnd_iff _ _).1 hL
    obtain ⟨_, hL⟩ := (bAnd_iff _ _).1 hL
    obtain ⟨h4, _⟩ := (bAnd_iff _ _).1 hL
    exact Nat.le_of_ble_eq_true h4
  have hTK : ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (fwT n w LR TR l k) ∧
      PRep n w (TRI (roff n (n * w) (LR l) + k)) (fwT n w LR TR l k)⁻¹ := fun k hk => by
    have hr := rep_permOfArr (isInvA_unpack (hperm k hk))
    exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩
  have hroot : pg w (mask w) BP l < n := hR.root ▸ (hR.pt 0 hR.c_pos).1
  have hT0 : fwT n w LR TR l 0 = 1 := by
    have e := (hTK 0 hR.c_pos).1
    rw [Nat.add_zero, h0] at e
    exact prep_unique e (prep_pidn hn24 hw)
  have main : ∀ k, k < rcnt (LR l) →
      pg w (mask w) (TR (roff n (n * w) (LR l) + k)) (pg w (mask w) BP l) =
        rpt w (mask w) (LR l) k ∧ fwT n w LR TR l k ∈ Subgroup.closure (fwGens n w PS kS BP l) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkc
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [hT0, Nat.add_zero, h0, PF.pg_pidn hn24 hw hroot, hR.root]
        exact ⟨rfl, Subgroup.one_mem _⟩
      · have hpk := hR.par_lt k hkc hk0
        have hlk := hR.lab_lt k hkc hk0
        obtain ⟨ℓ, hℓ, hPℓ⟩ := fw_letter hk hp _ hlk
        have e2 := hst k hkc hk0
        unfold eq2 at e2
        have e3 : ∀ x : Fin n, pg w (mask w) (TR (roff n (n * w) (LR l) + k)) x =
            pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP l)
              (rlab n (n * w) (LR l) k)))
              (pg w (mask w) (TR (roff n (n * w) (LR l) + rpar w (mask w) (n * w) (LR l) k)) x) :=
          fun x => Nat.eq_of_beq_eq_true (allN_spec e2 x x.2)
        obtain ⟨ihr, ihm⟩ := ih _ hpk (by omega)
        have eT : fwT n w LR TR l k = ℓ * fwT n w LR TR l (rpar w (mask w) (n * w) (LR l) k) :=
          Equiv.ext fun x => Fin.ext (by
            rw [Equiv.Perm.mul_apply, ← (hTK k hkc).1 x, e3 x, (hTK _ (by omega)).1 x, hPℓ])
        refine ⟨?_, ?_⟩
        · have e4 : pg w (mask w) (TR (roff n (n * w) (LR l) + k)) (pg w (mask w) BP l) =
              pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP l)
                (rlab n (n * w) (LR l) k)))
                (pg w (mask w) (TR (roff n (n * w) (LR l) + rpar w (mask w) (n * w) (LR l) k))
                  (pg w (mask w) BP l)) := e3 ⟨_, hroot⟩
          rw [e4, ihr]
          exact hR.edge k hkc hk0
        · rw [eT]
          exact Subgroup.mul_mem _ hℓ ihm
  exact ⟨hR.c_pos, hcn, hroot, hTK, hT0, fun k hk => ⟨(main k hk).1, (hR.pt k hk).2, (main k hk).2⟩⟩

theorem fw_apply {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} (hn : 0 < n)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {l : Nat} (hlt : l < nb) {h : Nat}
    (hh : h < rcnt (LR l)) {L : Nat} {ℓ : Equiv.Perm (Fin n)} (hL : PRep n w L ℓ) :
    ((ℓ * fwT n w LR TR l h) (fwB hn w BP l) : Nat) =
      pg w (mask w) L (rpt w (mask w) (LR l) h) := by
  obtain ⟨_, _, hroot, hTK, _, hpts⟩ := fw_level hp hl hlt
  rw [Equiv.Perm.mul_apply, ← hL, ← (hTK h hh).1, fwB_val hn hroot, (hpts h hh).1]

theorem fwSift_of_siftK {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} (hn : 0 < n)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) :
    ∀ d l, l + d = nb → ∀ (G : Nat) (γ : Equiv.Perm (Fin n)), PRep n w G γ →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true →
      fwSift (fwB hn w BP) (fun l => rcnt (LR l)) (fwPos n w LR) (fwT n w LR TR) d l γ := by
  intro d
  induction d with
  | zero =>
    intro l _ G γ hG h
    rw [siftK_zero] at h
    obtain ⟨hs, he⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hn24, hw⟩ := szOK_facts hs
    rw [Nat.eq_of_beq_eq_true he] at hG
    rw [fwSift_zero]
    exact prep_unique hG (prep_pidn hn24 hw)
  | succ d ih =>
    intro l hl' G γ hG h
    have hlt : l < nb := by omega
    obtain ⟨_, _, hroot, hTK, _, _⟩ := fw_level hp hl hlt
    obtain ⟨hn24, _⟩ := szOK_facts (schP_levels_sz hl hlt)
    have e : pg w (mask w) G (pg w (mask w) BP l) = (γ (fwB hn w BP l) : Nat) := by
      rw [← hG, fwB_val hn hroot]
    rw [siftK_succ] at h
    simp only [strictB_eq, bIf_eq] at h
    rw [e] at h
    split at h
    · rename_i hk
      have hk' := Nat.blt_eq.mp hk
      rw [fwSift_succ]
      refine ⟨hk', ih (l + 1) (by omega) _ _ (prep_pcomp (schP_lt32 hn24) (hTK _ hk').2 hG) ?_⟩
      simp only [Nat.add_eq] at h
      exact h
    · exact absurd h Bool.false_ne_true

theorem siftK_of_fwSift {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} (hn : 0 < n)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hsz : szOK n w = true) :
    ∀ d l, l + d = nb → ∀ (G : Nat) (γ : Equiv.Perm (Fin n)), PRep n w G γ →
      G >>> (n * w) = 0 →
      fwSift (fwB hn w BP) (fun l => rcnt (LR l)) (fwPos n w LR) (fwT n w LR TR) d l γ →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hw0 : 0 < w := PF.w_pos hw
  intro d
  induction d with
  | zero =>
    intro l _ G γ hG hG0 h
    rw [fwSift_zero] at h
    subst h
    rw [siftK_zero]
    refine (bAnd_iff _ _).2 ⟨hsz, schP_beq ?_⟩
    exact PF.eq_of_fields hw0 hG0 (PF.pidn_shr hn24 hw) fun i hi => by
      rw [hG ⟨i, hi⟩, PF.pg_pidn hn24 hw hi]
      rfl
  | succ d ih =>
    intro l hl' G γ hG hG0 h
    have hlt : l < nb := by omega
    obtain ⟨_, _, hroot, hTK, _, _⟩ := fw_level hp hl hlt
    have e : pg w (mask w) G (pg w (mask w) BP l) = (γ (fwB hn w BP l) : Nat) := by
      rw [← hG, fwB_val hn hroot]
    rw [fwSift_succ] at h
    obtain ⟨hk, h⟩ := h
    have hk' : Nat.blt (rpos w (mask w) (n * w) (LR l) (γ (fwB hn w BP l))) (rcnt (LR l)) =
      true := blt_true hk
    rw [siftK_succ]
    simp only [strictB_eq, bIf_eq]
    rw [e, if_pos hk']
    simp only [Nat.add_eq]
    exact ih (l + 1) (by omega) _ _ (prep_pcomp (schP_lt32 hn24) (hTK _ hk).2 hG)
      (PF.pcomp_shr _ _ (schP_lt32 hn24) hw0) h

theorem schK_of_spec {n w m nw idn kS BP nb i T h₀ cnt : Nat} {S SI LR TR TRI : Nat → Nat}
    (H : ∀ h, h₀ ≤ h → h < h₀ + cnt → h < rcnt (LR i) → ∀ j < stCnt T,
      rpos w m nw (LR i) (pg w m (letterK S SI kS (stAt T j)) (rpt w m (LR i) h)) <
        rcnt (LR i) ∧
      siftK n w m nw idn LR TRI BP (Nat.sub nb (Nat.succ i)) (Nat.succ i)
        (pcomp n w m (TRI (Nat.add (roff n nw (LR i)) (rpos w m nw (LR i)
          (pg w m (letterK S SI kS (stAt T j)) (rpt w m (LR i) h)))))
          (pcomp n w m (letterK S SI kS (stAt T j)) (TR (Nat.add (roff n nw (LR i)) h)))) =
        true) :
    schK n w m nw idn S SI LR TR TRI kS BP nb i T h₀ cnt = true := by
  unfold schK
  simp only [strictB_eq]
  apply allN_of_forall
  intro dh hdh
  cases hb : Nat.blt (Nat.add h₀ dh) (rcnt (LR i))
  · rfl
  · have hc := Nat.blt_eq.mp hb
    refine (allN_of_forall ?_ : allN _ _ = true)
    intro j hj
    obtain ⟨h1, h2⟩ := H _ (by rw [Nat.add_eq]; omega) (by rw [Nat.add_eq]; omega) hc j hj
    exact (bAnd_iff _ _).2 ⟨blt_true h1, h2⟩

theorem schK_fwdT_of_schK {n w m nw idn : Nat} {S SI LR TR TRI : Nat → Nat}
    {kS BP nb i T h₀ cnt : Nat}
    (h : schK n w m nw idn S SI LR TR TRI kS BP nb i T h₀ cnt = true) :
    schK n w m nw idn S SI LR TR TRI kS BP nb i (fwdT T) h₀ cnt = true := by
  apply schK_of_spec
  intro x hx0 hx1 hxc j hj
  rw [stCnt_fwdT] at hj
  rw [stAt_fwdT]
  exact schK_spec h hx0 hx1 hxc j (by omega)

theorem fwSift_all {n w kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} (hn : 0 < n)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hf : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (fwdT (stepsAt n w PS kS BP i)) (s * CH) CH = true) :
    ∀ l ≤ nb, ∀ g, fwSift (fwB hn w BP) (fun l => rcnt (LR l)) (fwPos n w LR) (fwT n w LR TR)
      (nb - l) l g ↔ g ∈ Subgroup.closure (fwGens n w PS kS BP l) := by
  obtain ⟨hp, hn24, hk⟩ := head_facts hh
  have hh' := hh
  unfold headK at hh'
  simp only [bAnd_eq, Bool.and_eq_true] at hh'
  obtain ⟨hsz, _, _, _, _, _, hterm, _⟩ := hh'
  obtain ⟨_, hw⟩ := szOK_facts hsz
  have hbot : ∀ g ∈ fwGens n w PS kS BP nb, g = 1 := by
    rintro g ⟨j, hj, hfx, rfl⟩
    have hfx' : allN nb (fun t => strictB (pg w (mask w) BP t) (fun b =>
        Nat.beq (pg w (mask w) (PS j) b) b)) = true := hfx
    have h1 := allN_spec hterm j hj
    rw [hfx'] at h1
    have h2 : Nat.beq (PS j) (pidn n w) = true := h1
    have h3 := (prep_fwG hp hj).1
    rw [Nat.eq_of_beq_eq_true h2] at h3
    exact prep_unique h3 (prep_pidn hn24 hw)
  intro l hl0 g
  refine fwSift_iff _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ hbot ?_ (nb - l) l (by omega) g
  · intro l hlt k hk
    obtain ⟨_, _, hroot, hTK, _, hpts⟩ := fw_level hp hl hlt
    unfold fwPos
    rw [← (hTK k hk).1, fwB_val hn hroot, (hpts k hk).1]
    exact (hpts k hk).2.1
  · intro l hlt
    exact (fw_level hp hl hlt).1
  · intro l hlt
    exact (fw_level hp hl hlt).2.2.2.2.1
  · intro l hlt k hk
    exact ((fw_level hp hl hlt).2.2.2.2.2 k hk).2.2
  · rintro l _ g ⟨j, hj, hfx, rfl⟩
    refine ⟨j, hj, ?_, rfl⟩
    unfold fxK at hfx ⊢
    rw [allN_iff] at hfx ⊢
    exact fun t ht => hfx t (by omega)
  · rintro l hlt g ⟨j, hj, hfx, rfl⟩
    obtain ⟨_, _, hroot, _⟩ := fw_level hp hl hlt
    unfold fxK at hfx
    have h1 := allN_iff.1 hfx l (by omega)
    rw [strictB_eq] at h1
    apply Fin.ext
    rw [← (prep_fwG hp hj).1, fwB_val hn hroot, Nat.eq_of_beq_eq_true h1]
  · rintro l hlt s ⟨g, hg, hfx, rfl⟩ x hx
    obtain ⟨j, hj, hjL⟩ := fw_cover (n := n) (PSI := PSI) hk hg hfx
    obtain ⟨_, hcn, _, hTK, _, _⟩ := fw_level hp hl hlt
    obtain ⟨hCH, hsk, e⟩ := slice_cover hNS (by omega : x < n)
    have hk2 := schK_spec (hf l hlt _ hsk) (h := x) (by rw [Nat.add_eq] at e; omega)
      (by have := Nat.mod_lt x hCH; rw [Nat.add_eq] at e; omega) hx j hj
    rw [hjL] at hk2
    obtain ⟨h1, h2⟩ := hk2
    have ea := fw_apply hn hp hl hlt hx (prep_fwG hp hg).1
    have e2 : nb - l = nb - (l + 1) + 1 := by omega
    have hpos : fwPos n w LR l ((fwG n w PS g * fwT n w LR TR l x) (fwB hn w BP l)) =
        rpos w (mask w) (n * w) (LR l) (pg w (mask w) (PS g) (rpt w (mask w) (LR l) x)) := by
      unfold fwPos
      rw [ea]
    rw [e2, fwSift_succ, hpos]
    refine ⟨h1, fwSift_of_siftK hn hp hl _ _ (by omega) _ _
      (prep_pcomp (schP_lt32 hn24) (hTK _ h1).2
        (prep_pcomp (schP_lt32 hn24) (prep_fwG hp hg).1 (hTK x hx).1)) ?_⟩
    simp only [Nat.sub_eq, Nat.add_eq] at h2
    exact h2

end CFSG.KS.Raw.Orb

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

theorem schK_of_fwd {n w kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hf : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (fwdT (stepsAt n w PS kS BP i)) (s * CH) CH = true) :
    ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true := by
  intro i hi s _
  obtain ⟨hp, hn24, hk⟩ := head_facts hh
  obtain ⟨hc0, hcn, _, hTK, _, hpts⟩ := fw_level hp hl hi
  have hn : 0 < n := by omega
  have hsz := schP_levels_sz hl hi
  have hw0 : 0 < w := PF.w_pos (szOK_facts hsz).2
  have HI := fwSift_all hn hh hl hNS hf
  apply schK_of_spec
  intro x _ _ hx j hj
  obtain ⟨ℓ, hℓ, hPℓ⟩ := fw_letter hk hp j hj
  have hm := (HI i hi.le _).2 (Subgroup.mul_mem _ hℓ (hpts x hx).2.2)
  have ea := fw_apply hn hp hl hi hx hPℓ
  have e2 : nb - i = nb - (i + 1) + 1 := by omega
  have hpos : fwPos n w LR i ((ℓ * fwT n w LR TR i x) (fwB hn w BP i)) =
      rpos w (mask w) (n * w) (LR i) (pg w (mask w) (letterK PS PSI kS
        (stAt (stepsAt n w PS kS BP i) j)) (rpt w (mask w) (LR i) x)) := by
    unfold fwPos
    rw [ea]
  rw [e2, fwSift_succ, hpos] at hm
  obtain ⟨h1, h2⟩ := hm
  refine ⟨h1, ?_⟩
  simp only [Nat.sub_eq, Nat.add_eq]
  exact siftK_of_fwSift hn hp hl hsz _ _ (by omega) _ _
    (prep_pcomp (schP_lt32 hn24) (hTK _ h1).2 (prep_pcomp (schP_lt32 hn24) hPℓ (hTK x hx).1))
    (PF.pcomp_shr _ _ (schP_lt32 hn24) hw0) h2

end CFSG.KS.Raw

end
