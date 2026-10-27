module

public import CFSG.Certificates.Kernel.LocalQTBfsWordSound
public import CFSG.Certificates.Kernel.LocalQTChainMSound
public import CFSG.Certificates.Kernel.LocalQTLatKSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

theorem img_ge (hn : n ≤ 32) {x : ℕ} (hx : FC n x) {i : ℕ} (hi : n ≤ i) : P.img x i = 0 := by
  have hlt : x < 32 ^ i := by
    have h1 : x < 32 ^ n := by
      rw [← hx.1, P.ofFn_eq]
      exact P.E_lt fun j hj => by have := hx.2 j hj; omega
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hi)
  rw [P.img_eq, Nat.div_eq_of_lt hlt]

theorem code_mul' (hn : n ≤ 32) (σ τ : Perm (Fin n)) :
    P.mul n (P.code σ) (P.code τ) = P.code (σ * τ) := P.code_mul hn σ τ

theorem code_inv_mul (hn : n ≤ 32) (σ τ : Perm (Fin n)) :
    P.mul n (P.inv n (P.code τ)) (P.code σ) = P.code (τ⁻¹ * σ) := by
  rw [P.code_inv hn, P.code_mul hn]

theorem img_code_fix (hn : n ≤ 32) (σ : Perm (Fin n)) {b : ℕ} (hb : b < n) :
    P.img (P.code σ) b = σ ⟨b, hb⟩ := P.img_code hn σ ⟨b, hb⟩

abbrev InC (n : ℕ) (C : List Lvl) (σ : Perm (Fin n)) : Prop := (sift n C (P.code σ)).isSome

abbrev LvP (n : ℕ) (prev : List ℕ) (lv : Lvl) : Prop :=
  LvOK n lv ∧ (∀ j < n, getK lv.2.1 j ≠ 0 →
    (∀ b ∈ prev, P.img (getK lv.2.1 j) b = b) ∧ P.img (getK lv.2.1 j) lv.1 = j) ∧
  (∀ i < lv.2.2.2, ∃ j < n, getK lv.2.1 j ≠ 0 ∧ getK lv.2.2.1 j = i) ∧ 0 < lv.2.2.2

def ChainP (n : ℕ) : List ℕ → List Lvl → Prop
  | _, [] => True
  | prev, lv :: C => LvP n prev lv ∧ ChainP n (lv.1 :: prev) C

theorem chainP_lvOK : ∀ {prev : List ℕ} {C : List Lvl}, ChainP n prev C → ∀ lv ∈ C, LvOK n lv
  | _, [], _ => fun _ h => absurd h List.not_mem_nil
  | _, lv :: C, h => fun l hl => by
    rcases List.mem_cons.1 hl with rfl | hl
    · exact h.1.1
    · exact chainP_lvOK h.2 l hl

theorem lvP_of {lv : Lvl} {prev : List ℕ}
    (h1 : P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
          (P.letB (getK lv.2.1 j) fun u => CFSG.KC.Ord.andB (P.permK n u)
            (CFSG.KC.Ord.andB (P.allL prev fun b => Nat.beq (P.img u b) b)
              (CFSG.KC.Ord.andB (Nat.beq (P.img u lv.1) j)
                (Nat.blt (getK lv.2.2.1 j) lv.2.2.2))))) = true)
    (h2 : Nat.beq (posMask lv n) (Nat.sub (Nat.shiftLeft 1 lv.2.2.2) 1) = true)
    (h3 : CFSG.KC.Ord.andB (Nat.blt 0 lv.2.2.2) (Nat.beq (validCnt n lv.2.1) lv.2.2.2) = true) :
    LvP n prev lv := by
  refine ⟨lvOK_of h1 h2 h3, fun j hj e => ?_, fun i hi => ?_,
    P.blt_iff.1 (P.andB_iff.1 h3).1⟩
  · rw [P.allN_iff] at h1
    have := h1 j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq, P.andB_iff, P.andB_iff, P.andB_iff,
      P.allL_iff, P.beq_iff] at this
    obtain ⟨-, hb, hj', -⟩ := this e
    exact ⟨fun b hb' => P.beq_iff.1 (hb b hb'), hj'⟩
  · rw [P.beq_iff] at h2
    rw [← testBit_posMask lv i n, h2]
    change (1 <<< lv.2.2.2 - 1).testBit i = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hi

theorem chainP_of : ∀ (C : List Lvl) (prev : List ℕ), okFrom n C prev = true →
    chainInj n C = true → ChainP n prev C
  | [], _, _, _ => trivial
  | lv :: C, prev, h, hI => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB _ (Nat.beq (posMask lv n) _))
      (okFrom n C (lv.1 :: prev)) = true at h
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt 0 lv.2.2.2)
      (Nat.beq (validCnt n lv.2.1) lv.2.2.2)) (chainInj n C) = true at hI
    rw [P.andB_iff, P.andB_iff] at h
    rw [P.andB_iff] at hI
    exact ⟨lvP_of h.1.1 h.1.2 hI.1, chainP_of C _ h.2 hI.2⟩

theorem chainP_of_ok {C : List Lvl} (hok : chainOK n C = true) (hI : chainInj n C = true) :
    ChainP n [] C := chainP_of C [] (by rw [← chainOK_eq]; exact hok) hI

theorem sift_cons_code (hn : n ≤ 32) {lv : Lvl} {C : List Lvl} (hlv : LvOK n lv) (σ : Perm (Fin n))
    {k : ℕ} (h : sift n (lv :: C) (P.code σ) = some k) :
    ∃ j < n, ∃ τ : Perm (Fin n), P.code τ = getK lv.2.1 j ∧ getK lv.2.1 j ≠ 0 ∧
      P.img (P.code σ) lv.1 = j ∧ ∃ k', sift n C (P.code (τ⁻¹ * σ)) = some k' ∧
        k = getK lv.2.2.1 j + lv.2.2.2 * k' := by
  simp only [sift] at h
  split_ifs at h with e
  obtain ⟨k', h', rfl⟩ := Option.map_eq_some_iff.1 h
  have hj := img_lt hn (fc_code hn σ) hlv.1 lv.1
  obtain ⟨⟨τ, hτ⟩, -⟩ := hlv.2.1 _ hj e
  refine ⟨_, hj, τ, hτ, e, rfl, k', ?_, rfl⟩
  rw [← hτ, code_inv_mul hn] at h'
  exact h'

theorem fix_of_inC (hn : n ≤ 32) : ∀ {prev : List ℕ} {C : List Lvl}, ChainP n prev C →
    ∀ {σ : Perm (Fin n)}, InC n C σ → ∀ b ∈ prev, P.img (P.code σ) b = P.img (P.one n) b
  | prev, [], _, σ, h, b, _ => by
    simp only [InC, sift] at h
    split_ifs at h with e
    · rw [e]
    · exact absurd h (by simp)
  | prev, lv :: C, hC, σ, h, b, hb => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ := sift_cons_code hn hC.1.1 σ hk
    have hfix := fix_of_inC hn hC.2 (σ := τ⁻¹ * σ) (by rw [InC, h']; rfl) b (List.mem_cons_of_mem _ hb)
    have hτb := (hC.1.2.1 j hj e).1 b hb
    rw [← hτ] at hτb
    by_cases hbn : b < n
    · rw [img_one hn hbn]
      rw [img_one hn hbn, img_code_fix hn _ hbn] at hfix
      rw [img_code_fix hn _ hbn] at hτb ⊢
      have e1 : σ = τ * (τ⁻¹ * σ) := by group
      rw [e1, Perm.mul_apply]
      have : (τ⁻¹ * σ) ⟨b, hbn⟩ = ⟨b, hbn⟩ := Fin.ext hfix
      rw [this]
      exact hτb
    · rw [img_ge hn (fc_code hn σ) (not_lt.1 hbn), img_ge hn (fc_one hn) (not_lt.1 hbn)]

theorem sift_mul_rep (hn : n ≤ 32) {prev : List ℕ} {lv : Lvl} {C : List Lvl}
    (hC : ChainP n prev (lv :: C)) {j : ℕ} (hj : j < n) (τ : Perm (Fin n))
    (hτ : P.code τ = getK lv.2.1 j) (e : getK lv.2.1 j ≠ 0) {σ : Perm (Fin n)} {k : ℕ}
    (hσ : sift n C (P.code σ) = some k) :
    sift n (lv :: C) (P.code (τ * σ)) = some (getK lv.2.2.1 j + lv.2.2.2 * k) := by
  have hfix := fix_of_inC hn hC.2 (σ := σ) (by rw [InC, hσ]; rfl) lv.1 (List.mem_cons_self ..)
  have himg : P.img (P.code (τ * σ)) lv.1 = j := by
    have hb := (hC.1.2.1 j hj e).2
    rw [← hτ] at hb
    by_cases hbn : lv.1 < n
    · rw [img_one hn hbn, img_code_fix hn _ hbn] at hfix
      rw [img_code_fix hn _ hbn] at hb ⊢
      rw [Perm.mul_apply]
      have : σ ⟨lv.1, hbn⟩ = ⟨lv.1, hbn⟩ := Fin.ext hfix
      rw [this]
      exact hb
    · rw [img_ge hn (fc_code hn _) (not_lt.1 hbn)]
      rw [img_ge hn (fc_code hn _) (not_lt.1 hbn)] at hb
      exact hb
  simp only [sift, himg, e, ↓reduceIte]
  rw [← hτ, code_inv_mul hn, inv_mul_cancel_left, hσ]
  rfl

theorem exists_sift (hn : n ≤ 32) : ∀ {prev : List ℕ} {C : List Lvl}, ChainP n prev C →
    ∀ k < chainF C, ∃ σ : Perm (Fin n), sift n C (P.code σ) = some k
  | _, [], _, k, hk => by
    have : k = 0 := by change k < 1 at hk; omega
    subst this
    refine ⟨1, ?_⟩
    simp [sift, P.code_one]
  | _, lv :: C, hC, k, hk => by
    change k < lv.2.2.2 * chainF C at hk
    have hr : 0 < lv.2.2.2 := hC.1.2.2.2
    obtain ⟨j, hj, e, hp⟩ := hC.1.2.2.1 (k % lv.2.2.2) (Nat.mod_lt _ hr)
    obtain ⟨⟨τ, hτ⟩, -⟩ := hC.1.1.2.1 j hj e
    obtain ⟨σ, hσ⟩ := exists_sift hn hC.2 (k / lv.2.2.2)
      (Nat.div_lt_of_lt_mul hk)
    refine ⟨τ * σ, ?_⟩
    rw [sift_mul_rep hn hC hj τ hτ e hσ, hp, Nat.mod_add_div]

theorem chainFrom_sound (hn : n ≤ 32) (f : ℕ → Bool) : ∀ {C : List Lvl}, (∀ lv ∈ C, LvOK n lv) →
    ∀ (π σ : Perm (Fin n)), chainFrom n C f (P.code π) = true → InC n C σ →
      f (P.code (π * σ)) = true
  | [], _, π, σ, h, hσ => by
    simp only [InC, sift] at hσ
    split_ifs at hσ with e
    · rw [P.code_one] at e
      rw [P.code_inj hn e, mul_one]
      exact h
    · exact absurd hσ (by simp)
  | lv :: C, hC, π, σ, h, hσ => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ := sift_cons_code hn (hC lv (List.mem_cons_self ..)) σ hk
    change P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
      (P.letB (P.mul n (P.code π) (getK lv.2.1 j)) (chainFrom n C f))) = true at h
    rw [P.allN_iff] at h
    have := h j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq, ← hτ, P.code_mul hn] at this
    have := chainFrom_sound hn f (fun l hl => hC l (List.mem_cons_of_mem _ hl)) (π * τ) (τ⁻¹ * σ)
      (this (by rwa [hτ])) (by rw [InC, h']; rfl)
    rwa [mul_assoc, mul_inv_cancel_left] at this

theorem allChain_sound (hn : n ≤ 32) {C : List Lvl} (hC : ∀ lv ∈ C, LvOK n lv) (f : ℕ → Bool)
    (h : allChain n C f = true) (σ : Perm (Fin n)) (hσ : InC n C σ) : f (P.code σ) = true := by
  have := chainFrom_sound hn f hC 1 σ (by rw [← P.code_one]; exact h) hσ
  rwa [one_mul] at this

theorem inC_iff (hn : n ≤ 32) {C : List Lvl} (hC : ∀ lv ∈ C, LvOK n lv) (σ : Perm (Fin n)) :
    inC n C (chainF C) (P.code σ) = true ↔ InC n C σ := by
  unfold inC InC
  rw [P.blt_iff, idxM_sift]
  cases e : sift n C (P.code σ) with
  | none => simp
  | some k =>
    simp only [Option.elim_some, id, Option.isSome_some, iff_true]
    exact sift_lt hn C hC (fc_code hn σ) e

theorem chainF_pos : ∀ {prev : List ℕ} {C : List Lvl}, ChainP n prev C → 0 < chainF C
  | _, [], _ => Nat.one_pos
  | _, _ :: _, hC => Nat.mul_pos hC.1.2.2.2 (chainF_pos hC.2)

@[expose] noncomputable def maxLen (m : ℕ) (ws : List (List ℕ)) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j m => Bool.rec (motive := fun _ => ℕ) m
    (lenA (CFSG.KC.LQT.M.getW ws j)) (Nat.blt m (lenA (CFSG.KC.LQT.M.getW ws j)))) m

theorem maxLen_ge (ws : List (List ℕ)) : ∀ m, ∀ j < m,
    lenA (CFSG.KC.LQT.M.getW ws j) ≤ maxLen m ws
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, j, hj => by
    change lenA (CFSG.KC.LQT.M.getW ws j) ≤ Bool.rec (motive := fun _ => ℕ) (maxLen m ws)
      (lenA (CFSG.KC.LQT.M.getW ws m)) (Nat.blt (maxLen m ws) (lenA (CFSG.KC.LQT.M.getW ws m)))
    have key : maxLen m ws ≤ Bool.rec (motive := fun _ => ℕ) (maxLen m ws)
        (lenA (CFSG.KC.LQT.M.getW ws m)) (Nat.blt (maxLen m ws) (lenA (CFSG.KC.LQT.M.getW ws m))) ∧
        lenA (CFSG.KC.LQT.M.getW ws m) ≤ Bool.rec (motive := fun _ => ℕ) (maxLen m ws)
        (lenA (CFSG.KC.LQT.M.getW ws m)) (Nat.blt (maxLen m ws) (lenA (CFSG.KC.LQT.M.getW ws m))) := by
      cases h : Nat.blt (maxLen m ws) (lenA (CFSG.KC.LQT.M.getW ws m))
      · have : ¬ maxLen m ws < lenA (CFSG.KC.LQT.M.getW ws m) := by
          rw [← Nat.blt_eq, h]
          exact Bool.false_ne_true
        exact ⟨le_refl _, by change _ ≤ maxLen m ws; omega⟩
      · have : maxLen m ws < lenA (CFSG.KC.LQT.M.getW ws m) := by
          rw [← Nat.blt_eq]
          exact h
        exact ⟨by change maxLen m ws ≤ lenA (CFSG.KC.LQT.M.getW ws m); omega, le_refl _⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact (maxLen_ge ws m j hj).trans key.1
    · exact key.2

@[expose] noncomputable def wordsGo (n : ℕ) (G : List ℕ) (C : List Lvl) :
    List (List (List ℕ)) → ℕ → Bool :=
  List.rec (motive := fun _ => List (List (List ℕ)) → ℕ → Bool) (fun _ _ => true)
    (fun lv _ ih W budget => List.rec (motive := fun _ => Bool) false
      (fun ws W' _ => CFSG.KC.Ord.andB
        (P.allN n fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
          (Nat.beq (CFSG.KC.LQT.W.evalWK n G (CFSG.KC.LQT.M.getW ws j)) (getK lv.2.1 j)))
        (P.letB (maxLen n ws) fun len =>
          CFSG.KC.Ord.andB (Nat.ble len budget) (ih W' (Nat.sub budget len))))
      W) C

theorem wordsC_eq (n : ℕ) (C : List Lvl) (G : List ℕ) (W : List (List (List ℕ))) (d : ℕ) :
    wordsC n C G W d = wordsGo n G C W d := rfl

theorem evalW_eq (G : List (Perm (Fin n))) : ∀ w : List ℕ,
    evalW G w = (w.filterMap fun i => G[i]?).prod
  | [] => rfl
  | i :: w => by
    rw [evalW, List.filterMap_cons, evalW_eq G w, List.getD_eq_getElem?_getD]
    cases G[i]? with
    | none => simp
    | some g => simp

theorem words_of_inC (hn : n ≤ 32) (G : List (Perm (Fin n))) : ∀ (C : List Lvl)
    (W : List (List (List ℕ))) (budget : ℕ), wordsGo n (G.map P.code) C W budget = true →
    (∀ lv ∈ C, LvOK n lv) → ∀ σ, InC n C σ →
      ∃ l : List (Perm (Fin n)), (∀ g ∈ l, g ∈ G) ∧ l.length ≤ budget ∧ l.prod = σ
  | [], _, _, _, _, σ, hσ => by
    refine ⟨[], by simp, by simp, ?_⟩
    simp only [InC, sift] at hσ
    split_ifs at hσ with e
    · rw [P.code_one] at e
      exact (P.code_inj hn e).symm
    · exact absurd hσ (by simp)
  | _ :: _, [], _, h, _, _, _ => absurd h (by simp [wordsGo])
  | lv :: C, ws :: W, budget, h, hC, σ, hσ => by
    change CFSG.KC.Ord.andB (P.allN n fun j => P.impB
        (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
        (Nat.beq (CFSG.KC.LQT.W.evalWK n (G.map P.code) (CFSG.KC.LQT.M.getW ws j)) (getK lv.2.1 j)))
      (P.letB (maxLen n ws) fun len => CFSG.KC.Ord.andB (Nat.ble len budget)
        (wordsGo n (G.map P.code) C W (Nat.sub budget len))) = true at h
    rw [P.andB_iff, P.letB_eq, P.andB_iff, P.allN_iff, Nat.ble_eq] at h
    obtain ⟨hw, hle, hrest⟩ := h
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ :=
      sift_cons_code hn (hC lv (List.mem_cons_self ..)) σ hk
    have hwj := hw j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.beq_iff, LK.evalWK_code hn, ← hτ] at hwj
    have hτ' : evalW G (CFSG.KC.LQT.M.getW ws j) = τ := P.code_inj hn (hwj (by rwa [hτ]))
    obtain ⟨l', hl'G, hl'len, hl'⟩ := words_of_inC hn G C W _ hrest
      (fun l hl => hC l (List.mem_cons_of_mem _ hl)) (τ⁻¹ * σ) (by rw [InC, h']; rfl)
    have hlen := maxLen_ge ws n j hj
    rw [LK.lenA_eq] at hlen
    refine ⟨(CFSG.KC.LQT.M.getW ws j).filterMap (fun i => G[i]?) ++ l', fun g hg => ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hg with hg | hg
      · obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hg
        exact List.mem_of_getElem? hi
      · exact hl'G g hg
    · rw [List.length_append]
      have := List.length_filterMap_le (fun i => G[i]?) (CFSG.KC.LQT.M.getW ws j)
      change _ ≤ budget - maxLen n ws at hl'len
      omega
    · rw [List.prod_append, ← evalW_eq, hτ', hl', mul_inv_cancel_left]

theorem inC_pow {C : List Lvl} {G : List (Perm (Fin n))}
    (hmul : ∀ σ, InC n C σ → ∀ g ∈ G, InC n C (σ * g)) {σ : Perm (Fin n)}
    (hσ : InC n C σ) {g : Perm (Fin n)} (hg : g ∈ G) : ∀ m : ℕ, InC n C (σ * g ^ m)
  | 0 => by rwa [pow_zero, mul_one]
  | m + 1 => by
    rw [pow_succ, ← mul_assoc]
    exact hmul _ (inC_pow hmul hσ hg m) g hg

theorem grpC_sound (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G : List (Perm (Fin n))) {W : List (List (List ℕ))} {d : ℕ}
    (h : grpC n C (chainF C) (G.map P.code) W d = true) :
    (∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ G}) ∧
      ∀ σ, InC n C σ → ∃ l : List (Perm (Fin n)), (∀ g ∈ l, g ∈ G) ∧ l.length ≤ d ∧ l.prod = σ := by
  have hCP := chainP_of_ok hok hI
  have hC := chainP_lvOK hCP
  unfold grpC at h
  rw [P.andB_iff, P.andB_iff, P.allL_map] at h
  obtain ⟨hg, hw, hc⟩ := h
  have hgen : ∀ g ∈ G, InC n C g := fun g hg' => (inC_iff hn hC g).1 (hg g hg')
  have hmul : ∀ σ, InC n C σ → ∀ g ∈ G, InC n C (σ * g) := fun σ hσ g hg' => by
    have := allChain_sound hn hC _ hc σ hσ
    rw [P.allL_map] at this
    have := this g hg'
    rwa [P.code_mul hn, inC_iff hn hC] at this
  have hwords := words_of_inC hn G C W d hw hC
  have hsub : ∀ σ, InC n C σ → σ ∈ Subgroup.closure {g | g ∈ G} := fun σ hσ => by
    obtain ⟨l, hl, -, rfl⟩ := hwords σ hσ
    clear hσ
    induction l with
    | nil => exact Subgroup.one_mem _
    | cons a l ih =>
      rw [List.prod_cons]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (hl a List.mem_cons_self))
        (ih fun g hg' => hl g (List.mem_cons_of_mem _ hg'))
  have hone : InC n C 1 := by
    obtain ⟨σ0, h0⟩ := exists_sift hn hCP 0 (chainF_pos hCP)
    have hσ0 : InC n C σ0 := by rw [InC, h0]; rfl
    rcases G with _ | ⟨g, G'⟩
    · have := hsub σ0 hσ0
      simp only [List.not_mem_nil, Set.ofPred_false, Subgroup.closure_empty,
        Subgroup.mem_bot] at this
      rwa [this] at hσ0
    · have hg1 := hgen g (List.mem_cons_self ..)
      have := inC_pow hmul hg1 (List.mem_cons_self ..) (orderOf g - 1)
      rwa [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one] at this
  refine ⟨fun σ => ⟨hsub σ, fun hσ => ?_⟩, hwords⟩
  induction hσ using Subgroup.closure_induction_right with
  | one => exact hone
  | mul_right x _ y hy ih => exact hmul x ih y hy
  | mul_inv_cancel x _ y hy ih =>
    have e : y⁻¹ = y ^ (orderOf y - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos y),
        pow_orderOf_eq_one]
    rw [e]
    exact inC_pow hmul ih hy _

theorem mem_bfsSet_iff (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G : List (Perm (Fin n))) {W : List (List (List ℕ))} {d : ℕ}
    (h : grpC n C (chainF C) (G.map P.code) W d = true) (r : RN n) :
    r ∈ bfsSet (G.map RN.enc) d ↔ ∃ σ, InC n C σ ∧ RN.enc σ = r := by
  obtain ⟨h1, h2⟩ := grpC_sound hn hok hI G h
  constructor
  · intro hr
    obtain ⟨σ, hσ, rfl⟩ := bfsSet_sound (rawIsEnc n) G d r hr
    exact ⟨σ, (h1 σ).2 hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨l, hl, hlen, rfl⟩ := h2 σ hσ
    exact mem_bfsSet_prod RN.enc_mul RN.enc_one G d l hl hlen

theorem card_inC (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) : Nat.card {σ : Perm (Fin n) // InC n C σ} = chainF C := by
  have hCP := chainP_of_ok hok hI
  have hC := chainP_lvOK hCP
  have hlt : ∀ σ : {σ : Perm (Fin n) // InC n C σ}, (sift n C (P.code σ.1)).get σ.2 < chainF C :=
    fun σ => sift_lt hn C hC (fc_code hn σ.1) (Option.some_get σ.2).symm
  rw [← Nat.card_fin (chainF C)]
  refine Nat.card_eq_of_bijective (fun σ => ⟨_, hlt σ⟩) ⟨fun a b hab => ?_, fun k => ?_⟩
  · simp only [Fin.mk.injEq] at hab
    refine Subtype.ext (P.code_inj hn (sift_inj hn C hC (fc_code hn _) (fc_code hn _)
      (Option.some_get a.2).symm (hab ▸ (Option.some_get b.2).symm)))
  · obtain ⟨σ, hσ⟩ := exists_sift hn hCP k k.isLt
    refine ⟨⟨σ, by rw [InC, hσ]; rfl⟩, Fin.ext ?_⟩
    simp only [hσ, Option.get_some]

theorem size_bfsSet (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G : List (Perm (Fin n))) {W : List (List (List ℕ))} {d : ℕ}
    (h : grpC n C (chainF C) (G.map P.code) W d = true) :
    (bfsSet (G.map RN.enc) d).size = chainF C := by
  obtain ⟨h1, -⟩ := grpC_sound hn hok hI G h
  have hY : ∀ x, x ∈ Subgroup.closure {g | g ∈ G} ↔ RN.enc x ∈ (bfsSet (G.map RN.enc) d).toList := by
    intro x
    rw [Std.HashSet.mem_toList, mem_bfsSet_iff hn hok hI G h, ← h1]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨σ, hσ, e⟩ => (RN.enc_inj e) ▸ hσ⟩
  have := card_of_list RN.enc_inj (Subgroup.closure {g | g ∈ G}) _ (toList_nodup _) hY
    (fun r hr => ⟨_, ((mem_bfsSet_iff hn hok hI G h r).1 (Std.HashSet.mem_toList.1 hr)).choose_spec.2⟩)
  rw [Std.HashSet.length_toList] at this
  rw [← this, ← card_inC hn hok hI]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => (h1 σ).symm)

end CFSG.KC.LQT.CM

end
