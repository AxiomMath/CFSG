module

public import Certificates.Data.Kernel.LocalQT.ChainInj
public import CFSG.Certificates.Kernel.LocalQTBfsKSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {n : ℕ}

@[expose] def FC (n x : ℕ) : Prop := P.ofFn n (P.img x) = x ∧ ∀ i < n, P.img x i < n

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem img_ofFn (hn : n ≤ 32) {g : ℕ → ℕ} (hg : ∀ i < n, g i < n) {i : ℕ} (hi : i < n) :
    P.img (P.ofFn n g) i = g i := by
  rw [P.img_eq, P.ofFn_eq, P.E_digit (fun j hj => by have := hg j hj; omega) hi]

theorem ofFn_congr {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : P.ofFn n f = P.ofFn n g := by
  rw [P.ofFn_eq, P.ofFn_eq]
  exact P.E_congr h

theorem fc_ofFn (hn : n ≤ 32) {g : ℕ → ℕ} (hg : ∀ i < n, g i < n) : FC n (P.ofFn n g) :=
  ⟨ofFn_congr fun i hi => img_ofFn hn hg hi, fun i hi => by rw [img_ofFn hn hg hi]; exact hg i hi⟩

theorem fc_ext {x y : ℕ} (hx : FC n x) (hy : FC n y) (h : ∀ i < n, P.img x i = P.img y i) :
    x = y := by
  rw [← hx.1, ← hy.1, P.ofFn_eq, P.ofFn_eq]
  exact P.E_congr h

theorem img_code_lt (hn : n ≤ 32) (σ : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    P.img (P.code σ) i < n := by
  have e : P.img (P.code σ) i = ((σ ⟨i, hi⟩ : Fin n) : ℕ) := P.img_code hn σ ⟨i, hi⟩
  rw [e]
  exact (σ _).isLt

theorem fc_code (hn : n ≤ 32) (σ : Perm (Fin n)) : FC n (P.code σ) := by
  refine ⟨?_, fun i hi => img_code_lt hn σ hi⟩
  rw [P.ofFn_eq]
  exact P.code_of_vals σ fun i hi => P.img_code' hn σ hi

theorem img_mul (hn : n ≤ 32) {s t : ℕ} (hs : FC n s) (ht : FC n t) {i : ℕ} (hi : i < n) :
    P.img (P.mul n s t) i = P.img s (P.img t i) :=
  img_ofFn hn (fun j hj => hs.2 _ (ht.2 j hj)) hi

theorem fc_mul (hn : n ≤ 32) {s t : ℕ} (hs : FC n s) (ht : FC n t) : FC n (P.mul n s t) :=
  fc_ofFn hn fun j hj => hs.2 _ (ht.2 j hj)

theorem fc_one (hn : n ≤ 32) : FC n (P.one n) := by
  rw [P.code_one]
  exact fc_code hn 1

theorem img_one (hn : n ≤ 32) {i : ℕ} (hi : i < n) : P.img (P.one n) i = i :=
  img_ofFn hn (fun _ hj => hj) hi

theorem img_lt (hn : n ≤ 32) {x : ℕ} (hx : FC n x) (hn0 : 0 < n) (i : ℕ) : P.img x i < n := by
  by_cases hi : i < n
  · exact hx.2 i hi
  · have hlt : x < 32 ^ i := by
      have h1 : x < 32 ^ n := by
        rw [← hx.1, P.ofFn_eq]
        exact P.E_lt fun j hj => by have := hx.2 j hj; omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [P.img_eq, Nat.div_eq_of_lt hlt]
    simpa using hn0

theorem mul_inv_mul (hn : n ≤ 32) (σ : Perm (Fin n)) {x : ℕ} (hx : FC n x) :
    P.mul n (P.code σ) (P.mul n (P.inv n (P.code σ)) x) = x := by
  rw [P.code_inv hn]
  refine fc_ext (fc_mul hn (fc_code hn σ) (fc_mul hn (fc_code hn _) hx)) hx fun i hi => ?_
  rw [img_mul hn (fc_code hn σ) (fc_mul hn (fc_code hn _) hx) hi,
    img_mul hn (fc_code hn _) hx hi]
  have h1 := hx.2 i hi
  have e1 : P.img (P.code σ⁻¹) (P.img x i) = ((σ⁻¹ ⟨P.img x i, h1⟩ : Fin n) : ℕ) :=
    P.img_code hn σ⁻¹ ⟨_, h1⟩
  rw [e1, P.img_code hn σ]
  simp

@[expose] noncomputable def sift (n : ℕ) : List Lvl → ℕ → Option ℕ
  | [], h => if h = P.one n then some 0 else none
  | lv :: C, h => if getK lv.2.1 (P.img h lv.1) = 0 then none else
      (sift n C (P.mul n (P.inv n (getK lv.2.1 (P.img h lv.1))) h)).map
        (fun k => getK lv.2.2.1 (P.img h lv.1) + lv.2.2.2 * k)

@[expose] noncomputable def idxGo (n F : ℕ) (C : List Lvl) : ℕ → ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ)
    (fun h acc _ => Bool.rec (motive := fun _ => ℕ) F acc (Nat.beq h (P.one n)))
    (fun lv _ ih h acc mult =>
      CFSG.KC.Loop.strictN (P.img h lv.1) fun j => CFSG.KC.Loop.strictN (getK lv.2.1 j) fun u =>
        Bool.rec (motive := fun _ => ℕ)
          (CFSG.KC.Loop.strictN (P.mul n (P.inv n u) h) fun h' =>
            ih h' (Nat.add acc (Nat.mul (getK lv.2.2.1 j) mult)) (Nat.mul mult lv.2.2.2))
          F (Nat.beq u 0))
    C

theorem idxM_eq (n : ℕ) (C : List Lvl) (F x : ℕ) : idxM n C F x = idxGo n F C x 0 1 := rfl

theorem idxGo_eq (F : ℕ) : ∀ (C : List Lvl) (h acc mult : ℕ),
    idxGo n F C h acc mult = (sift n C h).elim F (fun k => acc + mult * k)
  | [], h, acc, mult => by
    change Bool.rec (motive := fun _ => ℕ) F acc (Nat.beq h (P.one n)) = _
    by_cases e : h = P.one n
    · rw [P.beq_iff.2 e]
      simp [sift, e]
    · rw [beq_false e]
      simp [sift, e]
  | lv :: C, h, acc, mult => by
    change CFSG.KC.Loop.strictN (P.img h lv.1) (fun j => CFSG.KC.Loop.strictN (getK lv.2.1 j)
      fun u => Bool.rec (motive := fun _ => ℕ)
        (CFSG.KC.Loop.strictN (P.mul n (P.inv n u) h) fun h' =>
          idxGo n F C h' (Nat.add acc (Nat.mul (getK lv.2.2.1 j) mult)) (Nat.mul mult lv.2.2.2))
        F (Nat.beq u 0)) = _
    rw [strictN_eq, strictN_eq]
    by_cases e : getK lv.2.1 (P.img h lv.1) = 0
    · rw [P.beq_iff.2 e]
      simp [sift, e]
    · rw [beq_false e]
      dsimp only
      rw [strictN_eq, idxGo_eq F C]
      simp only [sift, e, ↓reduceIte]
      cases sift n C (P.mul n (P.inv n (getK lv.2.1 (P.img h lv.1))) h) with
      | none => rfl
      | some k =>
        simp only [Option.map_some, Option.elim_some]
        change acc + getK lv.2.2.1 (P.img h lv.1) * mult + mult * lv.2.2.2 * k = _
        ring

theorem idxM_sift (C : List Lvl) (F x : ℕ) : idxM n C F x = (sift n C x).elim F id := by
  rw [idxM_eq, idxGo_eq]
  cases sift n C x <;> simp

@[expose] def LvOK (n : ℕ) (lv : Lvl) : Prop :=
  0 < n ∧ (∀ j < n, getK lv.2.1 j ≠ 0 → (∃ σ : Perm (Fin n), P.code σ = getK lv.2.1 j) ∧
    getK lv.2.2.1 j < lv.2.2.2) ∧
  ∀ j₁ < n, ∀ j₂ < n, getK lv.2.1 j₁ ≠ 0 → getK lv.2.1 j₂ ≠ 0 →
    getK lv.2.2.1 j₁ = getK lv.2.2.1 j₂ → j₁ = j₂

theorem sift_lt (hn : n ≤ 32) : ∀ (C : List Lvl), (∀ lv ∈ C, LvOK n lv) →
    ∀ {x k : ℕ}, FC n x → sift n C x = some k → k < chainF C
  | [], _, x, k, _, h => by
    simp only [sift] at h
    split_ifs at h
    cases h
    exact Nat.one_pos
  | lv :: C, hC, x, k, hx, h => by
    obtain ⟨hn0, hv, -⟩ := hC lv (List.mem_cons_self ..)
    simp only [sift] at h
    split_ifs at h with e
    obtain ⟨k', h', rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨⟨σ, hσ⟩, hp⟩ := hv _ (img_lt hn hx hn0 lv.1) e
    rw [← hσ] at h'
    have hk' := sift_lt hn C (fun l hl => hC l (List.mem_cons_of_mem _ hl))
      (fc_mul hn (by rw [P.code_inv hn]; exact fc_code hn _) hx) h'
    change _ < lv.2.2.2 * chainF C
    nlinarith

theorem sift_inj (hn : n ≤ 32) : ∀ (C : List Lvl), (∀ lv ∈ C, LvOK n lv) →
    ∀ {x y k : ℕ}, FC n x → FC n y → sift n C x = some k → sift n C y = some k → x = y
  | [], _, x, y, k, _, _, hx, hy => by
    simp only [sift] at hx hy
    split_ifs at hx hy with e1 e2
    rw [e1, e2]
  | lv :: C, hC, x, y, k, fx, fy, hx, hy => by
    obtain ⟨hn0, hv, hinj⟩ := hC lv (List.mem_cons_self ..)
    have hC' : ∀ l ∈ C, LvOK n l := fun l hl => hC l (List.mem_cons_of_mem _ hl)
    simp only [sift] at hx hy
    split_ifs at hx hy with e1 e2
    obtain ⟨kx, hx', ex⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨ky, hy', ey⟩ := Option.map_eq_some_iff.1 hy
    have jx := img_lt hn fx hn0 lv.1
    have jy := img_lt hn fy hn0 lv.1
    obtain ⟨⟨σ, hσ⟩, hpx⟩ := hv _ jx e1
    obtain ⟨-, hpy⟩ := hv _ jy e2
    have hr : 0 < lv.2.2.2 := by omega
    have e3 : getK lv.2.2.1 (P.img x lv.1) = getK lv.2.2.1 (P.img y lv.1) := by
      have := congrArg (· % lv.2.2.2) (ex.trans ey.symm)
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpx, Nat.mod_eq_of_lt hpy] at this
      exact this
    have ej := hinj _ jx _ jy e1 e2 e3
    have ek : kx = ky := by
      rw [e3] at ex
      have := ex.trans ey.symm
      exact Nat.eq_of_mul_eq_mul_left hr (by omega)
    have hσ' : P.code σ = getK lv.2.1 (P.img y lv.1) := ej ▸ hσ
    rw [← hσ, ek] at hx'
    rw [← hσ'] at hy'
    have fi : FC n (P.inv n (P.code σ)) := by
      rw [P.code_inv hn]
      exact fc_code hn _
    have := sift_inj hn C hC' (fc_mul hn fi fx) (fc_mul hn fi fy) hx' hy'
    rw [← mul_inv_mul hn σ fx, ← mul_inv_mul hn σ fy, this]

@[expose] noncomputable def okFrom (n : ℕ) (C : List Lvl) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun lv _ ih prev => CFSG.KC.Ord.andB
      (CFSG.KC.Ord.andB (P.allN n fun j => P.impB
          (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
          (P.letB (getK lv.2.1 j) fun u => CFSG.KC.Ord.andB (P.permK n u)
            (CFSG.KC.Ord.andB (P.allL prev fun b => Nat.beq (P.img u b) b)
              (CFSG.KC.Ord.andB (Nat.beq (P.img u lv.1) j)
                (Nat.blt (getK lv.2.2.1 j) lv.2.2.2)))))
        (Nat.beq (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.lor acc
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft 1 (getK lv.2.2.1 j)) 0
              (Nat.beq (getK lv.2.1 j) 0))) n)
          (Nat.sub (Nat.shiftLeft 1 lv.2.2.2) 1)))
      (ih (List.cons lv.1 prev)))
    C

theorem chainOK_eq (n : ℕ) (C : List Lvl) : chainOK n C = okFrom n C [] := rfl

@[expose] noncomputable def posMask (lv : Lvl) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.lor acc
    (Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft 1 (getK lv.2.2.1 j)) 0
      (Nat.beq (getK lv.2.1 j) 0))) m

theorem testBit_posMask (lv : Lvl) (i : ℕ) : ∀ m, (posMask lv m).testBit i = true ↔
    ∃ j < m, getK lv.2.1 j ≠ 0 ∧ getK lv.2.2.1 j = i
  | 0 => by simp [posMask]
  | m + 1 => by
    change (Nat.lor (posMask lv m) (Bool.rec (motive := fun _ => ℕ)
      (Nat.shiftLeft 1 (getK lv.2.2.1 m)) 0 (Nat.beq (getK lv.2.1 m) 0))).testBit i = true ↔ _
    by_cases e : getK lv.2.1 m = 0
    · rw [P.beq_iff.2 e]
      change (posMask lv m ||| 0).testBit i = true ↔ _
      rw [Nat.or_zero, testBit_posMask lv i m]
      constructor
      · rintro ⟨j, hj, h⟩
        exact ⟨j, by omega, h⟩
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ⟨j, hj, h⟩
        · exact absurd e h.1
    · rw [beq_false e]
      change (Nat.lor (posMask lv m) (Nat.shiftLeft 1 (getK lv.2.2.1 m))).testBit i = true ↔ _
      rw [P.lor_eq, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, testBit_posMask lv i m,
        decide_eq_true_iff]
      constructor
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, by omega, h⟩
        · exact ⟨m, by omega, e, h⟩
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inl ⟨j, hj, h⟩
        · exact Or.inr h.2

theorem validCnt_eq (U : List ℕ) : ∀ m,
    validCnt m U = ((Finset.range m).filter fun j => getK U j ≠ 0).card
  | 0 => rfl
  | m + 1 => by
    change validCnt m U + Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (getK U m) 0) = _
    rw [validCnt_eq U m, Finset.range_add_one, Finset.filter_insert]
    by_cases e : getK U m = 0
    · rw [P.beq_iff.2 e]
      simp [e]
    · rw [beq_false e]
      simp only [ne_eq, e, not_false_eq_true, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]

theorem lvOK_of {lv : Lvl} {prev : List ℕ}
    (h1 : P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
          (P.letB (getK lv.2.1 j) fun u => CFSG.KC.Ord.andB (P.permK n u)
            (CFSG.KC.Ord.andB (P.allL prev fun b => Nat.beq (P.img u b) b)
              (CFSG.KC.Ord.andB (Nat.beq (P.img u lv.1) j)
                (Nat.blt (getK lv.2.2.1 j) lv.2.2.2))))) = true)
    (h2 : Nat.beq (posMask lv n) (Nat.sub (Nat.shiftLeft 1 lv.2.2.2) 1) = true)
    (h3 : CFSG.KC.Ord.andB (Nat.blt 0 lv.2.2.2) (Nat.beq (validCnt n lv.2.1) lv.2.2.2) = true) :
    LvOK n lv := by
  rw [P.andB_iff, P.blt_iff, P.beq_iff] at h3
  rw [P.beq_iff] at h2
  rw [P.allN_iff] at h1
  have hv : ∀ j < n, getK lv.2.1 j ≠ 0 → (∃ σ : Perm (Fin n), P.code σ = getK lv.2.1 j) ∧
      getK lv.2.2.1 j < lv.2.2.2 := by
    intro j hj e
    have := h1 j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq, P.andB_iff, P.andB_iff, P.andB_iff,
      P.blt_iff] at this
    obtain ⟨hp, -, -, hlt⟩ := this e
    exact ⟨P.exists_of_permK hp, hlt⟩
  have hcov : ∀ i < lv.2.2.2, ∃ j < n, getK lv.2.1 j ≠ 0 ∧ getK lv.2.2.1 j = i := by
    intro i hi
    rw [← testBit_posMask lv i n, h2]
    change (1 <<< lv.2.2.2 - 1).testBit i = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hi
  have hpos : 0 < n := by
    obtain ⟨j, hj, -⟩ := hcov 0 h3.1
    omega
  refine ⟨hpos, hv, ?_⟩
  set V := (Finset.range n).filter fun j => getK lv.2.1 j ≠ 0
  have hcard : V.card = lv.2.2.2 := by
    rw [← validCnt_eq]
    exact h3.2
  have himg : V.image (getK lv.2.2.1) = Finset.range lv.2.2.2 := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_filter, Finset.mem_range] at hj
      exact Finset.mem_range.2 (hv j hj.1 hj.2).2
    · rw [Finset.card_range]
      calc lv.2.2.2 = (Finset.range lv.2.2.2).card := (Finset.card_range _).symm
        _ ≤ (V.image (getK lv.2.2.1)).card := Finset.card_le_card fun i hi => by
          obtain ⟨j, hj, e, rfl⟩ := hcov i (Finset.mem_range.1 hi)
          exact Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, e⟩, rfl⟩
  have hinj : Set.InjOn (getK lv.2.2.1) V := by
    rw [← Finset.card_image_iff, himg, Finset.card_range, hcard]
  intro j₁ hj₁ j₂ hj₂ e₁ e₂ e
  exact hinj (by simp [V, hj₁, e₁]) (by simp [V, hj₂, e₂]) e

theorem all_lvOK : ∀ (C : List Lvl) (prev : List ℕ), okFrom n C prev = true →
    chainInj n C = true → ∀ lv ∈ C, LvOK n lv
  | [], _, _, _ => fun _ h => absurd h List.not_mem_nil
  | lv :: C, prev, h, hI => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB _ (Nat.beq (posMask lv n) _))
      (okFrom n C (lv.1 :: prev)) = true at h
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt 0 lv.2.2.2)
      (Nat.beq (validCnt n lv.2.1) lv.2.2.2)) (chainInj n C) = true at hI
    rw [P.andB_iff, P.andB_iff] at h
    rw [P.andB_iff] at hI
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact lvOK_of h.1.1 h.1.2 hI.1
    · exact all_lvOK C _ h.2 hI.2 l hl

theorem idxM_inj (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) {F x y : ℕ} (fx : FC n x) (fy : FC n y)
    (hlt : idxM n C F x < F) (he : idxM n C F x = idxM n C F y) : x = y := by
  have hC := all_lvOK C [] (by rw [← chainOK_eq]; exact hok) hI
  rw [idxM_sift] at hlt he
  rw [idxM_sift] at he
  cases ex : sift n C x with
  | none => rw [ex] at hlt; exact absurd hlt (lt_irrefl F)
  | some k =>
    rw [ex] at hlt he
    cases ey : sift n C y with
    | none =>
      rw [ey] at he
      change k = F at he
      change k < F at hlt
      omega
    | some k' =>
      rw [ey] at he
      change k = k' at he
      subst he
      exact sift_inj hn C hC fx fy ex ey

theorem idxM_lt_chainF (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) {F x : ℕ} (fx : FC n x) (hlt : idxM n C F x < F) :
    idxM n C F x < chainF C := by
  have hC := all_lvOK C [] (by rw [← chainOK_eq]; exact hok) hI
  rw [idxM_sift] at hlt ⊢
  cases ex : sift n C x with
  | none => rw [ex] at hlt; exact absurd hlt (lt_irrefl F)
  | some k => exact sift_lt hn C hC fx ex

end CFSG.KC.LQT.CM

end
