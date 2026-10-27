module

public import Certificates.Data.Kernel.GMS78RuNM
public import CFSG.Certificates.Kernel.GMS78RuGenN
public import CFSG.Certificates.Kernel.GMS78RuNGlue

public section

namespace CFSG.KC.GMS.NG

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.GMS CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuN

theorem glList_closed : glList.length = 168 ∧
    allN 167 (fun k => Nat.blt (nIdxK (packV (glList.getD k linId)))
      (nIdxK (packV (glList.getD (k + 1) linId)))) = true ∧
    allN 168 (fun k => Nat.beq (glList.idxOf (glList.getD k linId)) k) = true := by
  decide +kernel

theorem glList_length : glList.length = 168 := glList_closed.1

theorem idxOf_getD {k : Nat} (hk : k < 168) : glList.idxOf (glList.getD k linId) = k :=
  Nat.eq_of_beq_eq_true (allN_of glList_closed.2.2 hk)

theorem mono_of_step {g : Nat → Nat} {n : Nat} (h : ∀ k, k + 1 < n → g k < g (k + 1)) :
    ∀ b, b < n → ∀ a, a < b → g a < g b := by
  intro b
  induction b with
  | zero => intro _ a ha; exact absurd ha (Nat.not_lt_zero a)
  | succ b ih =>
    intro hb a ha
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h' | h'
    · exact Nat.lt_trans (ih (by omega) a h') (h b hb)
    · rw [h']; exact h b hb

theorem mem_glList {R : Nat} (h : glK R = true) (hR : R < 512) :
    glList.idxOf (unV R) < 168 ∧ packV (glList.getD (glList.idxOf (unV R)) linId) = R := by
  obtain ⟨hm, -, -, -⟩ := glK_facts R h hR
  have hl := List.idxOf_lt_length_of_mem hm
  rw [glList_length] at hl
  refine ⟨hl, ?_⟩
  rw [getD_of_lt _ _ (by rw [glList_length]; exact hl), List.getElem_idxOf, packV_unV hR]

theorem enum_unique {n : Nat} {g f σ : Nat → Nat} (hg : ∀ k, k + 1 < n → g k < g (k + 1))
    (hf : ∀ i, i + 1 < n → f i < f (i + 1)) (hσ : ∀ i < n, σ i < n ∧ g (σ i) = f i) :
    ∀ i < n, σ i = i := by
  have hmono := mono_of_step hg
  have hinc : ∀ i, i + 1 < n → σ i < σ (i + 1) := by
    intro i hi
    have e := hf i hi
    rw [← (hσ i (by omega)).2, ← (hσ (i + 1) hi).2] at e
    rcases Nat.lt_or_ge (σ i) (σ (i + 1)) with h | h
    · exact h
    · exfalso
      rcases Nat.lt_or_eq_of_le h with h' | h'
      · have := hmono (σ i) (hσ i (by omega)).1 (σ (i + 1)) h'
        omega
      · rw [h'] at e
        omega
  have hge : ∀ i < n, i ≤ σ i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih => intro hi; exact Nat.lt_of_le_of_lt (ih (by omega)) (hinc i hi)
  have hle : ∀ k < n, σ (n - 1 - k) ≤ n - 1 - k := by
    intro k
    induction k with
    | zero =>
      intro h0
      have := (hσ (n - 1) (by omega)).1
      rw [Nat.sub_zero]
      omega
    | succ k ih =>
      intro hk
      have e1 := hinc (n - 1 - (k + 1)) (by omega)
      have e2 : n - 1 - (k + 1) + 1 = n - 1 - k := by omega
      rw [e2] at e1
      have := ih (by omega)
      omega
  intro i hi
  have h1 := hle (n - 1 - i) (by omega)
  have e : n - 1 - (n - 1 - i) = i := by omega
  rw [e] at h1
  exact Nat.le_antisymm h1 (hge i hi)

theorem gll_eq {GLL : Nat} (hG : gllOK GLL = true) : ∀ i < 168, gllAt GLL i = packV (glList.getD i linId) := by
  obtain ⟨h1, h⟩ := andB_true hG
  obtain ⟨h2, -⟩ := andB_true h
  have hσ : ∀ i < 168, glList.idxOf (unV (gllAt GLL i)) < 168 ∧
      packV (glList.getD (glList.idxOf (unV (gllAt GLL i))) linId) = gllAt GLL i := fun i hi =>
    mem_glList (allN_of h1 hi) (fget_lt GLL i 9)
  have key := enum_unique (n := 168) (g := fun k => nIdxK (packV (glList.getD k linId)))
    (f := fun i => nIdxK (gllAt GLL i)) (σ := fun i => glList.idxOf (unV (gllAt GLL i)))
    (fun k hk => Nat.le_of_ble_eq_true (allN_of glList_closed.2.1 (by omega)))
    (fun i hi => Nat.le_of_ble_eq_true (allN_of h2 (i := i) (by omega : i < 167)))
    (fun i hi => ⟨(hσ i hi).1, by rw [(hσ i hi).2]⟩)
  intro i hi
  rw [← (hσ i hi).2, key i hi]

theorem recIdx_go {α : Type} (P : α → Nat → Bool) (n : Nat) : ∀ (L : List α) (j : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
      (fun a _ ih i => andB (P a i) (ih (Nat.succ i))) L j = true →
    j + L.length = n ∧ ∀ i (h : i < L.length), P L[i] (j + i) = true := by
  intro L
  induction L with
  | nil => intro j h; exact ⟨Nat.eq_of_beq_eq_true h, fun i h => absurd h (Nat.not_lt_zero i)⟩
  | cons a L ih =>
    intro j h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨e, h3⟩ := ih (Nat.succ j) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ i =>
      rw [List.getElem_cons_succ]
      have := h3 i (by simp at hi; omega)
      have e2 : Nat.succ j + i = j + (i + 1) := by omega
      rwa [e2] at this

theorem recIdx {α : Type} {P : α → Nat → Bool} {n : Nat} {L : List α}
    (h : List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
      (fun a _ ih i => andB (P a i) (ih (Nat.succ i))) L 0 = true) :
    L.length = n ∧ ∀ i (hi : i < L.length), P L[i] i = true := by
  obtain ⟨e, h2⟩ := recIdx_go P n L 0 h
  refine ⟨by omega, fun i hi => ?_⟩
  have := h2 i hi
  rwa [Nat.zero_add] at this

theorem recAll {α : Type} {P : α → Bool} : ∀ {L : List α},
    List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (P a) ih) L = true → ∀ a ∈ L, P a = true
  | [], _, a, ha => by simp at ha
  | b :: L, h, a, ha => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h1
    · exact recAll h2 a ha

theorem nCode_nIdx (r : Lin8) : nCode (nIdx r) = r := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := r
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> simp [nCode, nIdx] <;> omega

theorem nIdx_lt (r : Lin8) : nIdx r < 512 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := r
  simp only [nIdx]
  omega

theorem indep3_glK : allN 512 (fun R => Nat.beq (Bool.rec (motive := fun _ => Nat) 0 1 (glK R))
    (Bool.rec (motive := fun _ => Nat) 0 1 (indep3 (unV R).1 (unV R).2.1 (unV R).2.2))) = true := by
  decide +kernel

theorem indep3_eq (r : Lin8) : indep3 r.1 r.2.1 r.2.2 = glK (packV r) := by
  have := Nat.eq_of_beq_eq_true (allN_of indep3_glK (packV_lt r))
  rw [unV_packV] at this
  cases h1 : indep3 r.1 r.2.1 r.2.2 <;> cases h2 : glK (packV r) <;> simp_all

theorem selN_zero_tab (n c : Nat) : selN n c (fun k => fget 0 k 8) = 0 := by
  rw [selN_congr (g := fun _ => 0) fun k _ => by rw [fget_eq, Nat.zero_shiftRight, Nat.zero_mod]]
  exact selN_zero_fun n c

structure Facts (nbt ntw : List (List (Fin 8))) (nc nb : List Nat) (GLL TW ADC TAU INV : Nat) : Prop where
  hNBT : ∀ j < 8, ∀ i < 8, (Gen.nBT nbt j i).val = fget NBT (8 * j + i) 3
  hNC : ∀ k < 8, nc.getD k 0 = fget NCOLS k 8
  hNB : ∀ k < 8, nb.getD k 0 = fget NBAS k 8
  hI : invTabOK INV = true
  hTW : ∀ r ∈ glList, ∀ j < 8, ((ntw.getD (glList.idxOf r) []).getD j 0).val = fget (fget TW (packV r) 24) j 3
  hR : ∀ r ∈ glList, nmR GLL INV TW ADC TAU (packV r) = true
  hZ : zeroOK ADC TAU = true

theorem tauF_lt (T G m : Nat) : tauF T G m < 8 := by
  change Nat.xor (xs8K _ _) (xs8K _ _) < 2 ^ 3
  rw [xs8K_eq, xs8K_eq]
  exact Nat.xor_lt_two_pow (selN_lt fun _ _ => fget_lt _ _ 3)
    (selN_lt fun _ _ => by rw [xs8K_eq]; exact selN_lt fun _ _ => fget_lt _ _ 3)

theorem rOK_facts {INV TW ADC TAU R : Nat} (h : rOK INV TW ADC TAU R = true) :
    fget ADC R 64 = adK R (fget INV R 9) ∧
      ∀ m < 256, tauA TAU R m = tauF (fget TW R 24) (gamTab R (adK R (fget INV R 9))) m := by
  simp only [rOK, strictB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun m hm => ?_⟩
  rw [tauA, Nat.eq_of_beq_eq_true h2]
  exact fget_orN 3 256 _ (fun _ _ => tauF_lt _ _ _) m hm

theorem arr_get! {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (h : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by rw [Array.size_ofFn]; exact h), Array.getElem_ofFn]

theorem empty_get! {α : Type} [Inhabited α] (i : Nat) : (#[] : Array α)[i]! = default :=
  getElem!_neg (#[] : Array α) i (by simp)

theorem xs8_congr (c : Nat) {f g : Nat → Fin 8} (h : ∀ j < 8, f j = g j) :
    CFSG.GMS78RuN.xs8 c f = CFSG.GMS78RuN.xs8 c g := by
  simp only [CFSG.GMS78RuN.xs8, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem zero_facts {ADC TAU R : Nat} (hZ : zeroOK ADC TAU = true) (hR : R < 512) (h : glK R = false) :
    fget ADC R 64 = 0 ∧ fget TAU R 768 = 0 := by
  have := allN_of hZ hR
  rw [h, orB_eq, Bool.false_or] at this
  obtain ⟨h1, h2⟩ := andB_true this
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

section Tables

variable {nbt ntw : List (List (Fin 8))} {nc nb : List Nat} {GLL TW ADC TAU INV : Nat}

theorem Facts.rok (F : Facts nbt ntw nc nb GLL TW ADC TAU INV) {r : Lin8} (hr : r ∈ glList) :
    rOK INV TW ADC TAU (packV r) = true :=
  (andB_true (F.hR r hr)).1

theorem Facts.mem (r : Lin8) (hg : glK (packV r) = true) : r ∈ glList := by
  have := (glK_facts (packV r) hg (packV_lt r)).1
  rwa [unV_packV] at this

theorem coArr_eq (F : Facts nbt ntw nc nb GLL TW ADC TAU INV) {m : Nat} (hm : m < 256) :
    (Gen.nCoArr nc)[m]! = maskAppK NCOLS m := by
  simp only [Gen.nCoArr]
  rw [arr_get! _ hm]
  exact maskApply_eq_maskAppK F.hNC m

theorem betaArr_val (F : Facts nbt ntw nc nb GLL TW ADC TAU INV) {x y : Nat} (hx : x < 256) (hy : y < 256) :
    ((Gen.nBetaArr nbt nc)[x * 256 + y]!).val = nBetaK x y := by
  simp only [Gen.nBetaArr]
  rw [arr_get! _ (by omega : x * 256 + y < 65536)]
  have e1 : (x * 256 + y) / 256 = x := by omega
  have e2 : (x * 256 + y) % 256 = y := by omega
  simp only [e1, e2, Gen.nBetaF]
  rw [xs8_val, coArr_eq F hx, nBetaK_eq]
  apply selN_congr
  intro j hj
  simp only [Gen.nRowArr]
  rw [arr_get! _ (by omega : 256 * j + y < 2048)]
  have e3 : (256 * j + y) % 256 = y := by omega
  have e4 : (256 * j + y) / 256 = j := by omega
  simp only [e3, e4]
  rw [xs8_val, coArr_eq F hy]
  exact selN_congr fun i hi => F.hNBT j hj i hi

theorem adTab_eq (F : Facts nbt ntw nc nb GLL TW ADC TAU INV) (r : Lin8) {m : Nat} (hm : m < 256) :
    (nAdTab[nIdx r]!)[m]! = adA ADC (packV r) m := by
  simp only [nAdTab]
  rw [arr_get! _ (nIdx_lt r)]
  simp only [nCode_nIdx, indep3_eq]
  cases hg : glK (packV r)
  · rw [ite_eq_right (by simp), empty_get!, adA, (zero_facts F.hZ (packV_lt r) hg).1, maskAppK_eq,
      selN_zero_tab]
    rfl
  · rw [ite_eq_left rfl]
    simp only [nAdArr]
    rw [arr_get! _ hm, adA, (rOK_facts (F.rok (Facts.mem r hg))).1]
    have := nAd_eq F.hI hg (packV_lt r) m
    rw [unV_packV] at this
    exact this

theorem adTab_lt (F : Facts nbt ntw nc nb GLL TW ADC TAU INV) (r : Lin8) {m : Nat} (hm : m < 256) :
    (nAdTab[nIdx r]!)[m]! < 256 := by
  rw [adTab_eq F r hm]
  exact maskAppK_lt _ _

theorem tauTab_val (F : Facts nbt ntw nc nb GLL TW ADC TAU INV) (r : Lin8) {m : Nat} (hm : m < 256) :
    (((Gen.nTauTab nbt ntw nc nb)[nIdx r]!)[m]!).val = tauA TAU (packV r) m := by
  simp only [Gen.nTauTab]
  rw [arr_get! _ (nIdx_lt r)]
  simp only [nCode_nIdx, indep3_eq]
  cases hg : glK (packV r)
  · rw [ite_eq_right (by simp), empty_get!, tauA, (zero_facts F.hZ (packV_lt r) hg).2, fget_eq,
      Nat.zero_shiftRight, Nat.zero_mod]
    rfl
  · rw [ite_eq_left rfl]
    have hr := Facts.mem r hg
    obtain ⟨hA, hT⟩ := rOK_facts (F.rok hr)
    rw [hT m hm]
    simp only [Gen.nTauArrW]
    rw [arr_get! _ hm]
    simp only
    rw [fxor_val, xs8_val, xs8_val, coArr_eq F hm]
    change _ = (xs8K (maskAppK NCOLS m) fun j => fget (fget TW (packV r) 24) j 3) ^^^
      (xs8K (maskAppK NCOLS m) fun j => xs8K (maskAppK NCOLS m) fun i =>
        fget (gamTab (packV r) (adK (packV r) (fget INV (packV r) 9))) (8 * i + j) 3)
    rw [xs8K_eq, xs8K_eq]
    congr 1
    · exact selN_congr fun j hj => F.hTW r hr j hj
    · apply selN_congr
      intro j hj
      rw [xs8_val, xs8K_eq]
      apply selN_congr
      intro i hi
      rw [fite_val, gamTab_fget _ _ hi hj]
      by_cases hij : i < j
      · rw [ite_eq_left hij, ite_eq_left hij]
        simp only [Gen.nGamBArr]
        rw [arr_get! _ (by omega : 8 * i + j < 64)]
        have e1 : (8 * i + j) / 8 = i := by omega
        have e2 : (8 * i + j) % 8 = j := by omega
        have hbi : Gen.nB nb i = fget NBAS i 8 := F.hNB i hi
        have hbj : Gen.nB nb j = fget NBAS j 8 := F.hNB j hj
        have hi8 : fget NBAS i 8 < 256 := fget_lt NBAS i 8
        have hj8 : fget NBAS j 8 < 256 := fget_lt NBAS j 8
        simp only [e1, e2, hbi, hbj]
        rw [fxor_val, betaArr_val F (adTab_lt F r hi8) (adTab_lt F r hj8), linApply_val,
          betaArr_val F hi8 hj8, adTab_eq F r hi8, adTab_eq F r hj8]
        simp only [adA, hA]
      · rw [ite_eq_right hij, ite_eq_right hij]

theorem lor_shl_gen {x : Nat} (y k : Nat) (hx : x < 2 ^ k) : x ||| (y <<< k) = y * 2 ^ k + x := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]

theorem lor3_eq {x t : Nat} (R : Nat) (hx : x < 256) (ht : t < 8) :
    Nat.lor x (Nat.lor (Nat.shiftLeft t 8) (Nat.shiftLeft R 11)) = x + 256 * t + 2048 * R := by
  change x ||| ((t <<< 8) ||| (R <<< 11)) = _
  have h8 : (2 : Nat) ^ 8 = 256 := rfl
  have h11 : (2 : Nat) ^ 11 = 2048 := rfl
  have h1 : t <<< 8 < 2 ^ 11 := by
    rw [Nat.shiftLeft_eq, h8, h11]
    omega
  rw [lor_shl_gen R 11 h1]
  have h2 : R * 2 ^ 11 + t <<< 8 = (R * 8 + t) <<< 8 := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, h8, h11]
    omega
  rw [h2, lor_shl_gen _ 8 hx, h8]
  clear h1 h2 h8 h11
  omega

theorem packT_eq (m : Nat) (t : Fin 8) (r : Lin8) (hm : m < 256) :
    packT (m, t, r) = m + 256 * t.val + 2048 * packV r :=
  lor3_eq (packV r) hm t.isLt

theorem tr_pack (m : Nat) (t : Fin 8) (r : Lin8) (hm : m < 256) :
    trM (packT (m, t, r)) = m ∧ trT (packT (m, t, r)) = t.val ∧ trR (packT (m, t, r)) = packV r := by
  have e := packT_eq m t r hm
  have ht := t.isLt
  have hr := packV_lt r
  have h8 : (2 : Nat) ^ 8 = 256 := rfl
  have h3 : (2 : Nat) ^ 3 = 8 := rfl
  have h11 : (2 : Nat) ^ 11 = 2048 := rfl
  refine ⟨?_, ?_, ?_⟩
  · change fget (packT (m, t, r)) 0 8 = m
    rw [fget_eq, Nat.zero_mul, Nat.shiftRight_zero, e, h8]
    omega
  · change fget (packT (m, t, r) >>> 8) 0 3 = t.val
    rw [fget_eq, Nat.zero_mul, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow, e, h8, h3]
    omega
  · change packT (m, t, r) >>> 11 = packV r
    rw [e, Nat.shiftRight_eq_div_pow, h11]
    omega

theorem packT_inj {p q : NTrip} (hp : p.1 < 256) (hq : q.1 < 256) (h : packT p = packT q) : p = q := by
  obtain ⟨m, t, r⟩ := p
  obtain ⟨m', t', r'⟩ := q
  obtain ⟨h1, h2, h3⟩ := tr_pack m t r hp
  obtain ⟨g1, g2, g3⟩ := tr_pack m' t' r' hq
  rw [h] at h1 h2 h3
  have em : m = m' := h1.symm.trans g1
  have et : t = t' := Fin.ext (h2.symm.trans g2)
  have er : r = r' := packV_inj (h3.symm.trans g3)
  rw [em, et, er]

theorem ONET_eq : ONET = packT nOneT := by decide +kernel

theorem mulT_pack (F : Facts nbt ntw nc nb GLL TW ADC TAU INV) (p q : NTrip) (hp : p.1 < 256) (hq : q.1 < 256) :
    mulT ADC TAU (packT p) (packT q) = packT (Gen.nMulT nbt ntw nc nb p q) ∧
      (Gen.nMulT nbt ntw nc nb p q).1 < 256 := by
  obtain ⟨m, t, r⟩ := p
  obtain ⟨m', t', r'⟩ := q
  simp only at hp hq
  obtain ⟨h1, h2, h3⟩ := tr_pack m t r hp
  obtain ⟨g1, g2, g3⟩ := tr_pack m' t' r' hq
  have ham := adTab_lt F r hq
  have hx : m ^^^ (nAdTab[nIdx r]!)[m']! < 256 := Nat.xor_lt_two_pow (n := 8) hp ham
  refine ⟨?_, hx⟩
  simp only [Gen.nMulT]
  rw [packT_eq _ _ _ hx]
  simp only [mulT, h1, h2, h3, g1, g2, g3]
  have hx' : Nat.xor m (adA ADC (packV r) m') < 256 := Nat.xor_lt_two_pow (n := 8) hp (maskAppK_lt _ _)
  have hv : Nat.xor (Nat.xor t.val (Nat.xor (linAppK (packV r) t'.val) (tauA TAU (packV r) m')))
      (nBetaK m (adA ADC (packV r) m')) < 8 :=
    Nat.xor_lt_two_pow (n := 3) (Nat.xor_lt_two_pow (n := 3) t.isLt
      (Nat.xor_lt_two_pow (n := 3) (linAppK_lt (packV r) t'.val) (fget_lt _ m' 3))) (nBetaK_lt m _)
  refine (lor3_eq (linCompK (packV r) (packV r')) hx' hv).trans ?_
  have hA : adA ADC (packV r) m' < 256 := maskAppK_lt _ _
  rw [adTab_eq F r hq, fxor_val, fxor_val, fxor_val, linApply_val, tauTab_val F r hq,
    betaArr_val F hp hA, ← linComp_pack]
  rfl

end Tables

theorem smallM_spec : ∀ {L : List NTrip}, smallM L = true → ∀ p ∈ L, p.1 < 256
  | [], _, p, hp => by simp at hp
  | (m, x) :: L, h, p, hp => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Nat.le_of_ble_eq_true h1
    · exact smallM_spec h2 p hp

theorem getD_mem {α : Type} {L : List α} {i : Nat} (d : α) (hi : i < L.length) : L.getD i d ∈ L := by
  rw [getD_of_lt _ _ hi]
  exact List.getElem_mem hi

theorem bindImg_facts {img imgInv rT : List NTrip} {NIMG NIMGI NRT : Nat}
    (h : bindImg img imgInv rT NIMG NIMGI NRT = true) :
    (∀ i < 7, packT (img.getD i nOneT) = fget NIMG i 20 ∧ (img.getD i nOneT).1 < 256) ∧
    (∀ i < 7, packT (imgInv.getD i nOneT) = fget NIMGI i 20 ∧ (imgInv.getD i nOneT).1 < 256) ∧
    rT.length = 11 ∧ (∀ i < 11, packT (rT.getD i nOneT) = fget NRT i 20) := by
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h5⟩ := andB_true h
  have l1 : img.length = 7 := (bindList_get h1).1
  have l2 : imgInv.length = 7 := (bindList_get h2).1
  exact ⟨fun i hi => ⟨bindList_getD h1 nOneT hi, smallM_spec h4 _ (getD_mem _ (by omega))⟩,
    fun i hi => ⟨bindList_getD h2 nOneT hi, smallM_spec h5 _ (getD_mem _ (by omega))⟩,
    (bindList_get h3).1, fun i hi => bindList_getD h3 nOneT hi⟩

theorem wordOfCodes_cons (c : Nat) (w : List Nat) :
    CFSG.CosetTable.wordOfCodes 7 (c :: w) =
      (if h : c < 14 then [((⟨c / 2, by omega⟩ : Fin 7), c % 2 == 0)] else []) ++
        CFSG.CosetTable.wordOfCodes 7 w := by
  unfold CFSG.CosetTable.wordOfCodes
  rw [List.flatMap_cons]
  congr 1
  split
  · next h => interval_cases c <;> rfl
  · next h =>
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro i _
    have := i.isLt
    simp only [decide_eq_true_eq]
    omega

@[expose] noncomputable def evalCgo (ADC TAU NIMG NIMGI : Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (nIf(Nat.blt c 14, mulT ADC TAU x (sgnK NIMG NIMGI c), x)) ih) w x

theorem evalCgo_cons (ADC TAU NIMG NIMGI c : Nat) (w : List Nat) (x : Nat) :
    evalCgo ADC TAU NIMG NIMGI (c :: w) x =
      evalCgo ADC TAU NIMG NIMGI w (nIf(Nat.blt c 14, mulT ADC TAU x (sgnK NIMG NIMGI c), x)) := by
  unfold evalCgo
  exact strictN_eq _ _

theorem evalC_eq (ADC TAU NIMG NIMGI : Nat) (w : List Nat) :
    evalC ADC TAU NIMG NIMGI w = evalCgo ADC TAU NIMG NIMGI w ONET := rfl

@[expose] noncomputable def evalSgo (ADC TAU NIMG NIMGI : Nat) (w : List (Fin 7 × Bool)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (Prod.rec (motive := fun _ => Nat) (fun i s =>
      mulT ADC TAU x (nIf(s, fget NIMG i.val 20, fget NIMGI i.val 20))) l) ih) w x

theorem evalSgo_cons (ADC TAU NIMG NIMGI : Nat) (i : Fin 7) (s : Bool) (w : List (Fin 7 × Bool)) (x : Nat) :
    evalSgo ADC TAU NIMG NIMGI ((i, s) :: w) x =
      evalSgo ADC TAU NIMG NIMGI w (mulT ADC TAU x (nIf(s, fget NIMG i.val 20, fget NIMGI i.val 20))) := by
  unfold evalSgo
  exact strictN_eq _ _

theorem evalS_eq (ADC TAU NIMG NIMGI : Nat) (w : List (Fin 7 × Bool)) :
    evalS ADC TAU NIMG NIMGI w = evalSgo ADC TAU NIMG NIMGI w ONET := rfl

section Words

variable {GLL TW ADC TAU INV : Nat} {nbt ntw : List (List (Fin 8))} {nc nb : List Nat}
  {img imgInv : List NTrip} {NIMG NIMGI : Nat}

theorem sign_pack (hI1 : ∀ i < 7, packT (img.getD i nOneT) = fget NIMG i 20 ∧ (img.getD i nOneT).1 < 256)
    (hI2 : ∀ i < 7, packT (imgInv.getD i nOneT) = fget NIMGI i 20 ∧ (imgInv.getD i nOneT).1 < 256)
    (i : Fin 7) (s : Bool) :
    nIf(s, fget NIMG i.val 20, fget NIMGI i.val 20) = packT (Gen.nSign img imgInv (i, s)) ∧
      (Gen.nSign img imgInv (i, s)).1 < 256 := by
  cases s
  · exact ⟨(hI2 i.val i.isLt).1.symm, (hI2 i.val i.isLt).2⟩
  · exact ⟨(hI1 i.val i.isLt).1.symm, (hI1 i.val i.isLt).2⟩

theorem sgnK_pack (hI1 : ∀ i < 7, packT (img.getD i nOneT) = fget NIMG i 20 ∧ (img.getD i nOneT).1 < 256)
    (hI2 : ∀ i < 7, packT (imgInv.getD i nOneT) = fget NIMGI i 20 ∧ (imgInv.getD i nOneT).1 < 256)
    {c : Nat} (hc : c < 14) :
    sgnK NIMG NIMGI c = packT (Gen.nSign img imgInv ((⟨c / 2, by omega⟩ : Fin 7), c % 2 == 0)) ∧
      (Gen.nSign img imgInv ((⟨c / 2, by omega⟩ : Fin 7), c % 2 == 0)).1 < 256 := by
  have := sign_pack hI1 hI2 ⟨c / 2, by omega⟩ (c % 2 == 0)
  rw [← this.1]
  refine ⟨?_, this.2⟩
  unfold sgnK
  rw [nIf_eq]
  change (if Nat.beq (c % 2) 0 = true then fget NIMG (c / 2) 20 else fget NIMGI (c / 2) 20) = _
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

theorem evalC_pack (F : Facts nbt ntw nc nb GLL TW ADC TAU INV)
    (hI1 : ∀ i < 7, packT (img.getD i nOneT) = fget NIMG i 20 ∧ (img.getD i nOneT).1 < 256)
    (hI2 : ∀ i < 7, packT (imgInv.getD i nOneT) = fget NIMGI i 20 ∧ (imgInv.getD i nOneT).1 < 256) :
    ∀ (w : List Nat) (X : NTrip), X.1 < 256 →
      evalCgo ADC TAU NIMG NIMGI w (packT X) = packT ((CFSG.CosetTable.wordOfCodes 7 w).foldl
        (fun x p => Gen.nMulT nbt ntw nc nb x (Gen.nSign img imgInv p)) X) ∧
      ((CFSG.CosetTable.wordOfCodes 7 w).foldl
        (fun x p => Gen.nMulT nbt ntw nc nb x (Gen.nSign img imgInv p)) X).1 < 256
  | [], X, hX => ⟨rfl, hX⟩
  | c :: w, X, hX => by
    rw [evalCgo_cons, wordOfCodes_cons, List.foldl_append]
    by_cases hc : c < 14
    · have hb : Nat.blt c 14 = true := Nat.ble_eq_true_of_le hc
      obtain ⟨hs, hsl⟩ := sgnK_pack hI1 hI2 hc
      obtain ⟨hm, hml⟩ := mulT_pack F X _ hX hsl
      rw [hb, dite_eq_left hc, List.foldl_cons, List.foldl_nil, hs, hm]
      exact evalC_pack F hI1 hI2 w _ hml
    · have hb : Nat.blt c 14 = false := by
        cases e : Nat.blt c 14
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true e) hc
      rw [hb, dite_eq_right hc, List.foldl_nil]
      exact evalC_pack F hI1 hI2 w X hX

theorem evalS_pack (F : Facts nbt ntw nc nb GLL TW ADC TAU INV)
    (hI1 : ∀ i < 7, packT (img.getD i nOneT) = fget NIMG i 20 ∧ (img.getD i nOneT).1 < 256)
    (hI2 : ∀ i < 7, packT (imgInv.getD i nOneT) = fget NIMGI i 20 ∧ (imgInv.getD i nOneT).1 < 256) :
    ∀ (w : List (Fin 7 × Bool)) (X : NTrip), X.1 < 256 →
      evalSgo ADC TAU NIMG NIMGI w (packT X) =
        packT (w.foldl (fun x p => Gen.nMulT nbt ntw nc nb x (Gen.nSign img imgInv p)) X) ∧
      (w.foldl (fun x p => Gen.nMulT nbt ntw nc nb x (Gen.nSign img imgInv p)) X).1 < 256
  | [], X, hX => ⟨rfl, hX⟩
  | (i, s) :: w, X, hX => by
    rw [evalSgo_cons, List.foldl_cons]
    obtain ⟨hs, hsl⟩ := sign_pack hI1 hI2 i s
    obtain ⟨hm, hml⟩ := mulT_pack F X _ hX hsl
    rw [hs, hm]
    exact evalS_pack F hI1 hI2 w _ hml

end Words

@[expose] noncomputable def qF (G c : Nat) : Nat := selN 8 c fun j => selN 8 c fun i => fget G (8 * i + j) 3

@[expose] noncomputable def pF (G c d : Nat) : Nat :=
  (selN 8 c fun j => selN 8 d fun i => fget G (8 * i + j) 3) ^^^
    (selN 8 d fun j => selN 8 c fun i => fget G (8 * i + j) 3)

theorem tauF_eq (T G m : Nat) :
    tauF T G m = (selN 8 (maskAppK NCOLS m) fun j => fget T j 3) ^^^ qF G (maskAppK NCOLS m) := by
  simp only [tauF, xs8K_eq, qF]
  rfl

theorem maskAppK_xor (A x y : Nat) : maskAppK A (x ^^^ y) = maskAppK A x ^^^ maskAppK A y := by
  rw [maskAppK_eq, maskAppK_eq, maskAppK_eq, selN_xor_set]

theorem qF_xor (G c d : Nat) : qF G (c ^^^ d) = qF G c ^^^ qF G d ^^^ pF G c d := by
  simp only [qF, pF, selN_xor_set, selN_xor_fun]
  ac_rfl

theorem tauF_xor (T G m m' : Nat) :
    tauF T G (m ^^^ m') = tauF T G m ^^^ tauF T G m' ^^^ pF G (maskAppK NCOLS m) (maskAppK NCOLS m') := by
  rw [tauF_eq, tauF_eq, tauF_eq, maskAppK_xor, selN_xor_set, qF_xor]
  ac_rfl

theorem pF_xor_left (G c c' d : Nat) : pF G (c ^^^ c') d = pF G c d ^^^ pF G c' d := by
  simp only [pF, selN_xor_set, selN_xor_fun]
  ac_rfl

theorem maskAppK_zero (A : Nat) : maskAppK A 0 = 0 := by
  rw [maskAppK_eq, selN_zero_set]

theorem pF_zero_left (G d : Nat) : pF G 0 d = 0 := by
  simp only [pF, selN_zero_set, selN_zero_fun, Nat.xor_zero]

theorem nBetaK_xor_left (x x' y : Nat) : nBetaK (x ^^^ x') y = nBetaK x y ^^^ nBetaK x' y := by
  rw [nBetaK_eq, nBetaK_eq, nBetaK_eq, maskAppK_xor, selN_xor_set]

theorem nBetaK_zero_left (y : Nat) : nBetaK 0 y = 0 := by
  rw [nBetaK_eq, maskAppK_zero, selN_zero_set]

theorem linAppK_xor (R a b : Nat) : linAppK R (a ^^^ b) = linAppK R a ^^^ linAppK R b := by
  rw [linAppK_eq, linAppK_eq, linAppK_eq, selN_xor_set]

theorem linAppK_zero (R : Nat) : linAppK R 0 = 0 := by
  rw [linAppK_eq, selN_zero_set]

@[expose] noncomputable def dQ (R A G m b : Nat) : Nat :=
  pF G (maskAppK NCOLS m) (maskAppK NCOLS b) ^^^
    (nBetaK (maskAppK A m) (maskAppK A b) ^^^ linAppK R (nBetaK m b))

theorem dQ_xor (R A G m m' b : Nat) : dQ R A G (m ^^^ m') b = dQ R A G m b ^^^ dQ R A G m' b := by
  simp only [dQ, maskAppK_xor, pF_xor_left, nBetaK_xor_left, linAppK_xor]
  ac_rfl

theorem dQ_zero (R A G b : Nat) : dQ R A G 0 b = 0 := by
  simp only [dQ, maskAppK_zero, pF_zero_left, nBetaK_zero_left, linAppK_zero, Nat.xor_zero]

theorem dQ_sel (R A G b : Nat) (s : Nat) (f : Nat → Nat) :
    ∀ n, dQ R A G (selN n s f) b = selN n s fun i => dQ R A G (f i) b := by
  intro n
  induction n with
  | zero => rw [selN_zero, selN_zero, dQ_zero]
  | succ n ih =>
    rw [selN_succ, selN_succ, dQ_xor, ih]
    congr 1
    split
    · rfl
    · exact dQ_zero R A G b

theorem xor_cancel_left (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  have e : a ^^^ (a ^^^ b) = a ^^^ (a ^^^ c) := by rw [h]
  rwa [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.zero_xor] at e

theorem quad_iff (R A T G m b : Nat) :
    tauF T G (m ^^^ b) = tauF T G m ^^^ tauF T G b ^^^
      (nBetaK (maskAppK A m) (maskAppK A b) ^^^ linAppK R (nBetaK m b)) ↔ dQ R A G m b = 0 := by
  rw [tauF_xor, dQ]
  constructor
  · intro h
    rw [xor_cancel_left _ _ _ h, Nat.xor_self]
  · intro h
    have e : pF G (maskAppK NCOLS m) (maskAppK NCOLS b) =
        nBetaK (maskAppK A m) (maskAppK A b) ^^^ linAppK R (nBetaK m b) := by
      have := congrArg (· ^^^ (nBetaK (maskAppK A m) (maskAppK A b) ^^^ linAppK R (nBetaK m b))) h
      simp only [Nat.zero_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
      exact this
    rw [e]

theorem quad_of {R A T G : Nat}
    (hq : ∀ i < 8, ∀ j < 8, tauF T G (fget NBAS i 8 ^^^ fget NBAS j 8) =
      tauF T G (fget NBAS i 8) ^^^ tauF T G (fget NBAS j 8) ^^^
        (nBetaK (maskAppK A (fget NBAS i 8)) (maskAppK A (fget NBAS j 8)) ^^^
          linAppK R (nBetaK (fget NBAS i 8) (fget NBAS j 8))))
    (hid : ∀ m < 256, maskAppK NBAS (maskAppK NCOLS m) = m) {m j : Nat} (hm : m < 256) (hj : j < 8) :
    tauF T G (m ^^^ fget NBAS j 8) = tauF T G m ^^^ tauF T G (fget NBAS j 8) ^^^
      (nBetaK (maskAppK A m) (maskAppK A (fget NBAS j 8)) ^^^
        linAppK R (nBetaK m (fget NBAS j 8))) := by
  rw [quad_iff]
  have e := hid m hm
  rw [maskAppK_eq] at e
  rw [← e, dQ_sel]
  rw [selN_congr (g := fun _ => 0) fun i hi => (quad_iff R A T G _ _).1 (hq i hi j hj)]
  exact selN_zero_fun 8 _

end CFSG.KC.GMS.NG

end
