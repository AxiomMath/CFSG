module

public import Certificates.Data.Kernel.Spor.ONPwK
public import CFSG.Certificates.Kernel.Spor.ONPvSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.ONPw

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONNQ CFSG.KS.ONPv

abbrev PwItems (D : Nat → Nat) : Prop :=
  (∀ j < 13, Lm 7 (wd (D j))) ∧ ∀ j < 49, Lm 3 (wd (D (13 + j)))

@[expose] def sI (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (j : Nat) :
    Equiv.Perm (Fin 245520) :=
  wv g (wd (D j))

@[expose] def hV (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (v : Nat) :
    Equiv.Perm (Fin 245520) :=
  wv (sI g D) (wd v)

@[expose] def cj (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (j : Nat) :
    Equiv.Perm (Fin 245520) :=
  (sI g D 12)⁻¹ * sI g D j * sI g D 12

@[expose] def kp (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (j : Nat) :
    Equiv.Perm (Fin 245520) :=
  cj g D (8 + j)

@[expose] def xp (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) : Equiv.Perm (Fin 245520) :=
  cj g D 7

@[expose] def yp (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) : Equiv.Perm (Fin 245520) :=
  cj g D 6

@[expose] def bE (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (e j : Nat) :
    Equiv.Perm (Fin 245520) :=
  hV g D (D (13 + 3 * e + j))

@[expose] def bY (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (e : Nat) :
    Equiv.Perm (Fin 245520) :=
  wv (bE g D e) (wd (D 61))

@[expose] def fWP {n : Nat} (a k : Nat → Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  a 0 * k 3 * k 2 * k 1 * a 2 * a 2 * k 1 * a 2 * a 0 * k 2

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem nbeq {a b : Nat} (h : Bool.not (Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

private theorem bIf_or {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) b true a = true) :
    a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem pw_eq {n : Nat} {f : Nat → Nat} {σ : Equiv.Perm (Fin n)}
    (hf : ∀ x : Fin n, f x = (σ x : Nat)) : ∀ (k : Nat) (x : Fin n), pw f k x = ((σ ^ k) x : Nat)
  | 0, x => by
    rw [pow_zero]
    rfl
  | k + 1, x => by
    change strictN (f x) (pw f k) = _
    rw [sN, hf x, pw_eq hf k (σ x), pow_succ, Equiv.Perm.mul_apply]

theorem fW_eq {n : Nat} {A K : Nat → Nat → Nat} {a k : Nat → Equiv.Perm (Fin n)}
    (hA : ∀ j < 3, ∀ x : Fin n, A j x = (a j x : Nat))
    (hK : ∀ j < 4, ∀ x : Fin n, K j x = (k j x : Nat)) (x : Fin n) :
    fW A K x = (fWP a k x : Nat) := by
  unfold fW
  simp only [sN]
  rw [hK 2 (by omega) x, hA 0 (by omega), hA 2 (by omega), hK 1 (by omega), hA 2 (by omega),
    hA 2 (by omega), hK 1 (by omega), hK 2 (by omega), hK 3 (by omega), hA 0 (by omega)]
  simp only [fWP, Equiv.Perm.mul_apply]

section Words

variable {TT UU : Nat → Nat → Nat} {D : Nat → Nat} {g : Nat → Equiv.Perm (Fin 245520)}

theorem pw_lm3 (hP : PwItems D) (j : Nat) (h1 : 13 ≤ j := by omega) (h2 : j < 62 := by omega) :
    Lm 3 (wd (D j)) := by
  have := hP.2 (j - 13) (by omega)
  rwa [show 13 + (j - 13) = j by omega] at this

theorem rp_s (hR : Rp TT UU g 7) (hP : PwItems D) :
    Rp (sT TT UU D) (sU TT UU D) (sI g D) 13 :=
  fun k hk x => ⟨iT_eq hR (hP.1 k hk) x, iU_eq hR (hP.1 k hk) x⟩

theorem hW_eq (hR : Rp TT UU g 7) (hP : PwItems D) {v : Nat} (hv : Lm 3 (wd v)) (x : Fin 245520) :
    hW TT UU D v x = (hV g D v x : Nat) :=
  iT_eq (rp_s hR hP) (Lm_mono (by omega) hv) x

theorem cjA_eq (hR : Rp TT UU g 7) (hP : PwItems D) {j : Nat} (hj : j < 13) (x : Fin 245520) :
    cjA TT UU D j x = (cj g D j x : Nat) := by
  have hS := rp_s hR hP
  unfold cjA
  simp only [sN]
  change sU TT UU D 12 (sT TT UU D j (sT TT UU D 12 x)) = _
  rw [(hS 12 (by omega) x).1, (hS j hj _).1, (hS 12 (by omega) _).2]
  simp only [cj, Equiv.Perm.mul_apply]

theorem kA_eq (hR : Rp TT UU g 7) (hP : PwItems D) {j : Nat} (hj : j < 4) (x : Fin 245520) :
    kA TT UU D j x = (kp g D j x : Nat) :=
  cjA_eq hR hP (j := 8 + j) (by omega) x

variable {K : Subgroup (Equiv.Perm (Fin 245520))}

theorem sI_mem (hK : ∀ k < 7, g k ∈ K) (hP : PwItems D) {j : Nat} (hj : j < 13) : sI g D j ∈ K :=
  wv_mem hK (hP.1 j hj)

theorem hV_mem (hK : ∀ k < 7, g k ∈ K) (hP : PwItems D) {v : Nat} (hv : Lm 3 (wd v)) :
    hV g D v ∈ K :=
  wv_mem (fun _ hk => sI_mem hK hP (by omega)) hv

theorem cj_mem (hK : ∀ k < 7, g k ∈ K) (hP : PwItems D) {j : Nat} (hj : j < 13) : cj g D j ∈ K :=
  mul_mem (mul_mem (inv_mem (sI_mem hK hP (by omega))) (sI_mem hK hP hj)) (sI_mem hK hP (by omega))

theorem fWP_mem {a k : Nat → Equiv.Perm (Fin 245520)} (ha : ∀ j < 3, a j ∈ K)
    (hk : ∀ j < 4, k j ∈ K) : fWP a k ∈ K := by
  have a0 := ha 0 (by omega)
  have a2 := ha 2 (by omega)
  have k1 := hk 1 (by omega)
  have k2 := hk 2 (by omega)
  have k3 := hk 3 (by omega)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem a0 k3) k2)
    k1) a2) a2) k1) a2) a0) k2

theorem wAt_pt (hR : Rp TT UU g 7) (hP : PwItems D) {p : Fin 245520} (h : wAt TT UU D p = true) :
    (sI g D 12 * sI g D 0 * (sI g D 12)⁻¹) p = (sI g D 6 ^ 14) p ∧
      yp g D p = hV g D (D 61) p ∧
      (∀ j < 4, (sI g D 7 * sI g D (8 + j)) p = (sI g D (8 + j) * sI g D 7) p) ∧
      (sI g D 7 ^ 7) p = p ∧ (fWP (sI g D) (kp g D) ^ 8) p = p := by
  have hS := rp_s hR hP
  unfold wAt at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  refine ⟨Fin.ext ?_, Fin.ext ?_, fun j hj => Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · have e := Nat.eq_of_beq_eq_true h1
    simp only [sN] at e
    change sT TT UU D 12 (sT TT UU D 0 (sU TT UU D 12 p)) = pw (sT TT UU D 6) 14 p at e
    rw [(hS 12 (by omega) p).2, (hS 0 (by omega) _).1, (hS 12 (by omega) _).1,
      pw_eq (fun x => (hS 6 (by omega) x).1) 14 p] at e
    simpa only [Equiv.Perm.mul_apply] using e
  · exact (cjA_eq hR hP (by omega) p).symm.trans
      ((Nat.eq_of_beq_eq_true h2).trans (hW_eq hR hP (pw_lm3 hP 61) p))
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec h3 j hj)
    simp only [sN] at e
    change sT TT UU D 7 (sT TT UU D (8 + j) p) = sT TT UU D (8 + j) (sT TT UU D 7 p) at e
    rw [(hS (8 + j) (by omega) p).1, (hS 7 (by omega) _).1, (hS 7 (by omega) p).1,
      (hS (8 + j) (by omega) _).1] at e
    simpa only [Equiv.Perm.mul_apply] using e
  · exact (pw_eq (fun x => (hS 7 (by omega) x).1) 7 p).symm.trans (Nat.eq_of_beq_eq_true h4)
  · exact (pw_eq (fun x => fW_eq (fun j hj x => (hS j (by omega) x).1)
      (fun j hj x => kA_eq hR hP hj x) x) 8 p).symm.trans (Nat.eq_of_beq_eq_true h5)

theorem pw_words (hR : Rp TT UU g 7) (hP : PwItems D) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) (h0 : wAt TT UU D p0 = true)
    (h1 : wAt TT UU D p1 = true) (h2 : wAt TT UU D p2 = true) :
    sI g D 12 * sI g D 0 * (sI g D 12)⁻¹ = sI g D 6 ^ 14 ∧ yp g D = hV g D (D 61) ∧
      (∀ j < 4, Commute (sI g D 7) (sI g D (8 + j))) ∧ sI g D 7 ^ 7 = 1 ∧
      fWP (sI g D) (kp g D) ^ 8 = 1 := by
  have P : ∀ p ∈ [p0, p1, p2], wAt TT UU D p = true := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have m : ∀ {j}, j < 13 → sI g D j ∈ K := fun hj => sI_mem hK hP hj
  have mk : ∀ j < 4, kp g D j ∈ K := fun j _ => cj_mem hK hP (by omega)
  refine ⟨sep_eq hS (mul_mem (mul_mem (m (by omega)) (m (by omega))) (inv_mem (m (by omega))))
      (pow_mem (m (by omega)) _) fun p hp => (wAt_pt hR hP (P p hp)).1,
    sep_eq hS (cj_mem hK hP (by omega)) (hV_mem hK hP (pw_lm3 hP 61))
      fun p hp => (wAt_pt hR hP (P p hp)).2.1,
    fun j hj => sep_eq hS (mul_mem (m (by omega)) (m (by omega))) (mul_mem (m (by omega))
      (m (by omega))) fun p hp => (wAt_pt hR hP (P p hp)).2.2.1 j hj,
    sep_eq hS (pow_mem (m (by omega)) _) (one_mem K) fun p hp => (wAt_pt hR hP (P p hp)).2.2.2.1,
    sep_eq hS (pow_mem (fWP_mem (fun j _ => m (by omega)) mk) _) (one_mem K)
      fun p hp => (wAt_pt hR hP (P p hp)).2.2.2.2⟩

theorem pw_hd (hR : Rp TT UU g 7) (hP : PwItems D) (h : wHd TT UU D = true) :
    (∃ j < 4, sI g D 0 * kp g D j ≠ kp g D j * sI g D 0) ∧ D 69 = 20160 := by
  have hS := rp_s hR hP
  unfold wHd at h
  simp only [sB, sN] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  have hp : Nat.shiftRight (D 71) 2 < 245520 := Nat.blt_eq.mp h1
  have hj : Nat.land (D 71) 3 < 4 :=
    Nat.lt_of_le_of_lt (Nat.and_le_right : D 71 &&& 3 ≤ 3) (by decide)
  refine ⟨⟨_, hj, fun hc => nbeq h2 ?_⟩, Nat.eq_of_beq_eq_true h3⟩
  have a1 : sT TT UU D 0 (kA TT UU D (Nat.land (D 71) 3) (Nat.shiftRight (D 71) 2)) =
      ((sI g D 0 * kp g D (Nat.land (D 71) 3)) ⟨_, hp⟩ : Nat) := by
    rw [kA_eq hR hP hj ⟨_, hp⟩, (hS 0 (by omega) _).1]
    rfl
  have a2 : kA TT UU D (Nat.land (D 71) 3) (sT TT UU D 0 (Nat.shiftRight (D 71) 2)) =
      ((kp g D (Nat.land (D 71) 3) * sI g D 0) ⟨_, hp⟩ : Nat) := by
    rw [(hS 0 (by omega) ⟨_, hp⟩).1, kA_eq hR hP hj]
    rfl
  exact a1.trans ((congrArg (fun σ : Equiv.Perm (Fin 245520) => (σ ⟨_, hp⟩ : Nat)) hc).trans a2.symm)

end Words

structure Blocks (D : Nat → Nat) (Mg : Subgroup (Equiv.Perm (Fin 245520)))
    (ρ : Equiv.Perm (Fin 245520) → Equiv.Perm (Fin 120)) : Prop where
  mul : ∀ a ∈ Mg, ∀ b ∈ Mg, ρ (a * b) = ρ a * ρ b
  lt : ∀ k < 120, blk D k 0 < 245520
  img : ∀ m ∈ Mg, ∀ k : Fin 120, (m ⟨blk D k 0, lt k k.isLt⟩ : Nat) = blk D (ρ m k) 0 ∨
    (m ⟨blk D k 0, lt k k.isLt⟩ : Nat) = blk D (ρ m k) 1
  disj : ∀ k < 120, ∀ k' < 120, ∀ i < 2, ∀ i' < 2, blk D k i = blk D k' i' → k = k'

section Blk

variable {Mg : Subgroup (Equiv.Perm (Fin 245520))} {ρ : Equiv.Perm (Fin 245520) → Equiv.Perm (Fin 120)}

theorem Blocks.one {D : Nat → Nat} (hBk : Blocks D Mg ρ) : ρ 1 = 1 := by
  have h := hBk.mul 1 (one_mem _) 1 (one_mem _)
  rw [one_mul] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem Blocks.inv {D : Nat → Nat} (hBk : Blocks D Mg ρ) {a : Equiv.Perm (Fin 245520)} (ha : a ∈ Mg) :
    ρ a⁻¹ = (ρ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hBk.mul _ (inv_mem ha) _ ha, inv_mul_cancel, hBk.one]

theorem Blocks.wv {D : Nat → Nat} (hBk : Blocks D Mg ρ) {a : Nat → Equiv.Perm (Fin 245520)}
    {m : Nat} (ha : ∀ k < m, a k ∈ Mg) : ∀ {w : List Int}, Lm m w →
    ρ (ONPv.wv a w) = ONPv.wv (fun k => ρ (a k)) w
  | [], _ => by rw [wv_nil, wv_nil, hBk.one]
  | z :: w, hw => by
    obtain ⟨hz, hw'⟩ := Lm_cons hw
    have hl : ρ (lv a z) = lv (fun k => ρ (a k)) z := by
      unfold lv
      by_cases hp : 0 < z
      · simp only [hp, ↓reduceIte]
      · simp only [hp, ↓reduceIte]
        exact hBk.inv (ha _ (by omega))
    rw [wv_cons, wv_cons, hBk.mul _ (lv_mem ha hz) _ (wv_mem ha hw'), hl, hBk.wv ha hw']

private theorem rInv_aux {P : Nat} {σ : Equiv.Perm (Fin 120)} (hP : ∀ j : Fin 120, rt P j = (σ j : Nat))
    (k : Fin 120) : ∀ n, n ≤ 120 →
    Nat.rec (motive := fun _ => Nat) (nat_lit 120) (fun j ih => nIf(Nat.beq (rt P j) k, j, ih)) n =
      if (σ⁻¹ k : Nat) < n then (σ⁻¹ k : Nat) else 120
  | 0, _ => by simp
  | n + 1, hn => by
    have ih := rInv_aux hP k n (by omega)
    change Bool.rec (motive := fun _ => Nat) (Nat.rec (motive := fun _ => Nat) (nat_lit 120)
      (fun j ih => nIf(Nat.beq (rt P j) k, j, ih)) n) n (Nat.beq (rt P n) k) = _
    rw [ih]
    have e : rt P n = (σ ⟨n, by omega⟩ : Nat) := hP ⟨n, by omega⟩
    cases hb : Nat.beq (rt P n) k with
    | true =>
      have hc : σ⁻¹ k = ⟨n, by omega⟩ := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact Fin.ext (e ▸ Nat.eq_of_beq_eq_true hb).symm
      rw [hc]
      simp
    | false =>
      have hc : (σ⁻¹ k : Nat) ≠ n := by
        intro h
        have h' : σ⁻¹ k = ⟨n, by omega⟩ := Fin.ext h
        rw [Equiv.Perm.inv_eq_iff_eq] at h'
        exact Nat.ne_of_beq_eq_false hb (e.trans (congrArg Fin.val h').symm)
      dsimp only
      split_ifs <;> omega

theorem rInv_eq {P : Nat} {σ : Equiv.Perm (Fin 120)} (hP : ∀ j : Fin 120, rt P j = (σ j : Nat))
    (k : Fin 120) : rInv P k = (σ⁻¹ k : Nat) :=
  (rInv_aux hP k 120 le_rfl).trans (if_pos (σ⁻¹ k).isLt)

variable {TT UU : Nat → Nat → Nat} {D : Nat → Nat} {g : Nat → Equiv.Perm (Fin 245520)}

theorem rhoAll_parts (h : rhoAll TT UU D = true) :
    (∀ j < 5, ∀ k < 120, rhoOK TT UU D j k = true) ∧ (∀ k < 120, ryOK D k = true) ∧
      ∀ j < 3, dB D j < 120 := by
  unfold rhoAll at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun j hj k hk => ?_, fun k hk => ?_, fun j hj => ?_⟩
  · have e := allBlk_spec (allBlk_spec h1 j hj) k hk
    rwa [show Nat.add 0 j = j from Nat.zero_add j, show Nat.add 0 k = k from Nat.zero_add k] at e
  · have e := allBlk_spec h2 k hk
    rwa [show Nat.add 0 k = k from Nat.zero_add k] at e
  · have e := allBlk_spec h3 j hj
    rw [show Nat.add 0 j = j from Nat.zero_add j] at e
    exact Nat.blt_eq.mp e

theorem rG_eq (hR : Rp TT UU g 7) (hP : PwItems D) (hBk : Blocks D Mg ρ)
    (hM : ∀ j < 5, sI g D j ∈ Mg) (h : rhoAll TT UU D = true) {j : Nat} (hj : j < 5)
    (k : Fin 120) : rG D j k = (ρ (sI g D j) k : Nat) := by
  have hS := rp_s hR hP
  have e := (rhoAll_parts h).1 j hj k k.isLt
  unfold rhoOK at e
  simp only [sB] at e
  obtain ⟨ht, hm⟩ := (bAnd_iff _ _).1 e
  have ht' : rG D j k < 120 := Nat.blt_eq.mp ht
  have hx : sT TT UU D j (blk D k 0) = (sI g D j ⟨blk D k 0, hBk.lt k k.isLt⟩ : Nat) :=
    (hS j (by omega) ⟨_, hBk.lt k k.isLt⟩).1
  have hρ := hBk.img _ (hM j hj) k
  rcases bIf_or hm with h0 | h0 <;> have e0 := Nat.eq_of_beq_eq_true h0 <;> rw [hx] at e0 <;>
    rcases hρ with h1 | h1
  · exact hBk.disj _ ht' _ (ρ (sI g D j) k).isLt 0 (by omega) 0 (by omega) (e0.symm.trans h1)
  · exact hBk.disj _ ht' _ (ρ (sI g D j) k).isLt 0 (by omega) 1 (by omega) (e0.symm.trans h1)
  · exact hBk.disj _ ht' _ (ρ (sI g D j) k).isLt 1 (by omega) 0 (by omega) (e0.symm.trans h1)
  · exact hBk.disj _ ht' _ (ρ (sI g D j) k).isLt 1 (by omega) 1 (by omega) (e0.symm.trans h1)

theorem rp_blk (hR : Rp TT UU g 7) (hP : PwItems D) (hBk : Blocks D Mg ρ)
    (hM : ∀ j < 5, sI g D j ∈ Mg) (h : rhoAll TT UU D = true) :
    Rp (rG D) (rGU D) (fun j => ρ (sI g D j)) 5 :=
  fun j hj k => ⟨rG_eq hR hP hBk hM h hj k, rInv_eq (fun i => rG_eq hR hP hBk hM h hj i) k⟩

theorem rp_blkL (hR : Rp TT UU g 7) (hP : PwItems D) (hBk : Blocks D Mg ρ)
    (hM : ∀ j < 5, sI g D j ∈ Mg) (h : rhoAll TT UU D = true) :
    Rp (rL D) (rLU D) (fun j => ρ (sI g D (3 + j))) 2 :=
  fun j hj k => rp_blk hR hP hBk hM h (3 + j) (by omega) k

theorem hV_memM (hM : ∀ j < 5, sI g D j ∈ Mg) {v : Nat} (hv : Lm 3 (wd v)) : hV g D v ∈ Mg :=
  wv_mem (fun j _ => hM j (by omega)) hv

theorem hB_eq (hR : Rp TT UU g 7) (hP : PwItems D) (hBk : Blocks D Mg ρ)
    (hM : ∀ j < 5, sI g D j ∈ Mg) (h : rhoAll TT UU D = true) {v : Nat} (hv : Lm 3 (wd v))
    (k : Fin 120) : hB D v k = (ρ (hV g D v) k : Nat) := by
  refine (iT_eq (rp_blk hR hP hBk hM h) (Lm_mono (by omega) hv) k).trans ?_
  rw [hV, hBk.wv (m := 3) (fun j _ => hM j (by omega)) hv]

theorem hBU_eq (hR : Rp TT UU g 7) (hP : PwItems D) (hBk : Blocks D Mg ρ)
    (hM : ∀ j < 5, sI g D j ∈ Mg) (h : rhoAll TT UU D = true) {v : Nat} (hv : Lm 3 (wd v))
    (k : Fin 120) : hBU D v k = ((ρ (hV g D v))⁻¹ k : Nat) := by
  refine (iU_eq (rp_blk hR hP hBk hM h) (Lm_mono (by omega) hv) k).trans ?_
  rw [hV, hBk.wv (m := 3) (fun j _ => hM j (by omega)) hv]

theorem aB_eq (hR : Rp TT UU g 7) (hP : PwItems D) (hBk : Blocks D Mg ρ)
    (hM : ∀ j < 5, sI g D j ∈ Mg) (h : rhoAll TT UU D = true) {e : Nat} (he : e < 16)
    (k : Fin 120) : aB D e k = (ρ (bY g D e) k : Nat) := by
  have hT : Rp (fun j => hB D (D (Nat.add (Nat.add 13 (Nat.mul 3 e)) j)))
      (fun j => hBU D (D (Nat.add (Nat.add 13 (Nat.mul 3 e)) j))) (fun j => ρ (bE g D e j)) 3 :=
    fun j hj x => ⟨hB_eq hR hP hBk hM h (pw_lm3 hP (13 + 3 * e + j)) x,
      hBU_eq hR hP hBk hM h (pw_lm3 hP (13 + 3 * e + j)) x⟩
  refine (iT_eq hT (pw_lm3 hP 61) k).trans ?_
  rw [bY, hBk.wv (a := bE g D e) (m := 3) (fun j _ => hV_memM hM (pw_lm3 hP (13 + 3 * e + j))) (pw_lm3 hP 61)]

theorem ry_eq (hR : Rp TT UU g 7) (hP : PwItems D) (hBk : Blocks D Mg ρ)
    (hM : ∀ j < 5, sI g D j ∈ Mg) (h : rhoAll TT UU D = true) (k : Fin 120) :
    rt (D 72) k = (ρ (hV g D (D 61)) k : Nat) :=
  (Nat.eq_of_beq_eq_true ((rhoAll_parts h).2.1 k k.isLt)).trans
    (hB_eq hR hP hBk hM h (pw_lm3 hP 61) k)

theorem dB_lt (h : rhoAll TT UU D = true) {j : Nat} (hj : j < 3) : dB D j < 120 :=
  (rhoAll_parts h).2.2 j hj

end Blk

end CFSG.KS.ONPw

end
