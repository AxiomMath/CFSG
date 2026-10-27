module

public import CFSG.Certificates.Kernel.TcRes.RootSound

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK CFSG.KC.TcRes.Lane Matrix

@[expose] noncomputable def ndL (ND j : ℕ) : List ℕ :=
  (List.range (Nat.land (Nat.shiftRight (fld ND 288 j) 64) 15)).map fun a =>
    fld (Nat.land (fld ND 288 j) 18446744073709551615) 8 a

@[expose] def SkewOk (vec : ℕ → Fin Tag.E8.rank → ℤ) (t : List ℕ) (x : ℕ) : Prop :=
  x < 240 ∧ iform (vec x) (vec t.length) = 0 ∧
    ∀ a (ha : a < t.length), iform (vec x) (vec t[a]) = iform (vec t.length) (vec a) ∧
      iform (vec x) (vec a) = - iform (vec t.length) (vec t[a])

structure SearchRaw (vec : ℕ → Fin Tag.E8.rank → ℤ) (ND T0 tot : ℕ) : Prop where
  root : 0 < tot ∧ ndL ND 0 = [fld T0 8 0]
  child : ∀ j < tot, (∀ a ∈ ndL ND j, a < 240) → (ndL ND j).length < 8 → ∀ x,
    SkewOk vec (ndL ND j) x → ∃ c < tot, ndL ND c = ndL ND j ++ [x]
  leaf : ∀ j < tot, (∀ a ∈ ndL ND j, a < 240) → (ndL ND j).length = 8 →
    ∀ ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ), (∀ x y, iform (ψ x) (ψ y) = iform x y) →
    (∀ m : Fin Tag.E8.rank, ψ (vec m) = vec ((ndL ND j).getD m 0)) →
    ∃ h : WeylGroup Tag.E8, ∀ m : Fin Tag.E8.rank, h • ψ (h⁻¹ • vec m) = vec (fld T0 8 m)

theorem SearchRaw.mem_search {vec : ℕ → Fin Tag.E8.rank → ℤ} {ND T0 tot : ℕ}
    (h : SearchRaw vec ND T0 tot) (hT0 : fld T0 8 0 < 240) (t : List ℕ)
    (ht0 : t.head? = some (fld T0 8 0))
    (ht8 : t.length = 8) (hok : ∀ k (hk : k < t.length), 1 ≤ k → SkewOk vec (t.take k) t[k]) :
    ∃ j < tot, ndL ND j = t ∧ (ndL ND j).length = 8 := by
  have hent : ∀ k, k ≤ t.length → ∀ a ∈ t.take k, a < 240 := by
    intro k hk a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    rw [List.getElem_take]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · cases t with
      | nil => simp at ht0
      | cons b t' =>
        simp only [List.head?_cons, Option.some.injEq] at ht0
        simpa [ht0] using hT0
    · exact (hok i _ hi0).1
  obtain ⟨j, hj, hjt⟩ := mem_of_chain (L := 8)
    (ok := fun s x => SkewOk vec s x ∧ ∀ a ∈ s, a < 240) h.root
    (fun j hj hl x hx => h.child j hj hx.2 hl x hx.1) t ht0 ht8.le
    (fun k hk hk1 => ⟨hok k hk hk1, hent k hk.le⟩)
  exact ⟨j, hj, hjt, by rw [hjt, ht8]⟩

def BtRec (RTs : ℕ → ℕ) (ADJ BT b0 k : ℕ) : Prop :=
  (fld BT 32 k &&& 255) < 240 ∧ ((fld BT 32 k >>> 13) &&& 127) < 126 ∧
    bit (fld ADJ 240 0) (fld BT 32 k &&& 255) = false ∧
    (((fld BT 32 k >>> 8) &&& 31) = 0 → (fld BT 32 k &&& 255) = b0) ∧
    (((fld BT 32 k >>> 8) &&& 31) ≠ 0 →
      ((fld BT 32 ((fld BT 32 k >>> 13) &&& 127) >>> 8) &&& 31) + 1 = ((fld BT 32 k >>> 8) &&& 31) ∧
      fld BT 32 k >>> 20 < 240 ∧ bit (fld ADJ 240 0) (fld BT 32 k >>> 20) = false ∧
      fld (RTs (fld BT 32 k >>> 20)) 8 (fld BT 32 ((fld BT 32 k >>> 13) &&& 127) &&& 255) =
        (fld BT 32 k &&& 255))

theorem btWalk_succ (RTs : ℕ → ℕ) (ADJ BT b0 c i prev acc : ℕ) :
    btWalk RTs ADJ BT b0 (c + 1) i prev acc =
      andB (Nat.blt prev (fld BT 32 i &&& 255)) (andB (Nat.blt (fld BT 32 i &&& 255) 240)
      (andB (Nat.blt ((fld BT 32 i >>> 13) &&& 127) 126)
      (andB (notB (bit (fld ADJ 240 0) (fld BT 32 i &&& 255)))
      (andB (Bool.rec (motive := fun _ => Bool)
          (andB (Nat.beq (Nat.succ ((fld BT 32 ((fld BT 32 i >>> 13) &&& 127) >>> 8) &&& 31))
              ((fld BT 32 i >>> 8) &&& 31))
            (andB (Nat.blt (fld BT 32 i >>> 20) 240)
              (andB (notB (bit (fld ADJ 240 0) (fld BT 32 i >>> 20)))
                (Nat.beq (fld (RTs (fld BT 32 i >>> 20)) 8
                  (fld BT 32 ((fld BT 32 i >>> 13) &&& 127) &&& 255)) (fld BT 32 i &&& 255)))))
          (Nat.beq (fld BT 32 i &&& 255) b0) (Nat.beq ((fld BT 32 i >>> 8) &&& 31) 0))
        (btWalk RTs ADJ BT b0 c (i + 1) (fld BT 32 i &&& 255)
          (acc ||| (1 <<< (fld BT 32 i &&& 255)))))))) := by
  simp only [btWalk, strictB_eq]
  rfl

theorem M240_testBit (g : ℕ) : M240.testBit g = decide (g < 240) := by
  change (1 <<< 240 - 1).testBit g = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]

theorem btWalk_spec (RTs : ℕ → ℕ) (ADJ BT b0 : ℕ) : ∀ c i prev acc,
    btWalk RTs ADJ BT b0 c i prev acc = true →
    (∀ t < c, BtRec RTs ADJ BT b0 (i + t)) ∧
    ∀ g, (M240 ^^^ fld ADJ 240 0).testBit g = true →
      acc.testBit g = true ∨ ∃ t < c, fld BT 32 (i + t) &&& 255 = g := by
  intro c
  induction c with
  | zero =>
    intro i prev acc h
    have h' : acc = M240 ^^^ fld ADJ 240 0 := beq_eq_true.1 h
    exact ⟨fun t ht => absurd ht (Nat.not_lt_zero _), fun g hg => Or.inl (h' ▸ hg)⟩
  | succ c ih =>
    intro i prev acc h
    rw [btWalk_succ] at h
    simp only [andB_eq_true, blt_eq_true, notB_eq_true, boolRec_true, beq_eq_true,
      beq_eq_false] at h
    obtain ⟨-, hg, hpi, hb, ⟨h0, h1⟩, hw⟩ := h
    obtain ⟨ih1, ih2⟩ := ih _ _ _ hw
    have hs : ∀ t, i + 1 + t = i + (t + 1) := fun t => by omega
    refine ⟨fun t ht => ?_, fun g' hg' => ?_⟩
    · rcases t with _ | t
      · simp only [add_zero]
        refine ⟨hg, hpi, hb, h0, fun hd => ?_⟩
        obtain ⟨a1, a2, a3, a4⟩ := h1 hd
        exact ⟨a1, a2, a3, a4⟩
      · rw [← hs]
        exact ih1 t (by omega)
    · rcases ih2 g' hg' with h2 | ⟨t, ht, h2⟩
      · rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow,
          Bool.or_eq_true, decide_eq_true_eq] at h2
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨0, by omega, by simpa using h2⟩
      · exact Or.inr ⟨t + 1, by omega, by rw [← hs]; exact h2⟩

theorem refl_mem_weyl
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    (hD : DatumRaw Tag.E8 240 vec rt adj neg) {l : ℕ} (hl : l < 240)
    (h0 : iform (vec l) (vec 0) = 0) :
    ∃ u : WeylGroup Tag.E8, u • vec 0 = vec 0 ∧ ∀ v, u • v = v - iform v (vec l) • vec l := by
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 (hD.isRoot l hl)
  have hsym : ∀ i j : Fin Tag.E8.rank, Tag.E8.symmetrizedCartan i j = Tag.E8.cartan i j := by
    intro i j
    change ((1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) * Tag.E8.cartan) i j = _
    rw [one_mul]
  have hu : ∀ v, (w * simple Tag.E8 j * w⁻¹) • v = v - iform v (vec l) • vec l := by
    intro v
    rw [smul_conj_simple, ← iform_single Tag.E8 hsym, hw, ← hw, ← iform_smul w, smul_inv_smul]
  refine ⟨_, ?_, hu⟩
  rw [hu, iform_comm, h0, zero_smul, sub_zero]

theorem btRaw_of_checks
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {neg : ℕ → ℕ} {ADJ BT T0 : ℕ} {RTs : ℕ → ℕ}
    (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v)
      (fun g v => Nat.beq (fld (fld ADJ 240 g) 1 v) 1) neg)
    (hbt : btOK RTs ADJ BT T0 = true) :
    ∀ g < 240, iform (vec g) (vec 0) = 0 →
      ∃ h : WeylGroup Tag.E8, h • vec 0 = vec 0 ∧ h • vec (fld T0 8 0) = vec g := by
  have hbit : ∀ g, bit (fld ADJ 240 0) g = false ↔
      Nat.beq (fld (fld ADJ 240 0) 1 g) 1 = false := by
    intro g
    rw [Bool.eq_false_iff, Bool.eq_false_iff, Ne, Ne, bit_iff, beq_eq_true, fld_one_eq_one]
  have hperp : ∀ g < 240, bit (fld ADJ 240 0) g = false → iform (vec g) (vec 0) = 0 := by
    intro g hg h
    rw [hbit] at h
    have := (hD.adj 0 (by norm_num) g hg).not
    rw [Bool.not_eq_true] at this
    exact not_not.1 (this.1 h)
  obtain ⟨hrec, hcov⟩ := btWalk_spec RTs ADJ BT (fld T0 8 0) 126 0 0 0 hbt
  simp only [zero_add] at hrec hcov
  have hdep : ∀ d, ∀ i < 126, (fld BT 32 i >>> 8) &&& 31 = d →
      ∃ h : WeylGroup Tag.E8, h • vec 0 = vec 0 ∧ h • vec (fld T0 8 0) = vec (fld BT 32 i &&& 255) := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      obtain ⟨-, -, -, h0, -⟩ := hrec i hi
      exact ⟨1, one_smul _ _, by rw [one_smul, h0 hd]⟩
    | succ d ih =>
      intro i hi hd
      obtain ⟨-, hpi, -, -, h1⟩ := hrec i hi
      obtain ⟨hpd, hl, hlb, hrt⟩ := h1 (by omega)
      obtain ⟨hg', -, -, -, -⟩ := hrec _ hpi
      obtain ⟨h, hh0, hh⟩ := ih _ hpi (by omega)
      obtain ⟨u, hu0, hu⟩ := refl_mem_weyl hD hl (hperp _ hl hlb)
      refine ⟨u * h, by rw [mul_smul, hh0, hu0], ?_⟩
      rw [mul_smul, hh, hu, ← hrt]
      exact ((hD.refl _ hl _ hg').2).symm
  intro g hg h0
  have hb0 : (fld ADJ 240 0).testBit g = false := by
    rw [Bool.eq_false_iff]
    intro hc
    have h1 : Nat.beq (fld (fld ADJ 240 0) 1 g) 1 = true := by
      rw [beq_eq_true, fld_one_eq_one]
      exact hc
    exact (hD.adj 0 (by norm_num) g hg).1 h1 h0
  have hb : (M240 ^^^ fld ADJ 240 0).testBit g = true := by
    rw [Nat.testBit_xor, M240_testBit, decide_eq_true hg, hb0]
    rfl
  rcases hcov g hb with h1 | ⟨i, hi, rfl⟩
  · simp at h1
  · exact hdep _ i hi rfl

@[expose] noncomputable def amat (vec : ℕ → Fin Tag.E8.rank → ℤ) (T0 r : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  fun m j => ((vec (fld T0 8 j) m : ℤ) : ZMod 5) - if m = j then (r : ZMod 5) else 0

@[expose] noncomputable def bvec (B : ℕ) (i : Fin 4) : Fin 8 → ZMod 5 :=
  fun m => (dg5 (fld B 20 i) m : ZMod 5)

structure KerRaw (vec : ℕ → Fin Tag.E8.rank → ℤ) (T0 B PV MW r : ℕ) : Prop where
  ker : ∀ i, bvec B i ᵥ* amat vec T0 r = 0
  piv : ∀ i k : Fin 4, bvec B i ⟨fld PV 3 k % 8, Nat.mod_lt _ (by norm_num)⟩ =
    if i = k then 1 else 0
  minor : (amat vec T0 r).submatrix (fun a : Fin 4 => ⟨fld MW 3 a % 8, Nat.mod_lt _ (by norm_num)⟩)
      (fun b : Fin 4 => ⟨fld MW 3 (4 + b) % 8, Nat.mod_lt _ (by norm_num)⟩) *
    Matrix.of (fun c b : Fin 4 => (fld MW 3 (8 + (4 * c + b)) : ZMod 5)) = 1

theorem kerRaw_of_checks {vec : ℕ → Fin Tag.E8.rank → ℤ} {V T0 B PV MW r : ℕ}
    {RC : ℕ → ℕ} (hvec : vec = vecOf 8 V) (hr : r ≤ 5) (hT0 : ∀ j < 8, fld T0 8 j < 240)
    (hrc : ∀ g < 240, rc5OK RC V g = true) (hk : kOK RC T0 B PV MW r = true) :
    KerRaw vec T0 B PV MW r := by
  subst hvec
  have hA : ∀ (m j : ℕ) (hm : m < 8) (hj : j < 8),
      ((amj RC T0 r m j : ℕ) : ZMod 5) = amat (vecOf 8 V) T0 r ⟨m, hm⟩ ⟨j, hj⟩ := by
    intro m j hm hj
    have h1 := hrc _ (hT0 j hj)
    simp only [rc5OK, strictB_eq, allLt_iff, beq_eq_true] at h1
    have h2 := h1 m hm
    simp only [amj, amat, vecOf, boolRec_nat, beq_eq_true, h2, nadd, nmod, nsub, Fin.mk.injEq]
    have h10 : (10 : ZMod 5) = 0 := by decide
    have h15 : (15 : ZMod 5) = 0 := by decide
    split_ifs with h3
    · rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod, Nat.cast_sub hr]
      push_cast
      linear_combination h15
    · rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod]
      push_cast
      linear_combination h10
  have h3 : ∀ x, fld MW 3 x % 8 = fld MW 3 x := fun x => Nat.mod_eq_of_lt (fld_lt MW 3 x)
  have hPV : ∀ x, fld PV 3 x % 8 = fld PV 3 x := fun x => Nat.mod_eq_of_lt (fld_lt PV 3 x)
  simp only [kOK, andB_eq_true, allLt_iff, strictB_eq, beq_eq_true, blt_eq_true, nadd, nmul,
    nmod] at hk
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨fun i => ?_, fun i k => ?_, ?_⟩
  · funext j
    have h := (hk1 i i.2).1 j j.2
    rw [sumLt_eq] at h
    have h' := congrArg (fun x : ℕ => (x : ZMod 5)) h
    simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul, Nat.cast_zero] at h'
    rw [← Fin.sum_univ_eq_sum_range] at h'
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, bvec]
    rw [← h']
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hA m j m.2 j.2]
  · have h := (hk1 i i.2).2 k k.2
    simp only [bvec, hPV]
    rw [h.2, boolRec_nat]
    simp only [beq_eq_true, Fin.val_inj]
    split_ifs <;> simp
  · ext a b
    have h := hk2 a a.2 b b.2
    rw [sumLt_eq] at h
    have h' := congrArg (fun x : ℕ => (x : ZMod 5)) h
    simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul, boolRec_nat, beq_eq_true,
      Fin.val_inj] at h'
    rw [← Fin.sum_univ_eq_sum_range] at h'
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.one_apply, h3]
    have h'' : ((if a = b then 1 else 0 : ℕ) : ZMod 5) = if a = b then 1 else 0 := by
      split_ifs <;> simp
    rw [h''] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hA _ _ (fld_lt MW 3 a) (fld_lt MW 3 (4 + c))]

theorem KerRaw.mem_span {vec : ℕ → Fin Tag.E8.rank → ℤ} {T0 B PV MW r : ℕ}
    (h : KerRaw vec T0 B PV MW r) {u : Fin 8 → ZMod 5} (hu : u ᵥ* amat vec T0 r = 0) :
    ∃ c : Fin 4 → ZMod 5, u = ∑ i, c i • bvec B i := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact mem_span_of_vecMul_eq_zero (n := 8) (m := 8) (k := 4) (d := 4) (amat vec T0 r)
    (fun a : Fin 4 => ⟨fld MW 3 a % 8, Nat.mod_lt _ (by norm_num)⟩)
    (fun b : Fin 4 => ⟨fld MW 3 (4 + b) % 8, Nat.mod_lt _ (by norm_num)⟩)
    (Matrix.of (fun c b : Fin 4 => (fld MW 3 (8 + (4 * c + b)) : ZMod 5))) h.minor (bvec B)
    (linearIndependent_of_pivots (bvec B)
      (fun k : Fin 4 => (⟨fld PV 3 k % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)) h.piv) h.ker
    (by norm_num) hu

section Search

theorem fld_shl_w {w P : ℕ} (hP : P < 2 ^ w) (s v : ℕ) :
    fld (P <<< (w * s)) w v = if v = s then P else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_fld, Nat.testBit_shiftLeft]
  have hbig : ∀ i, w ≤ i → P.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) hi))
  split_ifs with h
  · subst h
    by_cases hj : j < w
    · simp [hj]
    · simp [hj, hbig j (by omega)]
  · rw [Nat.zero_testBit]
    by_cases hj : j < w
    · rcases Nat.lt_or_gt_of_ne h with h' | h'
      · have : w * (v + 1) ≤ w * s := Nat.mul_le_mul_left _ h'
        have h2 : ¬ (w * v + j ≥ w * s) := by rw [mul_add, mul_one] at this; omega
        simp [hj, h2]
      · have : w * (s + 1) ≤ w * v := Nat.mul_le_mul_left _ h'
        rw [mul_add, mul_one] at this
        simp [hj, hbig (w * v + j - w * s) (by omega)]
    · simp [hj]

theorem fld_land_mask {y n w a : ℕ} (h : w * a + w ≤ n) :
    fld (y &&& (2 ^ n - 1)) w a = fld y w a := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_fld, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < w
  · simp [hj, show w * a + j < n by omega]
  · simp [hj]

theorem sum8_eq (f : ℕ → ℕ) : sum8 f = ∑ m ∈ Finset.range 8, f m := by
  have h : ∀ n, (Nat.rec (motive := fun _ => ℕ) 0
      (fun m ih => strictN ih fun a => Nat.add a (f m)) n : ℕ) = ∑ m ∈ Finset.range n, f m := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact strictN_eq _ _
  exact h 8

def lsum (f : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range 240, f i * 2 ^ (16 * i)

theorem lsum_lt {f : ℕ → ℕ} (hf : ∀ i < 240, f i < 2 ^ 16) : lsum f < 2 ^ (16 * 240) :=
  sum_lanes_lt 16 240 f hf

theorem fld_lsum {f : ℕ → ℕ} (hf : ∀ i < 240, f i < 2 ^ 16) (i : ℕ) :
    fld (lsum f) 16 i = if i < 240 then f i else 0 :=
  fld_sum_lanes 16 240 f hf i

theorem lsum_add (f g : ℕ → ℕ) : lsum f + lsum g = lsum (fun i => f i + g i) := by
  simp only [lsum, ← Finset.sum_add_distrib, add_mul]

theorem lsum_sub {f g : ℕ → ℕ} (h : ∀ i < 240, g i ≤ f i) :
    lsum f - lsum g = lsum (fun i => f i - g i) := by
  simp only [lsum, tsub_mul]
  exact (Finset.sum_tsub_distrib _ fun i hi =>
    Nat.mul_le_mul_right _ (h i (Finset.mem_range.1 hi))).symm

theorem mul_lsum (c : ℕ) (f : ℕ → ℕ) : c * lsum f = lsum (fun i => c * f i) := by
  simp only [lsum, Finset.mul_sum, mul_assoc]

theorem lsum_congr {f g : ℕ → ℕ} (h : ∀ i < 240, f i = g i) : lsum f = lsum g :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem low16_eq : LOW16 = lsum (fun _ => 1) := lowW_eq 16 240 (by norm_num)

theorem testBit_lsum {f : ℕ → ℕ} (hf : ∀ i < 240, f i ≤ 1) (i : ℕ) :
    (lsum f).testBit (16 * i) = true ↔ i < 240 ∧ f i = 1 := by
  have h := testBit_fld (lsum f) 16 i 0
  simp only [Nat.ofNat_pos, decide_true, Bool.true_and, add_zero] at h
  rw [← h, fld_lsum (fun i hi => by have := hf i hi; omega)]
  split_ifs with hi
  · have := hf i hi
    rcases (by omega : f i = 0 ∨ f i = 1) with h0 | h0 <;> simp [h0, hi]
  · simp [hi]

theorem testBit_shl_add {L n p : ℕ} (h : L.testBit p = true) : (L <<< n).testBit (p + n) = true := by
  rw [Nat.testBit_shiftLeft]
  simp [h]

theorem geL_eq {z : ℕ → ℕ} (hz : ∀ i < 240, z i ≤ 4) {v : ℕ} (hv1 : 1 ≤ v) (hv : v ≤ 4) :
    geL (lsum z) v = lsum (fun i => if v ≤ z i then 1 else 0) := by
  have e : geL (lsum z) v = ((lsum z + (8 - v) * LOW16) >>> 3) &&& lowW 16 240 := rfl
  have e2 : lsum z + (8 - v) * LOW16 = lsum (fun i => z i + (8 - v)) := by
    rw [low16_eq, mul_lsum, lsum_add]
    simp only [mul_one]
  have hb : ∀ i < 240, z i + (8 - v) < 2 ^ 16 := fun i hi => by have := hz i hi; omega
  rw [e, e2]
  have hlt : ((lsum fun i => z i + (8 - v)) >>> 3) &&& lowW 16 240 < 2 ^ (16 * 240) :=
    lt_of_le_of_lt Nat.and_le_right (low_lt (by norm_num) 240)
  refine (eq_sum_lanes 16 240 _ hlt).trans (lsum_congr fun i hi' => ?_)
  rw [fld_shr3_low (by norm_num) hi', fld_lsum hb, if_pos hi']
  have := hz i hi'
  generalize z i = a at this ⊢
  interval_cases a <;> interval_cases v <;> decide

noncomputable def zOf (QS : ℕ → ℕ) (Y x : ℕ) : ℕ :=
  ((∑ m ∈ Finset.range 8, fld (fld Y 256 x) 16 (7 - m) * QS m) +
      (2 + 7 * ∑ m ∈ Finset.range 8, fld (fld Y 256 x) 16 (15 - m)) * LOW16) -
    ((∑ m ∈ Finset.range 8, fld (fld Y 256 x) 16 (15 - m) * QS m) +
      7 * (∑ m ∈ Finset.range 8, fld (fld Y 256 x) 16 (7 - m)) * LOW16)

theorem mvRow_eq (QS : ℕ → ℕ) (Y x : ℕ) : mvRow QS Y x =
    (LOW16 - geL (zOf QS Y x) 1) ||| ((geL (zOf QS Y x) 1 - geL (zOf QS Y x) 2) <<< 3840 |||
      ((geL (zOf QS Y x) 2 - geL (zOf QS Y x) 3) <<< 7680 |||
      ((geL (zOf QS Y x) 3 - geL (zOf QS Y x) 4) <<< 11520 ||| geL (zOf QS Y x) 4 <<< 15360))) := by
  simp only [mvRow, strictN_eq, sum8_eq]
  rfl

theorem e8_sym : ∀ i j : Fin Tag.E8.rank, Tag.E8.symmetrizedCartan i j = Tag.E8.cartan i j := by
  intro i j
  change ((1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) * Tag.E8.cartan) i j = _
  rw [one_mul]

section Checks

variable
  {vec : ℕ → Fin Tag.E8.rank → ℤ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ} {RTs : ℕ → ℕ}
  (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v) adj neg)

include hD in
theorem iform_root_self {v : ℕ} (hv : v < 240) : iform (vec v) (vec v) = 2 := by
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 (hD.isRoot v hv)
  rw [← hw, iform_smul, iform_single Tag.E8 e8_sym]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  fin_cases j <;> decide

include hD in
theorem iform_root_bound {v g : ℕ} (hv : v < 240) (hg : g < 240) :
    -2 ≤ iform (vec v) (vec g) ∧ iform (vec v) (vec g) ≤ 2 := by
  have hn : ∀ x : Fin Tag.E8.rank → ℤ, 0 ≤ iform x x := fun x => by
    by_cases hx : x = 0
    · subst hx
      simp [iform]
    · exact (iform_self_pos hx).le
  have h1 := hn (vec v + vec g)
  have h2 := hn (vec v - vec g)
  simp only [iform_add_left, iform_add_right, iform_sub_left, iform_sub_right] at h1 h2
  rw [iform_comm (vec g) (vec v), iform_root_self hD hv, iform_root_self hD hg] at h1 h2
  constructor <;> linarith

include hD in
theorem zOf_eq {V Y : ℕ} {QS : ℕ → ℕ} (hvec : vec = vecOf 8 V)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (hq : ∀ i < 240, qOK QS V i = true) {x : ℕ} (hx : x < 240) :
    ∃ z : ℕ → ℕ, zOf QS Y x = lsum z ∧ ∀ i < 240, (z i : ℤ) = iform (vec i) (vec x) + 2 := by
  obtain ⟨cP, hcP⟩ : ∃ f : ℕ → ℕ, f = fun m => fld (fld Y 256 x) 16 (7 - m) := ⟨_, rfl⟩
  obtain ⟨cN, hcN⟩ : ∃ f : ℕ → ℕ, f = fun m => fld (fld Y 256 x) 16 (15 - m) := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : ℕ → ℕ → ℕ, q = fun m i => fld (fld V 128 i) 16 m := ⟨_, rfl⟩
  have hz : zOf QS Y x = ((∑ m ∈ Finset.range 8, cP m * QS m) +
      (2 + 7 * ∑ m ∈ Finset.range 8, cN m) * LOW16) -
      ((∑ m ∈ Finset.range 8, cN m * QS m) + 7 * (∑ m ∈ Finset.range 8, cP m) * LOW16) := by
    rw [hcP, hcN]
    rfl
  have hYc' : ∀ k : Fin Tag.E8.rank, (cP k : ℤ) - cN k = ∑ j, Tag.E8.symmetrizedCartan k j * vec x j := by
    intro k
    rw [hcP, hcN]
    exact hYc x hx k
  have hcPl : ∀ m, cP m ≤ 3 := fun m => by rw [hcP]; exact hYl x hx _
  have hcNl : ∀ m, cN m ≤ 3 := fun m => by rw [hcN]; exact hYl x hx _
  have hQ : ∀ m < 8, QS m = lsum (q m) := by
    intro m hm
    rw [eq_sum_lanes 16 240 (QS m) (hQb m hm)]
    unfold lsum
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := hq i (Finset.mem_range.1 hi)
    simp only [qOK, strictB_eq, allLt_iff, beq_eq_true] at h
    rw [hqd]
    congr 1
    exact h m hm
  have hql : ∀ m < 8, ∀ i < 240, q m i < 16 := fun m hm i hi => by rw [hqd]; exact hVl i hi m hm
  have hlin : ∀ c : ℕ → ℕ, ∑ m ∈ Finset.range 8, c m * QS m =
      lsum (fun i => ∑ m ∈ Finset.range 8, c m * q m i) := by
    intro c
    have h : ∀ m ∈ Finset.range 8, c m * QS m = lsum (fun i => c m * q m i) := fun m hm => by
      rw [hQ m (Finset.mem_range.1 hm), mul_lsum]
    rw [Finset.sum_congr rfl h]
    unfold lsum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  have hPe : (∑ m ∈ Finset.range 8, cP m * QS m) + (2 + 7 * ∑ m ∈ Finset.range 8, cN m) * LOW16 =
      lsum (fun i => (∑ m ∈ Finset.range 8, cP m * q m i) + (2 + 7 * ∑ m ∈ Finset.range 8, cN m)) := by
    rw [hlin cP, low16_eq, mul_lsum, lsum_add]
    simp only [mul_one]
  have hNe : (∑ m ∈ Finset.range 8, cN m * QS m) + 7 * (∑ m ∈ Finset.range 8, cP m) * LOW16 =
      lsum (fun i => (∑ m ∈ Finset.range 8, cN m * q m i) + 7 * ∑ m ∈ Finset.range 8, cP m) := by
    rw [hlin cN, low16_eq, mul_lsum, lsum_add]
    simp only [mul_one]
  have hr : ∀ f : ℕ → ℤ, ∑ m ∈ Finset.range 8, f m = ∑ k : Fin Tag.E8.rank, f k := fun f =>
    (Fin.sum_univ_eq_sum_range f 8).symm
  have hiden : ∀ i < 240, (((∑ m ∈ Finset.range 8, cP m * q m i) +
      (2 + 7 * ∑ m ∈ Finset.range 8, cN m) : ℕ) : ℤ) -
      (((∑ m ∈ Finset.range 8, cN m * q m i) + 7 * ∑ m ∈ Finset.range 8, cP m : ℕ) : ℤ) =
      iform (vec i) (vec x) + 2 := by
    intro i hi
    have hv : ∀ k : Fin Tag.E8.rank, (q k i : ℤ) = vec i k + 7 := fun k => by
      subst hvec
      rw [hqd]
      change (fld (fld V 128 i) 16 (k : ℕ) : ℤ) = (fld (fld V 128 i) 16 (k : ℕ) : ℤ) - 7 + 7
      ring
    have key : ∑ k : Fin Tag.E8.rank, vec i k * ((cP k : ℤ) - cN k) = iform (vec i) (vec x) := by
      simp only [iform]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hYc' k, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e1 : ∀ c : ℕ → ℕ, ∑ k : Fin Tag.E8.rank, (c k : ℤ) * (vec i k + 7) =
        ∑ k : Fin Tag.E8.rank, vec i k * c k + 7 * ∑ k : Fin Tag.E8.rank, (c k : ℤ) := fun c => by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k : Fin Tag.E8.rank, vec i k * ((cP k : ℤ) - cN k) =
        ∑ k : Fin Tag.E8.rank, vec i k * cP k - ∑ k : Fin Tag.E8.rank, vec i k * cN k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    push_cast
    simp only [hr, hv]
    rw [e1, e1, ← key, e2]
    ring
  have hle : ∀ i < 240, (∑ m ∈ Finset.range 8, cN m * q m i) + 7 * ∑ m ∈ Finset.range 8, cP m ≤
      (∑ m ∈ Finset.range 8, cP m * q m i) + (2 + 7 * ∑ m ∈ Finset.range 8, cN m) := by
    intro i hi
    have h1 := hiden i hi
    have h2 := (iform_root_bound hD hi hx).1
    omega
  refine ⟨fun i => ((∑ m ∈ Finset.range 8, cP m * q m i) + (2 + 7 * ∑ m ∈ Finset.range 8, cN m)) -
    ((∑ m ∈ Finset.range 8, cN m * q m i) + 7 * ∑ m ∈ Finset.range 8, cP m), ?_, fun i hi => ?_⟩
  · rw [hz, hPe, hNe, lsum_sub hle]
  · beta_reduce
    rw [Nat.cast_sub (hle i hi)]
    exact hiden i hi

include hD in
theorem mv_fld {V Y : ℕ} {QS MVS : ℕ → ℕ} (hvec : vec = vecOf 8 V)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    {x : ℕ} (hx : x < 240) (f : ℕ) :
    mvf MVS x f = lsum (fun i => if iform (vec i) (vec x) + 2 = f then 1 else 0) := by
  obtain ⟨z, hz, hzi⟩ := zOf_eq hD hvec hVl hYc hYl hQb hq hx
  have hz4 : ∀ i < 240, z i ≤ 4 := fun i hi => by
    have := hzi i hi
    have := iform_root_bound hD hi hx
    omega
  have hM : MVS x = mvRow QS Y x := beq_eq_true.1 (hmv x hx)
  have hlow : LOW16 - geL (zOf QS Y x) 1 = lsum (fun i => 1 - if 1 ≤ z i then 1 else 0) := by
    rw [hz, geL_eq hz4 le_rfl (by norm_num), low16_eq, lsum_sub (fun i _ => by split_ifs <;> omega)]
  have hsub : ∀ v, 1 ≤ v → v ≤ 3 → geL (zOf QS Y x) v - geL (zOf QS Y x) (v + 1) =
      lsum (fun i => (if v ≤ z i then 1 else 0) - if v + 1 ≤ z i then 1 else 0) := by
    intro v h1 h3
    rw [hz, geL_eq hz4 h1 (by omega), geL_eq hz4 (by omega) (by omega),
      lsum_sub (fun i _ => by split_ifs <;> omega)]
  have h4 : geL (zOf QS Y x) 4 = lsum (fun i => if 4 ≤ z i then 1 else 0) := by
    rw [hz, geL_eq hz4 (by norm_num) le_rfl]
  have hlt : ∀ g : ℕ → ℕ, (∀ i < 240, g i ≤ 1) → lsum g < 2 ^ (16 * 240) := fun g hg =>
    lsum_lt fun i hi => by have := hg i hi; omega
  have hs : ∀ g : ℕ → ℕ, (∀ i < 240, g i ≤ 1) → ∀ s,
      fld (lsum g <<< (3840 * s)) 3840 f = if f = s then lsum g else 0 :=
    fun g hg s => fld_shl_w (w := 3840)
      (lt_of_lt_of_eq (hlt g hg) (congrArg (2 ^ ·) (by norm_num : 16 * 240 = 3840))) s f
  have b0 : ∀ i < 240, (1 - if 1 ≤ z i then 1 else 0) ≤ 1 := fun i _ => by split_ifs <;> omega
  have bs : ∀ v, ∀ i < 240, ((if v ≤ z i then 1 else 0) - if v + 1 ≤ z i then 1 else 0) ≤ 1 :=
    fun v i _ => by split_ifs <;> omega
  have b4 : ∀ i < 240, (if 4 ≤ z i then 1 else 0) ≤ 1 := fun i _ => by split_ifs <;> omega
  have e0 := hs _ b0 0
  have e1 := hs _ (bs 1) 1
  have e2 := hs _ (bs 2) 2
  have e3 := hs _ (bs 3) 3
  have e4 := hs _ b4 4
  rw [mul_zero, Nat.shiftLeft_zero] at e0
  rw [(by norm_num : 3840 * 1 = 3840)] at e1
  rw [(by norm_num : 3840 * 2 = 7680)] at e2
  rw [(by norm_num : 3840 * 3 = 11520)] at e3
  rw [(by norm_num : 3840 * 4 = 15360)] at e4
  have e : mvf MVS x f = fld (MVS x) 3840 f := rfl
  rw [e, hM, mvRow_eq, hsub 1 le_rfl (by norm_num), hsub 2 (by norm_num) (by norm_num),
    hsub 3 (by norm_num) le_rfl, hlow, h4, fld_lor, fld_lor, fld_lor, fld_lor, e0, e1, e2, e3, e4]
  have hc : ∀ i < 240, (iform (vec i) (vec x) + 2 = f ↔ z i = f) := fun i hi => by
    have := hzi i hi
    omega
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ 5 ≤ f) with
    rfl | rfl | rfl | rfl | rfl | h5
  case inr.inr.inr.inr.inr =>
    have n0 : f ≠ 0 := by omega
    have n1 : f ≠ 1 := by omega
    have n2 : f ≠ 2 := by omega
    have n3 : f ≠ 3 := by omega
    have n4 : f ≠ 4 := by omega
    rw [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, Nat.zero_or, Nat.zero_or,
      Nat.zero_or, Nat.zero_or]
    unfold lsum
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    have h1 := hc i (Finset.mem_range.1 hi)
    have h2 := hz4 i (Finset.mem_range.1 hi)
    have h3 : ¬ (iform (vec i) (vec x) + 2 = (f : ℤ)) := fun h => by omega
    beta_reduce
    rw [if_neg h3, zero_mul]
  all_goals simp only [↓reduceIte, Nat.reduceEqDiff, Nat.zero_or, Nat.or_zero]
  all_goals
    refine lsum_congr fun i hi => ?_
    have := hc i hi
    have := hz4 i hi
    split_ifs <;> omega

include hD in
theorem mv_bit {V Y : ℕ} {QS MVS : ℕ → ℕ} (hvec : vec = vecOf 8 V)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    {x i f : ℕ} (hx : x < 240) (hi : i < 240) (hf : iform (vec i) (vec x) + 2 = f) :
    (mvf MVS x f).testBit (16 * i) = true := by
  obtain ⟨z, hz, hzi⟩ := zOf_eq hD hvec hVl hYc hYl hQb hq hx
  have hz4 : ∀ i < 240, z i ≤ 4 := fun i hi => by
    have := hzi i hi
    have := iform_root_bound hD hi hx
    omega
  have hM : MVS x = mvRow QS Y x := beq_eq_true.1 (hmv x hx)
  have hlow : LOW16 - geL (zOf QS Y x) 1 = lsum (fun i => 1 - if 1 ≤ z i then 1 else 0) := by
    rw [hz, geL_eq hz4 le_rfl (by norm_num), low16_eq, lsum_sub (fun i _ => by split_ifs <;> omega)]
  have hsub : ∀ v, 1 ≤ v → v ≤ 3 → geL (zOf QS Y x) v - geL (zOf QS Y x) (v + 1) =
      lsum (fun i => (if v ≤ z i then 1 else 0) - if v + 1 ≤ z i then 1 else 0) := by
    intro v h1 h3
    rw [hz, geL_eq hz4 h1 (by omega), geL_eq hz4 (by omega) (by omega),
      lsum_sub (fun i _ => by split_ifs <;> omega)]
  have h4 : geL (zOf QS Y x) 4 = lsum (fun i => if 4 ≤ z i then 1 else 0) := by
    rw [hz, geL_eq hz4 (by norm_num) le_rfl]
  have hfi : f = z i := by
    have := hzi i hi
    omega
  have hf4 : f ≤ 4 := hfi ▸ hz4 i hi
  have hbit : ∀ g : ℕ → ℕ, (∀ j < 240, g j ≤ 1) → g i = 1 → (lsum g).testBit (16 * i) = true :=
    fun g hg h1 => (testBit_lsum hg i).2 ⟨hi, h1⟩
  have e : mvf MVS x f = fld (MVS x) 3840 f := rfl
  rw [e, testBit_fld, hM, mvRow_eq, hsub 1 le_rfl (by norm_num), hsub 2 (by norm_num) (by norm_num),
    hsub 3 (by norm_num) le_rfl, hlow, h4, decide_eq_true (by omega : 16 * i < 3840), Bool.true_and]
  simp only [Nat.testBit_or, Bool.or_eq_true]
  interval_cases f
  · exact Or.inl (by
      rw [(by ring : 3840 * 0 + 16 * i = 16 * i)]
      exact hbit _ (fun j _ => by split_ifs <;> omega) (by simp [← hfi]))
  · refine Or.inr (Or.inl ?_)
    rw [(by ring : 3840 * 1 + 16 * i = 16 * i + 3840)]
    exact testBit_shl_add (hbit _ (fun j _ => by split_ifs <;> omega) (by simp [← hfi]))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [(by ring : 3840 * 2 + 16 * i = 16 * i + 7680)]
    exact testBit_shl_add (hbit _ (fun j _ => by split_ifs <;> omega) (by simp [← hfi]))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [(by ring : 3840 * 3 + 16 * i = 16 * i + 11520)]
    exact testBit_shl_add (hbit _ (fun j _ => by split_ifs <;> omega) (by simp [← hfi]))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [(by ring : 3840 * 4 + 16 * i = 16 * i + 15360)]
    exact testBit_shl_add (hbit _ (fun j _ => by split_ifs <;> omega) (by simp [← hfi]))

theorem ipK8_int {X Y v g : ℕ} {I : ℤ}
    (h : (dP 8 (fld X 256 v * fld Y 256 g) : ℤ) - dQ 8 (fld X 256 v * fld Y 256 g) = I)
    (hI : -2 ≤ I) : (ipK8 X Y v g : ℤ) = 4294967296 + I := by
  have hq : dQ 8 (fld X 256 v * fld Y 256 g) < 2 ^ 16 := by
    rw [dQ_eq]
    exact fld_lt _ _ _
  have e : ipK8 X Y v g = 4294967296 + dP 8 (fld X 256 v * fld Y 256 g) -
      dQ 8 (fld X 256 v * fld Y 256 g) := by
    simp only [ipK8, strictN_eq]
    rfl
  rw [e]
  omega

@[expose] noncomputable def candR (X Y : ℕ) (MVS : ℕ → ℕ) (t k a : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (mvf MVS k 2)
    (fun a ih => strictN ih fun acc => strictN (fld t 8 a) fun ta =>
      Nat.land acc (Nat.land
        (mvf MVS ta (Nat.sub (Nat.add (ipK8 X Y k a) 2) OFS))
        (mvf MVS a (Nat.sub (Nat.add OFS 2) (ipK8 X Y k ta))))) a

theorem candR_succ (X Y : ℕ) (MVS : ℕ → ℕ) (t k a : ℕ) :
    candR X Y MVS t k (a + 1) = candR X Y MVS t k a &&&
      (mvf MVS (fld t 8 a) (ipK8 X Y k a + 2 - OFS) &&&
        mvf MVS a (OFS + 2 - ipK8 X Y k (fld t 8 a))) := by
  change strictN (candR X Y MVS t k a) (fun acc => strictN (fld t 8 a) fun ta =>
      Nat.land acc (Nat.land
        (mvf MVS ta (Nat.sub (Nat.add (ipK8 X Y k a) 2) OFS))
        (mvf MVS a (Nat.sub (Nat.add OFS 2) (ipK8 X Y k ta))))) = _
  rw [strictN_eq, strictN_eq]
  rfl

theorem cand_eq_candR (X Y : ℕ) (MVS : ℕ → ℕ) (t k : ℕ) :
    cand X Y MVS t k = candR X Y MVS t k k := rfl

include hD in
theorem cand_bit {V X Y : ℕ} {QS MVS : ℕ → ℕ} (hvec : vec = vecOf 8 V)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    (hX : ∀ v < 240, ∀ g < 240, (dP 8 (fld X 256 v * fld Y 256 g) : ℤ) -
      dQ 8 (fld X 256 v * fld Y 256 g) = iform (vec v) (vec g))
    {t k x : ℕ} (hk : k < 8) (ht : ∀ a < k, fld t 8 a < 240) (hx : x < 240)
    (h0 : iform (vec x) (vec k) = 0)
    (h1 : ∀ a < k, iform (vec x) (vec (fld t 8 a)) = iform (vec k) (vec a) ∧
      iform (vec x) (vec a) = - iform (vec k) (vec (fld t 8 a))) :
    (cand X Y MVS t k).testBit (16 * x) = true := by
  have hO : OFS = 4294967296 := rfl
  rw [cand_eq_candR]
  suffices h : ∀ a ≤ k, (candR X Y MVS t k a).testBit (16 * x) = true from h k le_rfl
  intro a
  induction a with
  | zero =>
    intro _
    exact mv_bit hD hvec hVl hYc hYl hQb hq hmv (by omega) hx (by rw [h0]; rfl)
  | succ a ih =>
    intro ha
    rw [candR_succ, Nat.testBit_and, Nat.testBit_and,
      ih (by omega), Bool.true_and, Bool.and_eq_true]
    have hta := ht a (by omega)
    obtain ⟨e1, e2⟩ := h1 a (by omega)
    have b1 := iform_root_bound hD (by omega : k < 240) (by omega : a < 240)
    have b2 := iform_root_bound hD (by omega : k < 240) hta
    have i1 := ipK8_int (hX k (by omega) a (by omega)) b1.1
    have i2 := ipK8_int (hX k (by omega) _ hta) b2.1
    refine ⟨mv_bit hD hvec hVl hYc hYl hQb hq hmv hta hx ?_,
      mv_bit hD hvec hVl hYc hYl hQb hq hmv (by omega) hx ?_⟩
    · rw [hO]
      omega
    · rw [hO]
      omega

end Checks

theorem chWalk_spec (ND t k : ℕ) : ∀ c j prev acc cm, chWalk ND t k c j prev acc cm = true →
    (∀ i < c, fld ND 288 (j + i) &&& (2 ^ (8 * k) - 1) = t ∧
      (fld ND 288 (j + i) >>> 64) &&& 15 = k + 1) ∧
    ∀ b, cm.testBit b = true → acc.testBit b = true ∨
      ∃ i < c, 16 * fld (fld ND 288 (j + i)) 8 k = b := by
  intro c
  induction c with
  | zero =>
    intro j prev acc cm h
    have h' : acc = cm := beq_eq_true.1 h
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun b hb => Or.inl (h' ▸ hb)⟩
  | succ c ih =>
    intro j prev acc cm h
    have e : chWalk ND t k (c + 1) j prev acc cm =
        andB (Nat.beq (fld ND 288 j &&& ((1 <<< (8 * k)) - 1)) t)
        (andB (Nat.beq ((fld ND 288 j >>> 64) &&& 15) (k + 1))
        (andB (Nat.ble prev (fld (fld ND 288 j) 8 k)) (andB (bit cm (16 * fld (fld ND 288 j) 8 k))
          (chWalk ND t k c (j + 1) (fld (fld ND 288 j) 8 k + 1)
            (acc ||| (1 <<< (16 * fld (fld ND 288 j) 8 k))) cm)))) := by
      simp only [chWalk, strictB_eq]
      rfl
    rw [e] at h
    simp only [andB_eq_true, beq_eq_true] at h
    obtain ⟨h1, h2, -, -, hw⟩ := h
    obtain ⟨ih1, ih2⟩ := ih _ _ _ _ hw
    have hs : ∀ i, j + 1 + i = j + (i + 1) := fun i => by omega
    refine ⟨fun i hi => ?_, fun b hb => ?_⟩
    · rcases i with _ | i
      · rw [Nat.shiftLeft_eq, one_mul] at h1
        exact ⟨h1, h2⟩
      · rw [← hs]
        exact ih1 i (by omega)
    · rcases ih2 b hb with h3 | ⟨i, hi, h3⟩
      · rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow,
          Bool.or_eq_true, decide_eq_true_eq] at h3
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr ⟨0, by omega, by simpa using h3⟩
      · exact Or.inr ⟨i + 1, by omega, by rw [← hs]; exact h3⟩

theorem fld_pack (g : ℕ → ℕ) (hg : ∀ j, g j < 2 ^ 8) : ∀ n m,
    fld (Nat.rec (motive := fun _ => ℕ) 0
      (fun j ih => strictN ih fun acc => Nat.lor acc (Nat.shiftLeft (g j) (Nat.mul 8 j))) n) 8 m =
      if m < n then g m else 0 := by
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℕ, R = fun n => Nat.rec (motive := fun _ => ℕ) 0
      (fun j ih => strictN ih fun acc => Nat.lor acc (Nat.shiftLeft (g j) (Nat.mul 8 j))) n :=
    ⟨_, rfl⟩
  have e : ∀ n, R (n + 1) = R n ||| (g n <<< (8 * n)) := fun n => by
    rw [hR]
    exact strictN_eq _ _
  suffices h : ∀ n m, fld (R n) 8 m = if m < n then g m else 0 by
    intro n m
    have := h n m
    rw [hR] at this
    exact this
  intro n m
  induction n with
  | zero =>
    rw [hR]
    simp [fld_zero]
  | succ n ih =>
    rw [e, fld_lor, ih, fld_shl_w (hg n)]
    rcases lt_trichotomy m n with h | rfl | h
    · simp [h, show m ≠ n by omega, show m < n + 1 by omega]
    · simp
    · simp [show ¬ m < n by omega, show m ≠ n by omega, show ¬ m < n + 1 by omega]

theorem fld_cj8 (RTs : ℕ → ℕ) (t l : ℕ) {m : ℕ} (hm : m < 8) :
    fld (cj8 RTs t l) 8 m = fld (RTs l) 8 (fld (RTs (fld t 8 l)) 8 (fld t 8 m)) := by
  have h := fld_pack (fun j => fld (RTs l) 8 (fld (RTs (fld t 8 l)) 8 (fld t 8 j)))
    (fun j => fld_lt _ _ _) 8 m
  rw [if_pos hm] at h
  rw [← h]
  simp only [cj8, strictN_eq]
  rfl

theorem cjW_succ (RTs : ℕ → ℕ) (wl w t : ℕ) :
    cjW RTs (wl + 1) w t = cjW RTs wl (w >>> 3) (cj8 RTs t (w &&& 7)) := by
  change strictN (cj8 RTs t (Nat.land w 7)) (fun t' => cjW RTs wl (Nat.shiftRight w 3) t') = _
  rw [strictN_eq]
  rfl

section Leaf

variable
  {vec : ℕ → Fin Tag.E8.rank → ℤ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ} {RTs : ℕ → ℕ}
  (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v) adj neg)

include hD in
theorem cjW_spec : ∀ wl w t (ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ)),
    (∀ x y, iform (ψ x) (ψ y) = iform x y) →
    (∀ m < 8, fld t 8 m < 240 ∧ ψ (vec m) = vec (fld t 8 m)) →
    ∃ h : WeylGroup Tag.E8, ∀ m : Fin Tag.E8.rank,
      h • ψ (h⁻¹ • vec m) = vec (fld (cjW RTs wl w t) 8 m) := by
  intro wl
  induction wl with
  | zero =>
    intro w t ψ _ hψ
    refine ⟨1, fun m => ?_⟩
    rw [inv_one, one_smul, one_smul]
    exact (hψ m m.2).2
  | succ wl ih =>
    intro w t ψ hiso hψ
    have hl : w &&& 7 < 8 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
    set l := w &&& 7 with hldef
    let s : WeylGroup Tag.E8 := simple Tag.E8 ⟨l, hl⟩
    have hvl : vec l = Pi.single (⟨l, hl⟩ : Fin Tag.E8.rank) 1 := hD.simple ⟨l, hl⟩
    have hs : ∀ v : Fin Tag.E8.rank → ℤ, s • v = v - iform v (vec l) • vec l := by
      intro v
      change simple Tag.E8 ⟨l, hl⟩ • v = _
      rw [simple_smul, hvl, iform_single Tag.E8 e8_sym]
      rfl
    have hll : iform (vec l) (vec l) = 2 := iform_root_self hD (by omega)
    have hss : ∀ v : Fin Tag.E8.rank → ℤ, s • s • v = v := by
      intro v
      rw [hs v, hs (v - iform v (vec l) • vec l), iform_sub_left, iform_smul_left, hll]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hsinv : ∀ v : Fin Tag.E8.rank → ℤ, s⁻¹ • v = s • v := fun v => by
      rw [inv_smul_eq_iff, hss]
    let ψ' : AddMonoid.End (Fin Tag.E8.rank → ℤ) :=
      { toFun := fun x => s • ψ (s • x)
        map_zero' := by simp
        map_add' := fun a b => by simp only [smul_add, map_add] }
    have hψ' : ∀ x, ψ' x = s • ψ (s • x) := fun _ => rfl
    have hiso' : ∀ x y, iform (ψ' x) (ψ' y) = iform x y := by
      intro x y
      rw [hψ', hψ', iform_smul, hiso, iform_smul]
    have htl := hψ l hl
    have htup : ∀ m < 8, fld (cj8 RTs t l) 8 m < 240 ∧
        ψ' (vec m) = vec (fld (cj8 RTs t l) 8 m) := by
      intro m hm
      have htm := hψ m hm
      obtain ⟨r1, hr1⟩ := hD.refl _ htl.1 _ htm.1
      obtain ⟨r2, hr2⟩ := hD.refl _ (by omega : l < 240) _ r1
      rw [fld_cj8 RTs t l hm]
      refine ⟨r2, ?_⟩
      rw [hψ', hs (vec m), map_sub, map_zsmul, htm.2, htl.2, ← hiso, htm.2, htl.2, ← hr1, hs,
        ← hr2]
    obtain ⟨h', hh'⟩ := ih (w >>> 3) (cj8 RTs t l) ψ' hiso' htup
    refine ⟨h' * s, fun m => ?_⟩
    rw [cjW_succ, ← hh' m, _root_.mul_inv_rev, mul_smul, mul_smul, hsinv, hψ']

end Leaf

theorem searchRaw_of_checks
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {adj : ℕ → ℕ → Bool}
    {neg : ℕ → ℕ} {V X Y ND T0 tot : ℕ} {RTs QS MVS : ℕ → ℕ} (hvec : vec = vecOf 8 V)
    (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v) adj neg)
    (hX : ∀ v < 240, ∀ g < 240, (dP 8 (fld X 256 v * fld Y 256 g) : ℤ) -
      dQ 8 (fld X 256 v * fld Y 256 g) = iform (vec v) (vec g))
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    (hsz : ND < 2 ^ (288 * tot)) (hnd : ∀ j < tot, ndOK X Y RTs MVS ND T0 j = true)
    (hnd0 : nd0OK ND T0 = true) : SearchRaw vec ND T0 tot := by
  have hM64 : (18446744073709551615 : ℕ) = 2 ^ 64 - 1 := by norm_num
  have hndL : ∀ j, ndL ND j = (List.range ((fld ND 288 j >>> 64) &&& 15)).map
      (fun a => fld (fld ND 288 j &&& 18446744073709551615) 8 a) := fun j => rfl
  have hnz : ∀ c, (fld ND 288 c >>> 64) &&& 15 ≠ 0 → c < tot := by
    intro c hc
    by_contra h
    rw [fld_eq_zero_of_lt 288 tot ND hsz (by omega)] at hc
    exact hc rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    have h : fld ND 288 0 &&& (2 ^ 68 - 1) = fld T0 8 0 + 2 ^ 64 := beq_eq_true.1 hnd0
    rw [Nat.and_two_pow_sub_one_eq_mod] at h
    have hb : fld T0 8 0 < 2 ^ 8 := fld_lt _ _ _
    have hlen : (fld ND 288 0 >>> 64) &&& 15 = 1 := by
      rw [Nat.shiftRight_eq_div_pow, (by norm_num : (15 : ℕ) = 2 ^ 4 - 1),
        Nat.and_two_pow_sub_one_eq_mod, ← Nat.mod_mul_right_div_self,
        (by norm_num : (2 : ℕ) ^ 64 * 2 ^ 4 = 2 ^ 68), h]
      norm_num at hb ⊢
      omega
    have hent : fld (fld ND 288 0 &&& 18446744073709551615) 8 0 = fld T0 8 0 := by
      rw [hM64, Nat.and_two_pow_sub_one_eq_mod,
        ← Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : 64 ≤ 68)), h, fld_eq]
      norm_num at hb ⊢
      omega
    refine ⟨hnz 0 (by rw [hlen]; decide), ?_⟩
    rw [hndL, hlen]
    simp [hent]
  ·
    intro j hj hent hlen x hx
    have hL : (ndL ND j).length = (fld ND 288 j >>> 64) &&& 15 := by rw [hndL]; simp
    rw [hL] at hlen
    have h := hnd j hj
    simp only [ndOK, strictB_eq, andB_eq_true, ble_eq_true, beq_eq_true, boolRec_true,
      blt_eq_true, nland, nshr, nmul, nsub, nshl] at h
    obtain ⟨-, -, -, hch, -⟩ := h
    obtain ⟨hrec, hcov⟩ := chWalk_spec ND _ _ _ _ _ _ _ (hch hlen)
    have ht : ∀ a < (fld ND 288 j >>> 64) &&& 15,
        fld (fld ND 288 j &&& 18446744073709551615) 8 a < 240 := fun a ha =>
      hent _ (by rw [hndL]; exact List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩)
    have hget : ∀ a (ha : a < (ndL ND j).length),
        (ndL ND j)[a] = fld (fld ND 288 j &&& 18446744073709551615) 8 a := by
      intro a ha
      simp [hndL]
    obtain ⟨hx240, h0, h1⟩ := hx
    rw [hL] at h0
    have h1' : ∀ a < (fld ND 288 j >>> 64) &&& 15,
        iform (vec x) (vec (fld (fld ND 288 j &&& 18446744073709551615) 8 a)) =
          iform (vec ((fld ND 288 j >>> 64) &&& 15)) (vec a) ∧
        iform (vec x) (vec a) = - iform (vec ((fld ND 288 j >>> 64) &&& 15))
          (vec (fld (fld ND 288 j &&& 18446744073709551615) 8 a)) := by
      intro a ha
      have := h1 a (by rw [hL]; exact ha)
      rw [hget, hL] at this
      exact this
    have hcb := cand_bit hD hvec hVl hYc hYl hQb hq hmv hX hlen ht hx240 h0 h1'
    rcases hcov _ hcb with h2 | ⟨i, hi, hxi⟩
    · simp at h2
    obtain ⟨hr1, hr2⟩ := hrec i hi
    refine ⟨_, hnz _ (by rw [hr2]; omega), ?_⟩
    rw [hndL, hndL j, hr2, List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · refine List.map_congr_left fun a ha => ?_
      have ha' := List.mem_range.1 ha
      rw [← hr1, fld_land_mask (by omega), hM64, fld_land_mask (by omega)]
    · rw [hM64, fld_land_mask (by omega)]
      congr 1
      omega
  ·
    intro j hj hent hlen ψ hiso hψ
    have hL : (ndL ND j).length = (fld ND 288 j >>> 64) &&& 15 := by rw [hndL]; simp
    rw [hL] at hlen
    have h := hnd j hj
    simp only [ndOK, strictB_eq, andB_eq_true, ble_eq_true, beq_eq_true, boolRec_true,
      blt_eq_true, nland, nshr, nmul, nsub, nshl] at h
    obtain ⟨-, -, -, -, hlf⟩ := h
    have hw := hlf (by rw [hlen]; rfl)
    obtain ⟨g, hg⟩ := cjW_spec hD _ _ _ ψ hiso (fun m hm => ⟨hent _ (by
        rw [hndL]
        exact List.mem_map.2 ⟨m, List.mem_range.2 (by omega), rfl⟩), by
      have := hψ ⟨m, hm⟩
      have hm' : m < (fld ND 288 j >>> 64) &&& 15 := by rw [hlen]; exact hm
      rw [List.getD_eq_getElem?_getD, hndL, List.getElem?_map, List.getElem?_range hm']
        at this
      exact this⟩)
    exact ⟨g, fun m => by rw [hg m, hw]⟩

end Search

end CFSG.KC.TcRes

end
