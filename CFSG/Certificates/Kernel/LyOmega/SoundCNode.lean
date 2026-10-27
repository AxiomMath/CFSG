module

public import Certificates.Data.Kernel.LyOmega.Chart
public import CFSG.Certificates.Kernel.LyOmega.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LyOmega.TreeCoreMul
import all CFSG.Certificates.Kernel.LyOmega.SoundMulCore
import all CFSG.Certificates.Kernel.LyOmega.SoundB1
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.LyOm.CN

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CFSG.KS.Ord CFSG.KS.PackFld CFSG.KS.LyOm.TreeCore CFSG.KS.LyOm.MC

private theorem validM_pk {w n p nb X : ℕ} (hw : 0 < w) (hnb : nb = w * n) (hp : p ≤ 2 ^ (w - 1))
    (h : validM p nb (pk w n (fun _ => 1)) (pk w n (fun _ => 2 ^ (w - 1))) X = true) :
    X < 2 ^ (w * n) ∧ ∀ t < n, lane w X t < p := by
  subst hnb
  unfold validM at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h
  have e2 := two_pow_pred hw
  have hlt : X < 2 ^ (w * n) := by
    have h1' : X >>> (w * n) = 0 := Nat.eq_of_beq_eq_true h1
    rw [Nat.shiftRight_eq_div_pow] at h1'
    rcases Nat.div_eq_zero_iff.1 h1' with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · exact h
  obtain ⟨a, ha_eq, ha⟩ : ∃ a, X = pk w n a ∧ ∀ t < n, a t < 2 ^ w :=
    ⟨lane w X, pk_lane hw hlt, fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  rw [ha_eq] at h2 h3 ⊢
  have h0 := Nat.two_pow_pos (w - 1)
  have hHb : ∀ t < n, (2 : ℕ) ^ (w - 1) < 2 ^ w := fun _ _ => by omega
  have htop : ∀ t < n, a t < 2 ^ (w - 1) := by
    intro t ht
    have h2' : pk w n a &&& pk w n (fun _ => 2 ^ (w - 1)) = 0 := Nat.eq_of_beq_eq_true h2
    have hF := fld_and (fld_pk ha) (fld_pk hHb)
    rw [h2'] at hF
    have hb := hF t (w - 1) (by omega)
    rw [Nat.zero_testBit] at hb
    simp only [ht, ↓reduceIte] at hb
    have ha2 : a t < 2 * 2 ^ (w - 1) := by have := ha t ht; omega
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, testBit_top ha2] at hb
    simpa using hb
  have h3' : ((pk w n a ||| pk w n (fun _ => 2 ^ (w - 1))) - p * pk w n (fun _ => 1)) &&&
      pk w n (fun _ => 2 ^ (w - 1)) = 0 := Nat.eq_of_beq_eq_true h3
  rw [top_H hw htop hp] at h3'
  unfold pk at h3'
  refine ⟨pk_lt ha, fun t ht => ?_⟩
  rw [lane_pk ha ht]
  by_contra hn
  have hz := Finset.sum_eq_zero_iff.1 h3' t (Finset.mem_range.2 ht)
  have hn' : p ≤ a t := Nat.le_of_not_lt hn
  simp only [hn', ↓reduceIte] at hz
  exact absurd hz (Nat.mul_ne_zero (Nat.two_pow_pos _).ne' (Nat.two_pow_pos _).ne')

private theorem lc_of_lanes {w r c X : ℕ} (hX : X < 2 ^ (w * (c * r)))
    (hl : ∀ t < c * r, lane w X t < 5) : LCanon w r c X := by
  refine ⟨by rw [Nat.mul_assoc]; exact hX, fun i hi j hj => ?_⟩
  have hidx : c * i + j < c * r := by
    have := Nat.mul_le_mul_left c (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at this
    omega
  have := hl _ hidx
  unfold lane at this
  have e : w * c * i + w * j = w * (c * i + j) := by ring
  rw [e]
  exact this

private theorem vecU_eq' (w S d RM v M : ℕ) : vecU w S d RM v M =
    ∑ k ∈ Finset.range d, bitsN v (w * k) w * ((M >>> (S * k)) &&& RM) := by
  unfold vecU
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

private theorem bitsN_eq (v o m : ℕ) : bitsN v o m = v / 2 ^ o % 2 ^ m := by
  change (v >>> o) &&& (1 <<< m - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem vec_core {w r m d S T : ℕ} {v b : ℕ → ℕ} (hw : 0 < w) (hS : S = w * r)
    (h5 : 5 ≤ 2 ^ w) (hv : ∀ k < d, v k < 5) (hb : ∀ t < r * m, b t < 5) (hdm : d ≤ m)
    (hT : 5 * 2 ^ T ≤ 2 ^ (w - 1)) (hB : 16 * d < 2 ^ (w - 1)) (hB2 : 16 * d < 5 * 2 ^ (T + 1)) :
    redP w (pk w r (fun _ => 1)) (pk w r (fun _ => 2 ^ (w - 1))) 5 T
      (vecU w S d (2 ^ S - 1) (pk w d v) (pk w (r * m) b)) =
    pk w r (fun j => (∑ k ∈ Finset.range d, v k * b (r * k + j)) % 5) := by
  have hv' : ∀ k < d, v k < 2 ^ w := fun k hk => lt_of_lt_of_le (hv k hk) h5
  have hb' : ∀ t < r * m, b t < 2 ^ w := fun t ht => lt_of_lt_of_le (hb t ht) h5
  have hsum : vecU w S d (2 ^ S - 1) (pk w d v) (pk w (r * m) b) =
      pk w r (fun j => ∑ k ∈ Finset.range d, v k * b (r * k + j)) := by
    rw [vecU_eq']
    subst hS
    calc _ = ∑ k ∈ Finset.range d, v k * pk w r (fun j => b (r * k + j)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := Finset.mem_range.1 hk
          rw [bitsN_eq, tcm_row hw hb' (by omega : k < m)]
          have := lane_pk hv' hk'
          unfold lane at this
          rw [this]
      _ = _ := by
          unfold pk
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  rw [hsum]
  have hbd : ∀ j < r, ∑ k ∈ Finset.range d, v k * b (r * k + j) ≤ 16 * d :=
    fun j hj => tcm_bound (fun k hk => hv k hk) (fun k hk => hb _ (idx (by omega) hj))
  exact redP_pk hw hT (fun t ht => by have := hbd t ht; omega)
    (fun t ht => by have := hbd t ht; omega)

private theorem bVec7_pk {C : BConsts} (hC : bConstsOK C = true) {x y : ℕ → ℕ}
    (hx : ∀ t < 7, x t < 5) (hy : ∀ t < 111 * 7, y t < 5) :
    bVec7 C (pk 12 7 x) (pk 12 (111 * 7) y) =
      pk 12 111 (fun j => (∑ k ∈ Finset.range 7, x k * y (111 * k + j)) % 5) := by
  obtain ⟨-, -, -, -, -, hLV, hHV, -⟩ := bc_facts hC
  unfold bVec7 vecR rmB
  rw [tcm_RM, hLV, hHV]
  exact vec_core (S := nat_lit 1332) (by norm_num) (by norm_num) (by norm_num) hx hy (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem bVec_pk {C : BConsts} (hC : bConstsOK C = true) {x y : ℕ → ℕ}
    (hx : ∀ t < 111, x t < 5) (hy : ∀ t < 111 * 111, y t < 5) :
    bVec C (pk 12 111 x) (pk 12 (111 * 111) y) =
      pk 12 111 (fun j => (∑ k ∈ Finset.range 111, x k * y (111 * k + j)) % 5) := by
  obtain ⟨-, -, -, -, -, hLV, hHV, -⟩ := bc_facts hC
  unfold bVec vecR rmB
  rw [tcm_RM, hLV, hHV]
  exact vec_core (S := nat_lit 1332) (by norm_num) (by norm_num) (by norm_num) hx hy (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem div_split (u a b c m : ℕ) (h : b + c ≤ m) :
    u / 2 ^ (a + b) % 2 ^ c = u / 2 ^ a % 2 ^ m / 2 ^ b % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < c
  · have h1 : j + b < m := by omega
    simp only [hj, h1, decide_true, Bool.true_and]
    congr 1
    ring
  · simp [hj]

private theorem witOK_sound {C : BConsts} (hC : bConstsOK C = true) {WC : ℕ → ℕ} {N c w : ℕ}
    (hN : LCanon 12 7 111 N) (hWC : ∀ e < c, LCanon 12 111 111 (WC (c + 8 * e)))
    (h : witOK C WC N c w = true) :
    ∀ e < c, ¬ IsUnit (lastCols (blkM N * bigM (WC (c + 8 * e)))).det := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, -, -, -, hLW, hHW, -⟩ := bc_facts hC
  intro e he
  unfold witOK at h
  have he' := (SB1.recAnd_iff _ c).1 h e he
  simp only [SB1.letB_eq, SB1.bAnd_eq, Bool.and_eq_true] at he'
  generalize fldW w (Nat.mul 84 e) 84 = x at he'
  obtain ⟨hx0, hxv, hz⟩ := he'
  have hx0' : x ≠ 0 := by
    intro h0
    rw [h0] at hx0
    exact absurd hx0 (by decide)
  rw [hLW, hHW] at hxv
  obtain ⟨hxlt, hxl⟩ := validM_pk (n := 7) (by norm_num) (by norm_num) (by norm_num) hxv
  have hxe : x = pk 12 7 (lane 12 x) := pk_lane (by norm_num) hxlt
  set xv := lane 12 x with hxv_def
  obtain ⟨y, hye, hy, -⟩ := lc_lanes (n := 111 * 7) (by norm_num) hN le_rfl
  obtain ⟨g, hge, hg, -⟩ := lc_lanes (n := 111 * 111) (by norm_num) (hWC e he)
    le_rfl
  have hge' : WC (Nat.add c (Nat.mul 8 e)) = pk 12 (111 * 111) g := hge
  rw [hxe, hye, bVec7_pk hC hxl hy, hge', bVec_pk hC (fun t _ => Nat.mod_lt _ (by norm_num)) hg,
    SB1.fldW_eq] at hz
  have hz' := Nat.eq_of_beq_eq_true hz
  set z : ℕ → ℕ := fun k => (∑ l ∈ Finset.range 7, xv l * y (111 * l + k)) % 5 with hz_def
  have hlane : ∀ j < 7, (∑ k ∈ Finset.range 111, z k * g (111 * k + (104 + j))) % 5 = 0 := by
    intro j hj
    have h1 := div_split (pk 12 111 (fun j => (∑ k ∈ Finset.range 111, z k *
      g (111 * k + j)) % 5)) 1248 (12 * j) 12 84 (by omega)
    rw [hz', Nat.zero_div, Nat.zero_mod, show 1248 + 12 * j = 12 * (104 + j) by ring] at h1
    have h2 := lane_pk (w := 12) (n := 111) (g := fun j => (∑ k ∈ Finset.range 111, z k *
      g (111 * k + j)) % 5) (fun t _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
      (show 104 + j < 111 by omega)
    unfold lane at h2
    rw [h2] at h1
    exact h1
  obtain ⟨l0, hl0, hxl0⟩ : ∃ l < 7, xv l ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply hx0'
    rw [hxe]
    unfold pk
    exact Finset.sum_eq_zero fun t ht => by rw [hall t (Finset.mem_range.1 ht), Nat.zero_mul]
  have hdet : (lastCols (blkM N * bigM (WC (c + 8 * e)))).det = 0 := by
    refine (Matrix.exists_vecMul_eq_zero_iff).1 ⟨fun l => ((xv l.val : ℕ) : ZMod 5), ?_, ?_⟩
    · intro h0
      have := congrFun h0 ⟨l0, hl0⟩
      simp only [Pi.zero_apply] at this
      have h2 := (ZMod.natCast_eq_natCast_iff' (xv l0) 0 5).1 (by rw [this]; simp)
      rw [Nat.mod_eq_of_lt (hxl l0 hl0)] at h2
      exact hxl0 (by simpa using h2)
    · funext j
      have hW : WC (c + 8 * e) = pk 12 (111 * 111) g := hge
      rw [hW, hye]
      simp only [Matrix.vecMul, dotProduct, lastCols, Matrix.mul_apply, blkM, bigM, Pi.zero_apply]
      have hj := hlane j.val j.isLt
      have hc0 : ((∑ k ∈ Finset.range 111, z k * g (111 * k + (104 + j.val)) : ℕ) : ZMod 5) = 0 := by
        rw [← ZMod.natCast_mod, hj, Nat.cast_zero]
      rw [← hc0]
      simp only [hz_def]
      push_cast [ZMod.natCast_mod]
      have e1 : ∀ (l : Fin 7) (k : Fin 111), ent 12 1332 (pk 12 777 y) l k *
          ent 12 1332 (pk 12 12321 g) k (104 + j) =
          ((y (111 * l.val + k.val) : ℕ) : ZMod 5) * ((g (111 * k.val + (104 + j.val)) : ℕ) : ZMod 5) := by
        intro l k
        rw [ent_pk (c := 111) (by norm_num) (fun t ht => lt_of_lt_of_le (hy t (by omega)) (by norm_num))
            (by omega),
          ent_pk (c := 111) (by norm_num) (fun t ht => lt_of_lt_of_le (hg t (by omega)) (by norm_num))
            (by omega)]
      simp only [e1, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm, ← sum_fin]
      refine Finset.sum_congr rfl fun k _ => ?_
      beta_reduce
      rw [← sum_fin]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
  rw [hdet]
  exact not_isUnit_zero

private theorem last7_one {C : BConsts} (hC : bConstsOK C = true) {N : ℕ} (hN : LCanon 12 7 111 N)
    (h : last7 C N = C.ONE7) : lastCols (blkM N) = 1 := by
  obtain ⟨-, -, -, hONE, hM, -⟩ := bc_facts hC
  obtain ⟨y, hye, hy, -⟩ := lc_lanes (n := 111 * 7) (by norm_num) hN le_rfl
  have hone : ∀ q < 7, ∀ l < 7,
      rep1 1344 7 / 2 ^ (12 * (111 * q + l)) % 2 ^ 12 = if q = l then 1 else 0 := by
    decide +kernel
  change (N >>> (12 * 104)) &&& C.MASK7 = C.ONE7 at h
  rw [hye, hM, cols7_pk hy le_rfl, hONE] at h
  ext i j
  have hl := congrArg (fun Z => Z / 2 ^ (12 * (111 * i.val + j.val)) % 2 ^ 12) h
  rw [hone i.val i.isLt j.val j.isLt] at hl
  have h2 := lane_pk (w := 12) (n := 111 * 7) (g := fun t => if t % 111 < 7 then y (t + 104) else 0)
    (fun t ht => by split <;> [exact lt_of_lt_of_le (hy _ (by omega)) (by norm_num); norm_num])
    (idx i.isLt (show j.val < 111 by omega))
  unfold lane at h2
  rw [h2] at hl
  have hk : (111 * i.val + j.val) % 111 < 7 := by rw [(dm_eq (by omega)).2]; exact j.isLt
  simp only [hk, ↓reduceIte] at hl
  simp only [lastCols, blkM, Matrix.one_apply]
  rw [hye, ent_pk (c := 111) (by norm_num) (fun t ht => lt_of_lt_of_le (hy t ht) (by norm_num))
    (show 111 * i.val + (104 + j.val) < 111 * 7 by omega),
    show 111 * i.val + (104 + j.val) = 111 * i.val + j.val + 104 by ring, hl]
  by_cases hij : i = j
  · subst hij
    simp
  · have : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, this]

private theorem parent_rel {C : BConsts} (hC : bConstsOK C = true) {Np N G : ℕ}
    (hNp : LCanon 12 7 111 Np) (hN : LCanon 12 7 111 N) (hG : LCanon 12 111 111 G)
    (h : sameSpanL C N (bMul C Np G) = true) :
    ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5), blkM Np * bigM G = M * blkM N := by
  obtain ⟨hY, hYe⟩ := MC.bMul_sound hC hNp hG
  exact ⟨_, hYe.symm.trans (MC.sameSpanL_sound hC hN hY h)⟩

theorem bVld_sound {C : BConsts} (hC : bConstsOK C = true) {X : ℕ}
    (h : validM 5 9324 C.L7 C.H7 X = true) : LCanon 12 7 111 X := by
  obtain ⟨hL, hH, -⟩ := bc_facts hC
  rw [hL, hH] at h
  obtain ⟨hlt, hl⟩ := validM_pk (n := 111 * 7) (by norm_num) (by norm_num) (by norm_num) h
  exact lc_of_lanes hlt hl

private theorem cNode_core {C : BConsts} (hC : bConstsOK C = true) {KX PT WT GT WC : ℕ → ℕ}
    {nc n i : ℕ}
    (hGT : ∀ j < i, ∀ s < 2, chartOf (getRec PT 32 i) < nc →
      LCanon 12 111 111 (GT (s + 2 * chartOf (getRec PT 32 j) + 16 * chartOf (getRec PT 32 i))))
    (hWC : chartOf (getRec PT 32 i) < nc → ∀ e < chartOf (getRec PT 32 i),
      LCanon 12 111 111 (WC (chartOf (getRec PT 32 i) + 8 * e)))
    (hKX : ∀ j < i, LCanon 12 7 111 (getRec KX 9324 j))
    (h : cNode C KX PT WT GT WC nc n i = true) :
    chartOf (getRec PT 32 i) < nc ∧ LCanon 12 7 111 (getRec KX 9324 i) ∧
      lastCols (blkM (getRec KX 9324 i)) = 1 ∧
      (∀ e < chartOf (getRec PT 32 i), ¬ IsUnit (lastCols (blkM (getRec KX 9324 i) *
        bigM (WC (chartOf (getRec PT 32 i) + 8 * e)))).det) ∧
      (0 < i → fldW (getRec PT 32 i) 0 20 < i ∧ fldW (getRec PT 32 i) 20 4 < 2 ∧
        ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
          blkM (getRec KX 9324 (fldW (getRec PT 32 i) 0 20)) *
            bigM (GT (fldW (getRec PT 32 i) 20 4 + 2 * chartOf (getRec PT 32 (fldW (getRec PT 32 i) 0 20))
              + 16 * chartOf (getRec PT 32 i))) = M * blkM (getRec KX 9324 i)) := by
  unfold cNode at h
  simp only [SB1.letB_eq, SB1.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hc, hv, hl7, hw, hpar⟩ := h
  have hN : LCanon 12 7 111 (getRec KX 9324 i) := bVld_sound hC hv
  have hc' := SB1.blt_iff.1 hc
  refine ⟨hc', hN, last7_one hC hN (Nat.eq_of_beq_eq_true hl7),
    fun e he => witOK_sound hC hN (hWC hc') hw e he, fun hi => ?_⟩
  have hi0 : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun hh => by rw [SB1.beq_iff] at hh; omega
  rw [hi0] at hpar
  simp only [Bool.and_eq_true] at hpar
  obtain ⟨hp, hs, hsp⟩ := hpar
  have hp' := SB1.blt_iff.1 hp
  have hs' := SB1.blt_iff.1 hs
  refine ⟨hp', hs', ?_⟩
  have hG := hGT _ hp' _ hs' hc'
  rw [Nat.add_assoc] at hG
  obtain ⟨M, hM⟩ := parent_rel hC (hKX _ hp') hN hG hsp
  exact ⟨M, by rw [Nat.add_assoc]; exact hM⟩

theorem cNode_sound {C : BConsts} (hC : bConstsOK C = true) {KX PT WT GT WC : ℕ → ℕ} {nc n i : ℕ}
    (hGT : ∀ k, LCanon 12 111 111 (GT k)) (hWC : ∀ k, LCanon 12 111 111 (WC k))
    (hKX : ∀ j < i, LCanon 12 7 111 (getRec KX 9324 j))
    (h : cNode C KX PT WT GT WC nc n i = true) :
    chartOf (getRec PT 32 i) < nc ∧ LCanon 12 7 111 (getRec KX 9324 i) ∧
      lastCols (blkM (getRec KX 9324 i)) = 1 ∧
      (∀ e < chartOf (getRec PT 32 i), ¬ IsUnit (lastCols (blkM (getRec KX 9324 i) *
        bigM (WC (chartOf (getRec PT 32 i) + 8 * e)))).det) ∧
      (0 < i → fldW (getRec PT 32 i) 0 20 < i ∧ fldW (getRec PT 32 i) 20 4 < 2 ∧
        ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
          blkM (getRec KX 9324 (fldW (getRec PT 32 i) 0 20)) *
            bigM (GT (fldW (getRec PT 32 i) 20 4 + 2 * chartOf (getRec PT 32 (fldW (getRec PT 32 i) 0 20))
              + 16 * chartOf (getRec PT 32 i))) = M * blkM (getRec KX 9324 i)) :=
  cNode_core hC (fun _ _ _ _ _ => hGT _) (fun _ _ _ => hWC _) hKX h

theorem cNode_sound' {C : BConsts} (hC : bConstsOK C = true) {KX PT WT GT WC : ℕ → ℕ} {nc n i : ℕ}
    (hGT : ∀ s < 2, ∀ c < nc, ∀ c' < nc, LCanon 12 111 111 (GT (s + 2 * c + 16 * c')))
    (hWC : ∀ e c, e < c → c < nc → LCanon 12 111 111 (WC (c + 8 * e)))
    (hKX : ∀ j < i, LCanon 12 7 111 (getRec KX 9324 j) ∧ chartOf (getRec PT 32 j) < nc)
    (h : cNode C KX PT WT GT WC nc n i = true) :
    chartOf (getRec PT 32 i) < nc ∧ LCanon 12 7 111 (getRec KX 9324 i) ∧
      lastCols (blkM (getRec KX 9324 i)) = 1 ∧
      (∀ e < chartOf (getRec PT 32 i), ¬ IsUnit (lastCols (blkM (getRec KX 9324 i) *
        bigM (WC (chartOf (getRec PT 32 i) + 8 * e)))).det) ∧
      (0 < i → fldW (getRec PT 32 i) 0 20 < i ∧ fldW (getRec PT 32 i) 20 4 < 2 ∧
        ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
          blkM (getRec KX 9324 (fldW (getRec PT 32 i) 0 20)) *
            bigM (GT (fldW (getRec PT 32 i) 20 4 + 2 * chartOf (getRec PT 32 (fldW (getRec PT 32 i) 0 20))
              + 16 * chartOf (getRec PT 32 i))) = M * blkM (getRec KX 9324 i)) :=
  cNode_core hC (fun j hj s hs hc => hGT s hs _ (hKX j hj).2 _ hc)
    (fun hc e he => hWC e _ he hc) (fun j hj => (hKX j hj).1) h

end CFSG.KS.LyOm.CN

end
