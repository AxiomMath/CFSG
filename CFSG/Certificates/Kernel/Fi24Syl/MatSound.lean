module

public import Certificates.Data.Kernel.Fi24Syl.Defs
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.Fi24Syl

open CFSG.KC.Ord CFSG.KC.Fi24Syl CFSG.KS.Ord CFSG.AGLEmbedding.R3 Matrix

noncomputable abbrev mat7 (X : ℕ) : Matrix (Fin 7) (Fin 7) (ZMod 3) := ordMat 3 7 6 42 X

abbrev C7 (X : ℕ) : Prop := Canon 3 7 6 X

@[expose] noncomputable def nOf (M : ℕ) : ℕ := redP 6 L7 H7 3 3 (Nat.add M TWO7)

theorem consts7 : constsOK 3 6 42 7 3 L7 H7 CM7 RM ONE7 LV7 HV7 = true := by decide +kernel

theorem mul7_sound {A B : ℕ} (hA : C7 A) (hB : C7 B) :
    C7 (mul7 A B) ∧ mat7 (mul7 A B) = mat7 A * mat7 B :=
  mulR_sound consts7 hA hB

theorem one7_sound : C7 ONE7 ∧ mat7 ONE7 = 1 := one_sound consts7

private theorem L7_eq : L7 = pk 6 (7 * 7) (fun _ => 1) := (consts_facts consts7).2.2.2.2.2.2.1

private theorem H7_eq : H7 = pk 6 (7 * 7) (fun _ => 2 ^ (6 - 1)) :=
  (consts_facts consts7).2.2.2.2.2.2.2.1

private theorem ONE7_eq : ONE7 = pk 6 (7 * 7) (fun t => if t / 7 = t % 7 then 1 else 0) :=
  (consts_facts consts7).2.2.2.2.2.2.2.2.2.2

private theorem TWO7_eq : TWO7 = ONE7 * 2 := by decide +kernel

theorem mat7_apply (X : ℕ) (i j : Fin 7) :
    mat7 X i j = ((lane 6 X (7 * i.val + j.val) : ℕ) : ZMod 3) := by
  unfold mat7 ordMat lane
  have e : 42 * i.val + 6 * j.val = 6 * (7 * i.val + j.val) := by ring
  rw [e]

private theorem lane_lt {X : ℕ} (hX : C7 X) {t : ℕ} (ht : t < 7 * 7) : lane 6 X t < 3 := hX.2 t ht

theorem canon7_inj {A B : ℕ} (hA : C7 A) (hB : C7 B) (h : mat7 A = mat7 B) : A = B := by
  rw [pk_lane (by norm_num) hA.1, pk_lane (by norm_num) hB.1]
  refine pk_congr fun t ht => ?_
  have hi : t / 7 < 7 := by omega
  have hj : t % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have h1 := congrFun (congrFun h ⟨t / 7, hi⟩) ⟨t % 7, hj⟩
  rw [mat7_apply, mat7_apply] at h1
  have e : 7 * (t / 7) + t % 7 = t := Nat.div_add_mod t 7
  simp only [e] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  rwa [Nat.mod_eq_of_lt (lane_lt hA ht), Nat.mod_eq_of_lt (lane_lt hB ht)] at h2

theorem canon7_zero : C7 0 := ⟨by positivity, fun t _ => by simp [lane]⟩

theorem mat7_zero : mat7 0 = 0 := by
  funext i j
  simp [mat7, ordMat]

theorem eq_zero_iff {X : ℕ} (hX : C7 X) : X = 0 ↔ mat7 X = 0 := by
  constructor
  · rintro rfl
    exact mat7_zero
  · intro h
    exact canon7_inj hX canon7_zero (h.trans mat7_zero.symm)

private def tr7 (t : ℕ) : ℕ := 7 * (t % 7) + t / 7

private theorem tr7_lt : ∀ t < 49, tr7 t < 49 := by decide

private theorem tr7_tr7 : ∀ t < 49, tr7 (tr7 t) = t := by decide

private theorem packL_rec (A : List ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.add acc (Nat.shiftLeft (A.getD t 0)
      (Nat.add (Nat.mul 42 (Nat.mod t 7)) (Nat.mul 6 (Nat.div t 7))))) n =
      ∑ t ∈ Finset.range n, A.getD t 0 * 2 ^ (6 * tr7 t)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← packL_rec A n]
    change Nat.add _ (Nat.shiftLeft (A.getD n 0) (42 * (n % 7) + 6 * (n / 7))) = _
    have hs : ∀ a b : ℕ, Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq
    rw [hs]
    have e : 42 * (n % 7) + 6 * (n / 7) = 6 * tr7 n := by unfold tr7; ring
    rw [e]
    rfl

private theorem packL_eq (A : List ℕ) :
    packL A = pk 6 (7 * 7) (fun t => A.getD (7 * (t % 7) + t / 7) 0) := by
  unfold packL
  rw [packL_rec]
  unfold pk
  refine Finset.sum_nbij' tr7 tr7 (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_) (fun t ht => ?_)
  · exact Finset.mem_range.2 (tr7_lt t (Finset.mem_range.1 ht))
  · exact Finset.mem_range.2 (tr7_lt t (Finset.mem_range.1 ht))
  · exact tr7_tr7 t (Finset.mem_range.1 ht)
  · exact tr7_tr7 t (Finset.mem_range.1 ht)
  · have h := tr7_tr7 t (Finset.mem_range.1 ht)
    change A.getD t 0 * _ = A.getD (tr7 (tr7 t)) 0 * _
    rw [h]

private theorem getD_lt {A : List ℕ} (hA : ∀ x ∈ A, x < 3) (k : ℕ) : A.getD k 0 < 3 := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : A[k]? with _ | x
  · simp
  · exact hA x (List.mem_of_getElem? h)

theorem packL_sound {A : List ℕ} (hA : ∀ x ∈ A, x < 3) :
    C7 (packL A) ∧ mat7 (packL A) = (toMatL 3 7 A).transpose := by
  have hg : ∀ t < 7 * 7, A.getD (7 * (t % 7) + t / 7) 0 < 3 := fun t _ => getD_lt hA _
  have hg' : ∀ t < 7 * 7, A.getD (7 * (t % 7) + t / 7) 0 < 2 ^ 6 :=
    fun t ht => Nat.lt_of_lt_of_le (hg t ht) (by norm_num)
  have hp := packL_eq A
  rw [hp]
  refine ⟨canon_pk hg (by norm_num), ?_⟩
  funext i j
  rw [mat7_apply, lane_pk hg' (idx_lt i.isLt j.isLt)]
  obtain ⟨e1, e2⟩ := dm_eq (d := 7) (i := i.val) j.isLt
  change ((A.getD (7 * ((7 * i.val + j.val) % 7) + (7 * i.val + j.val) / 7) 0 : ℕ) : ZMod 3) =
    ((A.getD (7 * j.val + i.val) 0 : ℕ) : ZMod 3)
  rw [e1, e2]

theorem nOf_sound {M : ℕ} (hM : C7 M) : C7 (nOf M) ∧ mat7 (nOf M) = mat7 M - 1 := by
  set f : ℕ → ℕ := fun t => lane 6 M t + (if t / 7 = t % 7 then 1 else 0) * 2 with hf
  have hf4 : ∀ t < 7 * 7, f t ≤ 4 := by
    intro t ht
    have := lane_lt hM ht
    simp only [hf]
    split <;> omega
  have hsum : Nat.add M TWO7 = pk 6 (7 * 7) f := by
    change M + TWO7 = _
    rw [TWO7_eq, ONE7_eq, pk_mul, pk_lane (by norm_num) hM.1, pk_add]
  have hred : nOf M = pk 6 (7 * 7) (fun t => f t % 3) := by
    unfold nOf
    rw [hsum, L7_eq, H7_eq]
    exact redP_pk (by norm_num) (by norm_num) (fun t ht => by have := hf4 t ht; norm_num; omega)
      (fun t ht => by have := hf4 t ht; norm_num; omega)
  have hg : ∀ t < 7 * 7, f t % 3 < 3 := fun t _ => Nat.mod_lt _ (by norm_num)
  rw [hred]
  refine ⟨canon_pk hg (by norm_num), ?_⟩
  funext i j
  rw [mat7_apply, lane_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) (by norm_num))
    (idx_lt i.isLt j.isLt), Matrix.sub_apply, mat7_apply, Matrix.one_apply]
  obtain ⟨e1, e2⟩ := dm_eq (d := 7) (i := i.val) j.isLt
  simp only [hf, e1, e2, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte, Nat.cast_one, one_mul]
    rw [sub_eq_add_neg]
    congr 1
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, h', ↓reduceIte, Nat.cast_zero, zero_mul, add_zero]
    exact (sub_zero _).symm

theorem cube_sub_one (X : Matrix (Fin 7) (Fin 7) (ZMod 3)) : (X - 1) ^ 3 = X ^ 3 - 1 := by
  have h3 : (3 : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 0 := CharP.ofNat_eq_zero _ 3
  have e : (X - 1) ^ 3 = X ^ 3 - 1 - 3 * (X ^ 2 - X) := by noncomm_ring
  rw [e, h3, zero_mul]
  exact sub_zero _

theorem ord3_sound {M : ℕ} (hM : C7 M) :
    andB (notB (Nat.beq (nOf M) 0)) (Nat.beq (mul7 (mul7 (nOf M) (nOf M)) (nOf M)) 0) = true ↔
      mat7 M ≠ 1 ∧ mat7 M ^ 3 = 1 := by
  obtain ⟨hN, hNm⟩ := nOf_sound hM
  obtain ⟨hN2, hN2m⟩ := mul7_sound hN hN
  obtain ⟨hN3, hN3m⟩ := mul7_sound hN2 hN
  have hb : ∀ a b : ℕ, Nat.beq a b = true ↔ a = b :=
    fun a b => ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩
  have h1 : Nat.beq (nOf M) 0 = true ↔ mat7 M = 1 := by
    rw [hb, eq_zero_iff hN, hNm, sub_eq_zero]
  have h2 : Nat.beq (mul7 (mul7 (nOf M) (nOf M)) (nOf M)) 0 = true ↔ mat7 M ^ 3 = 1 := by
    rw [hb, eq_zero_iff hN3, hN3m, hN2m, hNm, ← pow_two, ← pow_succ,
      cube_sub_one, sub_eq_zero]
  rw [Ne, ← h1, ← h2]
  cases Nat.beq (nOf M) 0 <;> cases Nat.beq (mul7 (mul7 (nOf M) (nOf M)) (nOf M)) 0 <;>
    simp [andB, notB]

end CFSG.KS.Fi24Syl

end
