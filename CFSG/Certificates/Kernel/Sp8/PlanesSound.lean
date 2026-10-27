module

public import CFSG.Quasithin.H13.L32NMat8
public import Certificates.Data.RudvalisFF81Sp8Cent

public section

namespace CFSG.KC.Sp8Planes

open CFSG.Quasithin.H13.Mat8Cert CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

abbrev M8 := Matrix (Fin 8) (Fin 8) (ZMod 2)

abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 2)

def ix (s : Fin 2) (p : Fin 4) : Fin 8 := ⟨p.val + 4 * s.val, by omega⟩

def pl (i : Fin 8) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩

def sd (i : Fin 8) : Fin 2 := ⟨i.val / 4, by omega⟩

theorem pl_ix (s : Fin 2) (p : Fin 4) : pl (ix s p) = p := by
  ext
  simp only [pl, ix]
  omega

theorem sd_ix (s : Fin 2) (p : Fin 4) : sd (ix s p) = s := by
  ext
  simp only [sd, ix]
  omega

theorem ix_pl_sd (i : Fin 8) : ix (sd i) (pl i) = i := by
  ext
  simp only [sd, ix, pl]
  omega

def e8 : Fin 4 × Fin 2 ≃ Fin 8 where
  toFun x := ix x.2 x.1
  invFun i := (pl i, sd i)
  left_inv x := by simp only [pl_ix, sd_ix]
  right_inv i := ix_pl_sd i

def blk (M : M8) (q p : Fin 4) : M2 := Matrix.of fun s t => M (ix s q) (ix t p)

theorem blk_mul (A B : M8) (q p : Fin 4) : blk (A * B) q p = ∑ r, blk A q r * blk B r p := by
  ext s t
  simp only [blk, Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply]
  rw [← Equiv.sum_comp e8, Fintype.sum_prod_type]
  rfl

theorem blk_ext {A B : M8} (h : ∀ q p, blk A q p = blk B q p) : A = B := by
  ext i j
  have e := congrFun (congrFun (h (pl i) (pl j)) (sd i)) (sd j)
  simpa only [blk, Matrix.of_apply, ix_pl_sd] using e

def bp (a : ZMod 3) : M2 :=
  if a = 0 then !![1, 0; 0, 1] else if a = 1 then !![0, 1; 1, 1] else !![1, 1; 1, 0]

theorem bp_add (a b : ZMod 3) : bp (a + b) = bp a * bp b := by
  revert a b
  decide

theorem bp_rel (X : M2) (hX : X ≠ 0) :
    (∀ a b : ZMod 3, bp a * X = X * bp b → a = b) ∨
      ∀ a b : ZMod 3, bp a * X = X * bp b → a = -b := by
  have key : ∀ x₀ x₁ x₂ x₃ : ZMod 2, !![x₀, x₁; x₂, x₃] ≠ 0 →
      (∀ a b : ZMod 3, bp a * !![x₀, x₁; x₂, x₃] = !![x₀, x₁; x₂, x₃] * bp b → a = b) ∨
        ∀ a b : ZMod 3, bp a * !![x₀, x₁; x₂, x₃] = !![x₀, x₁; x₂, x₃] * bp b → a = -b := by
    decide
  rw [Matrix.eta_fin_two X] at hX ⊢
  exact key _ _ _ _ hX

theorem bp_comm (X : M2) (hX : X ≠ 0) {a : ZMod 3} (ha : a ≠ 0) (h : bp a * X = X * bp a) :
    ∃ c, X = bp c := by
  have key : ∀ x₀ x₁ x₂ x₃ : ZMod 2, !![x₀, x₁; x₂, x₃] ≠ 0 → ∀ a : ZMod 3, a ≠ 0 →
      bp a * !![x₀, x₁; x₂, x₃] = !![x₀, x₁; x₂, x₃] * bp a →
        ∃ c ∈ ([0, 1, 2] : List (ZMod 3)), !![x₀, x₁; x₂, x₃] = bp c := by
    decide
  rw [Matrix.eta_fin_two X] at hX h ⊢
  obtain ⟨c, -, hc⟩ := key _ _ _ _ hX a ha h
  exact ⟨c, hc⟩

def zE (a : Fin 4 → ZMod 3) : M8 :=
  Matrix.of fun i j => if pl i = pl j then bp (a (pl i)) (sd i) (sd j) else 0

theorem blk_zE (a : Fin 4 → ZMod 3) (q p : Fin 4) :
    blk (zE a) q p = if q = p then bp (a q) else 0 := by
  ext s t
  simp only [blk, zE, Matrix.of_apply, pl_ix, sd_ix]
  split_ifs <;> rfl

theorem blk_zE_mul (a : Fin 4 → ZMod 3) (M : M8) (q p : Fin 4) :
    blk (zE a * M) q p = bp (a q) * blk M q p := by
  rw [blk_mul]
  simp only [blk_zE, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem blk_mul_zE (a : Fin 4 → ZMod 3) (M : M8) (q p : Fin 4) :
    blk (M * zE a) q p = blk M q p * bp (a p) := by
  rw [blk_mul]
  simp only [blk_zE, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem zE_add (a b : Fin 4 → ZMod 3) : zE (a + b) = zE a * zE b := by
  refine blk_ext fun q p => ?_
  rw [blk_mul, blk_zE]
  simp only [blk_zE, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  split_ifs with h
  · rw [h, Pi.add_apply, bp_add]
  · rfl

theorem zE_zero : zE 0 = 1 := by decide

theorem zE_nsmul (a : Fin 4 → ZMod 3) (n : ℕ) : zE (n • a) = zE a ^ n := by
  induction n with
  | zero => rw [zero_smul, zE_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, zE_add, ih, pow_succ]

def PlanesOK (E : List (Fin 4 → ZMod 3)) : Prop :=
  (∀ p, ∃ e ∈ E, e p ≠ 0) ∧ ∀ q p, q ≠ p → (∃ e ∈ E, e q ≠ e p) ∧ ∃ e ∈ E, e q ≠ -e p

instance (E : List (Fin 4 → ZMod 3)) : Decidable (PlanesOK E) :=
  inferInstanceAs (Decidable ((∀ p, ∃ e ∈ E, e p ≠ 0) ∧
    ∀ q p, q ≠ p → (∃ e ∈ E, e q ≠ e p) ∧ ∃ e ∈ E, e q ≠ -e p))

theorem eq_zE_of_commute {M : M8} {E : List (Fin 4 → ZMod 3)} (hE : PlanesOK E)
    (hc : ∀ e ∈ E, M * zE e = zE e * M) (hcol : ∀ p : Fin 4, ∃ i, M i (ix 0 p) ≠ 0) :
    ∃ a, M = zE a := by
  have hrel : ∀ e ∈ E, ∀ q p, bp (e q) * blk M q p = blk M q p * bp (e p) := by
    intro e he q p
    rw [← blk_zE_mul, ← blk_mul_zE, hc e he]
  have hoff : ∀ q p, q ≠ p → blk M q p = 0 := by
    intro q p hqp
    by_contra hX
    rcases bp_rel _ hX with h | h
    · obtain ⟨e, he, hne⟩ := (hE.2 q p hqp).1
      exact hne (h _ _ (hrel e he q p))
    · obtain ⟨e, he, hne⟩ := (hE.2 q p hqp).2
      exact hne (h _ _ (hrel e he q p))
  have hdiag : ∀ p, ∃ c, blk M p p = bp c := by
    intro p
    obtain ⟨e, he, hne⟩ := hE.1 p
    refine bp_comm _ (fun h0 => ?_) hne (hrel e he p p)
    obtain ⟨i, hi⟩ := hcol p
    apply hi
    have e1 : M i (ix 0 p) = blk M (pl i) p (sd i) 0 := by
      simp only [blk, Matrix.of_apply, ix_pl_sd]
    rw [e1]
    by_cases hq : pl i = p
    · rw [hq, h0]
      rfl
    · rw [hoff _ _ hq]
      rfl
  choose a ha using hdiag
  refine ⟨a, blk_ext fun q p => ?_⟩
  rw [blk_zE]
  split_ifs with h
  · rw [h]
    exact ha p
  · exact hoff q p h

theorem valid8_of_validS {A : List ℕ} (h : validS A = true) : Valid8 A := by
  simp only [validS, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

theorem mulS_eq_mul8 (A B : List ℕ) (hB : B.length = 8) : mulS A B = mul8 A B := by
  match B, hB with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem dec8_mulS {A B : List ℕ} (hB : validS B = true) : dec8 (mulS A B) = dec8 A * dec8 B := by
  have hl := (valid8_of_validS hB).1
  rw [mulS_eq_mul8 A B hl, dec8_mul8 A B hl]

theorem dec8_mulS_zE {A B : List ℕ} {a b : Fin 4 → ZMod 3} (hB : validS B = true)
    (hA : dec8 A = zE a) (hB' : dec8 B = zE b) : dec8 (mulS A B) = zE (a + b) := by
  rw [dec8_mulS hB, hA, hB', zE_add]

theorem commS_dec8 {x y : List ℕ} (hy : validS y = true) (hx : validS x = true)
    (h : commS x y = true) : dec8 x * dec8 y = dec8 y * dec8 x := by
  rw [commS, beq_iff_eq] at h
  rw [← dec8_mulS hy, ← dec8_mulS hx, h]

theorem validS_of_spS {x : List ℕ} (h : spS x = true) : validS x = true := by
  simp only [spS, Bool.and_eq_true] at h
  exact h.1

theorem spS_col {x : List ℕ} (hx : spS x = true) (p : Fin 4) : ∃ i, dec8 x i (ix 0 p) ≠ 0 := by
  have hb : b4N (x.getD p 0) (x.getD (p + 4) 0) = true := by
    simp only [spS, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hx
    have e := hx.2 p (by omega) (p + 4) (by omega)
    simpa using e
  refine by_contra fun hcon => ?_
  have h0 : vec8 (x.getD p 0) = 0 := by
    funext i
    have e : dec8 x i (ix 0 p) = 0 := by_contra fun h => hcon ⟨i, h⟩
    simpa [dec8, ix] using e
  have e := b4N_spec (x.getD p 0) (x.getD (p + 4) 0)
  rw [hb, h0, b4V, zero_add] at e
  have hq : q4V 0 = 0 := by simp [q4V]
  rw [hq, add_zero] at e
  generalize q4V (vec8 (x.getD (p + 4) 0)) = t at e
  revert t e
  decide

theorem dec8_eq_zE_of_commS {x : List ℕ} (hx : spS x = true) {Y : List (List ℕ)}
    {E : List (Fin 4 → ZMod 3)} (hE : PlanesOK E)
    (hY : ∀ e ∈ E, ∃ y ∈ Y, validS y = true ∧ dec8 y = zE e) (hc : Y.all (commS x) = true) :
    ∃ a, dec8 x = zE a := by
  refine eq_zE_of_commute hE (fun e he => ?_) (spS_col hx)
  obtain ⟨y, hy, hvy, hdy⟩ := hY e he
  rw [← hdy]
  exact commS_dec8 hvy (validS_of_spS hx) (List.all_eq_true.1 hc y hy)

theorem dec8_z0 : dec8 z0S = zE ![1, 0, 0, 0] := by decide

theorem dec8_z1 : dec8 z1S = zE ![0, 1, 0, 0] := by decide

theorem dec8_z2 : dec8 z2S = zE ![0, 0, 1, 0] := by decide

theorem dec8_z3 : dec8 z3S = zE ![0, 0, 0, 1] := by decide

theorem planes_e0 : PlanesOK [![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] := by
  decide

theorem e0c_planes {x : List ℕ} (hx : spS x = true) (hc : e0Gens.all (commS x) = true) :
    ∃ a, dec8 x = zE a := by
  refine dec8_eq_zE_of_commS hx planes_e0 (fun e he => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨z0S, by simp [e0Gens], by decide, dec8_z0⟩
  · exact ⟨z1S, by simp [e0Gens], by decide, dec8_z1⟩
  · exact ⟨z2S, by simp [e0Gens], by decide, dec8_z2⟩
  · exact ⟨z3S, by simp [e0Gens], by decide, dec8_z3⟩

theorem dec8_zz : dec8 zzS = zE ![1, 1, 0, 0] := by
  rw [zzS, dec8_mulS_zE (by decide) dec8_z0 dec8_z1]
  congr 1
  decide

theorem w2S23 {y : List ℕ} (hy : y ∈ w2S 2 3) :
    validS y = true ∧ ∃ α β : ZMod 3, α ≠ 0 ∧ β ≠ 0 ∧ dec8 y = zE ![0, 0, α, β] := by
  have h2 : dec8 (mulS z2S z2S) = zE ![0, 0, 2, 0] := by
    rw [dec8_mulS_zE (by decide) dec8_z2 dec8_z2]
    congr 1
    decide
  have h3 : dec8 (mulS z3S z3S) = zE ![0, 0, 0, 2] := by
    rw [dec8_mulS_zE (by decide) dec8_z3 dec8_z3]
    congr 1
    decide
  have hw : w2S 2 3 = [mulS z2S z3S, mulS z2S (mulS z3S z3S), mulS (mulS z2S z2S) z3S,
      mulS (mulS z2S z2S) (mulS z3S z3S)] := rfl
  rw [hw] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · refine ⟨by decide, 1, 1, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) dec8_z2 dec8_z3]
    congr 1
    decide
  · refine ⟨by decide, 1, 2, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) dec8_z2 h3]
    congr 1
    decide
  · refine ⟨by decide, 2, 1, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) h2 dec8_z3]
    congr 1
    decide
  · refine ⟨by decide, 2, 2, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) h2 h3]
    congr 1
    decide

theorem w2S03 {y : List ℕ} (hy : y ∈ w2S 0 3) :
    validS y = true ∧ ∃ γ δ : ZMod 3, γ ≠ 0 ∧ δ ≠ 0 ∧ dec8 y = zE ![γ, 0, 0, δ] := by
  have h0 : dec8 (mulS z0S z0S) = zE ![2, 0, 0, 0] := by
    rw [dec8_mulS_zE (by decide) dec8_z0 dec8_z0]
    congr 1
    decide
  have h3 : dec8 (mulS z3S z3S) = zE ![0, 0, 0, 2] := by
    rw [dec8_mulS_zE (by decide) dec8_z3 dec8_z3]
    congr 1
    decide
  have hw : w2S 0 3 = [mulS z0S z3S, mulS z0S (mulS z3S z3S), mulS (mulS z0S z0S) z3S,
      mulS (mulS z0S z0S) (mulS z3S z3S)] := rfl
  rw [hw] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · refine ⟨by decide, 1, 1, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) dec8_z0 dec8_z3]
    congr 1
    decide
  · refine ⟨by decide, 1, 2, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) dec8_z0 h3]
    congr 1
    decide
  · refine ⟨by decide, 2, 1, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) h0 dec8_z3]
    congr 1
    decide
  · refine ⟨by decide, 2, 2, by decide, by decide, ?_⟩
    rw [dec8_mulS_zE (by decide) h0 h3]
    congr 1
    decide

theorem planes_hyp : ∀ α β γ δ : ZMod 3, α ≠ 0 → β ≠ 0 → γ ≠ 0 → δ ≠ 0 →
    PlanesOK [![1, 1, 0, 0], ![0, 0, α, β], ![γ, 0, 0, δ]] := by
  decide

theorem hyp_planes {x a b : List ℕ} (hx : spS x = true) (hzz : commS x zzS = true)
    (ha : a ∈ w2S 2 3) (hb : b ∈ w2S 0 3) (hca : commS x a = true) (hcb : commS x b = true) :
    ∃ e, dec8 x = zE e := by
  obtain ⟨hva, α, β, hα, hβ, hda⟩ := w2S23 ha
  obtain ⟨hvb, γ, δ, hγ, hδ, hdb⟩ := w2S03 hb
  refine dec8_eq_zE_of_commS hx (Y := [zzS, a, b]) (planes_hyp α β γ δ hα hβ hγ hδ)
    (fun e he => ?_) (by simp [hzz, hca, hcb])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨zzS, by simp, by decide, dec8_zz⟩
  · exact ⟨a, by simp, hva, hda⟩
  · exact ⟨b, by simp, hvb, hdb⟩

end CFSG.KC.Sp8Planes

end
