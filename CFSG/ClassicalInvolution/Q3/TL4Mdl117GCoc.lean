module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Vec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
open CFSG.ComponentClassification.PresentationLocal

variable {n : ℕ}

theorem sq_vec (x : Wr n) (i : Fin n) : (x ^ 2).vec i = x.vec i + x.vec (x.perm.symm i) := by
  rw [sq, mul_vec]

theorem cube_vec (x : Wr n) (i : Fin n) :
    (x ^ 3).vec i = x.vec i + x.vec (x.perm.symm i) + x.vec (x.perm.symm (x.perm.symm i)) := by
  rw [pow_three, mul_vec, mul_vec, add_assoc]

theorem ofPerm_mul_ofVec (σ : Equiv.Perm (Fin n)) (w : Fin n → ZMod 2) :
    ofPerm σ * ofVec w = ⟨fun i => w (σ.symm i), σ⟩ :=
  Wr.ext (funext fun i => by show 0 + w (σ.symm i) = w (σ.symm i); rw [zero_add])
    (by show σ * 1 = σ; rw [mul_one])

theorem allOnes_eq_ofVec : allOnes n = ofVec (fun _ => 1) := rfl

theorem eq_one_or_allOnes_of_mkQ {x : Wr n} (h : mkQ n x = 1) : x = 1 ∨ x = allOnes n :=
  mem_piSub.mp ((QuotientGroup.eq_one_iff x).mp h)

abbrev carmZero (k : CarmichaelIndex n) : Fin n := ⟨0, by have := k.two_lt; omega⟩

abbrev carmOne (k : CarmichaelIndex n) : Fin n := ⟨1, by have := k.two_lt; omega⟩

theorem carmichaelPerm_symm_zero (k : CarmichaelIndex n) :
    (carmichaelPerm k).symm (carmZero k) = k.1 := by
  rw [Equiv.symm_apply_eq, carmichaelPerm_apply]
  have hk := k.2
  simp [show (k.1 : ℕ) ≠ 0 by omega, show (k.1 : ℕ) ≠ 1 by omega]

theorem carmichaelPerm_symm_one (k : CarmichaelIndex n) :
    (carmichaelPerm k).symm (carmOne k) = carmZero k := by
  rw [Equiv.symm_apply_eq, carmichaelPerm_apply]
  simp

theorem carmichaelPerm_symm_self (k : CarmichaelIndex n) :
    (carmichaelPerm k).symm k.1 = carmOne k := by
  rw [Equiv.symm_apply_eq, carmichaelPerm_apply]
  simp

theorem carmichaelPerm_symm_of_ne (k : CarmichaelIndex n) {x : Fin n} (h0 : (x : ℕ) ≠ 0)
    (h1 : (x : ℕ) ≠ 1) (hk : x ≠ k.1) : (carmichaelPerm k).symm x = x := by
  rw [Equiv.symm_apply_eq, carmichaelPerm_apply]
  simp [h0, h1, hk]

@[expose] def NormAt (k : CarmichaelIndex n) (w : Fin n → ZMod 2) : Prop :=
  (∀ x : Fin n, (x : ℕ) ≠ 0 → (x : ℕ) ≠ 1 → x ≠ k.1 → w x = 0) ∧
    w k.1 = w (carmZero k) + w (carmOne k)

theorem zmod_two_cube_zero : ∀ a b c : ZMod 2, a + b + c = 0 → a = c + b := by decide

theorem zmod_two_cube_one : ∀ a b c : ZMod 2, a + b + c = 1 → a + 1 = (c + 1) + (b + 1) := by
  decide

theorem zmod_two_pair : ∀ a b c d : ZMod 2, a = b + c → a + (c + d) = 0 → b = d := by decide

theorem exists_norm_of_cube (k : CarmichaelIndex n) {w : Fin n → ZMod 2}
    (h : mkQ n ((ofPerm (carmichaelPerm k) * ofVec w) ^ 3) = 1) :
    ∃ w' : Fin n → ZMod 2, NormAt k w' ∧
      mkQ n (ofPerm (carmichaelPerm k) * ofVec w') =
        mkQ n (ofPerm (carmichaelPerm k) * ofVec w) := by
  set t := carmichaelPerm k with ht
  have hv : ∀ y, ((ofPerm t * ofVec w) ^ 3).vec y =
      w (t.symm y) + w (t.symm (t.symm y)) + w (t.symm (t.symm (t.symm y))) := by
    intro y
    rw [cube_vec, ofPerm_mul_ofVec]
  have hoff : ∀ y : Fin n, (y : ℕ) ≠ 0 → (y : ℕ) ≠ 1 → y ≠ k.1 →
      ((ofPerm t * ofVec w) ^ 3).vec y = w y := by
    intro y h0 h1 hk
    rw [hv, carmichaelPerm_symm_of_ne k h0 h1 hk, carmichaelPerm_symm_of_ne k h0 h1 hk,
      carmichaelPerm_symm_of_ne k h0 h1 hk, zmod_two_add_self, zero_add]
  have hzero : ((ofPerm t * ofVec w) ^ 3).vec (carmZero k) =
      w k.1 + w (carmOne k) + w (carmZero k) := by
    rw [hv, carmichaelPerm_symm_zero, carmichaelPerm_symm_self, carmichaelPerm_symm_one]
  have hpi : mkQ n (allOnes n) = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_piSub.mpr (Or.inr rfl))
  rcases eq_one_or_allOnes_of_mkQ h with h1 | h1
  · refine ⟨w, ⟨fun y h0 h1' hk => ?_, ?_⟩, rfl⟩
    · rw [← hoff y h0 h1' hk, h1]
      rfl
    · have h2 : w k.1 + w (carmOne k) + w (carmZero k) = 0 := by rw [← hzero, h1]; rfl
      exact zmod_two_cube_zero _ _ _ h2
  · refine ⟨w + fun _ => 1, ⟨fun y h0 h1' hk => ?_, ?_⟩, ?_⟩
    · have h2 : w y = 1 := by rw [← hoff y h0 h1' hk, h1]; rfl
      show w y + 1 = 0
      rw [h2]
      decide
    · have h2 : w k.1 + w (carmOne k) + w (carmZero k) = 1 := by rw [← hzero, h1]; rfl
      exact zmod_two_cube_one _ _ _ h2
    · rw [ofVec_add, ← allOnes_eq_ofVec, ← mul_assoc, map_mul, hpi, mul_one]

theorem eq_at_zero_of_sq (hn : 5 ≤ n) {k l : CarmichaelIndex n} (hkl : k ≠ l)
    {w w' : Fin n → ZMod 2} (hw : NormAt k w) (hw' : NormAt l w')
    (h : mkQ n ((ofPerm (carmichaelPerm k) * ofVec w *
      (ofPerm (carmichaelPerm l) * ofVec w')) ^ 2) = 1) :
    w (carmZero k) = w' (carmZero l) := by
  classical
  have hk2 := k.2
  have hl2 := l.2
  have hkl' : k.1 ≠ l.1 := fun e => hkl (Subtype.ext e)
  set y := ofPerm (carmichaelPerm k) * ofVec w * (ofPerm (carmichaelPerm l) * ofVec w') with hy
  have hyv : ∀ z, y.vec z = w ((carmichaelPerm k).symm z) +
      w' ((carmichaelPerm l).symm ((carmichaelPerm k).symm z)) := by
    intro z
    rw [hy, ofPerm_mul_ofVec, ofPerm_mul_ofVec, mul_vec]
  have hyp : y.perm = carmichaelPerm k * carmichaelPerm l := by
    rw [hy, mul_perm, ofPerm_mul_ofVec, ofPerm_mul_ofVec]
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({carmZero k, carmOne k, k.1, l.1} : Finset (Fin n))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (Finset.card_le_four) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  obtain ⟨hm0, hm1, hmk, hml⟩ := hm
  have hm0' : (m : ℕ) ≠ 0 := fun e => hm0 (Fin.ext e)
  have hm1' : (m : ℕ) ≠ 1 := fun e => hm1 (Fin.ext e)
  have hym : y.vec m = 0 := by
    rw [hyv, carmichaelPerm_symm_of_ne k hm0' hm1' hmk, carmichaelPerm_symm_of_ne l hm0' hm1' hml,
      hw.1 m hm0' hm1' hmk, hw'.1 m hm0' hm1' hml, add_zero]
  have hsymm : ∀ z, y.perm.symm z = (carmichaelPerm l).symm ((carmichaelPerm k).symm z) := by
    intro z
    rw [hyp, Equiv.Perm.mul_def, Equiv.symm_trans_apply]
  have hy2m : (y ^ 2).vec m = 0 := by
    rw [sq_vec, hsymm, carmichaelPerm_symm_of_ne k hm0' hm1' hmk,
      carmichaelPerm_symm_of_ne l hm0' hm1' hml, hym, add_zero]
  rcases eq_one_or_allOnes_of_mkQ h with h1 | h1
  ·
    have hk0 : (k.1 : ℕ) ≠ 0 := by omega
    have hk1 : (k.1 : ℕ) ≠ 1 := by omega
    have e1 : (y ^ 2).vec (carmZero k) = y.vec (carmZero k) + y.vec k.1 := by
      rw [sq_vec, hsymm, carmichaelPerm_symm_zero, carmichaelPerm_symm_of_ne l hk0 hk1 hkl']
    have e2 : y.vec (carmZero k) = w k.1 := by
      rw [hyv, carmichaelPerm_symm_zero, carmichaelPerm_symm_of_ne l hk0 hk1 hkl',
        hw'.1 k.1 hk0 hk1 hkl', add_zero]
    have e3 : y.vec k.1 = w (carmOne k) + w' (carmZero k) := by
      rw [hyv, carmichaelPerm_symm_self, show carmOne k = carmOne l from rfl,
        carmichaelPerm_symm_one]
    have e4 : (y ^ 2).vec (carmZero k) = 0 := by rw [h1]; rfl
    have h0 : w k.1 + (w (carmOne k) + w' (carmZero k)) = 0 := by rw [← e2, ← e3, ← e1, e4]
    exact zmod_two_pair _ _ _ _ hw.2 h0
  · exfalso
    have h2 : (y ^ 2).vec m = 1 := by rw [h1]; rfl
    rw [hy2m] at h2
    exact absurd h2 (by decide)

@[expose] def uVec (c : ZMod 2) (w : CarmichaelIndex n → Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun y => if h : 2 ≤ (y : ℕ) then c + w ⟨y, h⟩ ⟨1, by omega⟩ else if (y : ℕ) = 1 then c else 0

theorem uVec_zero (c : ZMod 2) (w : CarmichaelIndex n → Fin n → ZMod 2) (k : CarmichaelIndex n) :
    uVec c w (carmZero k) = 0 := by
  simp [uVec]

theorem uVec_one (c : ZMod 2) (w : CarmichaelIndex n → Fin n → ZMod 2) (k : CarmichaelIndex n) :
    uVec c w (carmOne k) = c := by
  simp [uVec]

theorem uVec_idx (c : ZMod 2) (w : CarmichaelIndex n → Fin n → ZMod 2) (k : CarmichaelIndex n) :
    uVec c w k.1 = c + w k (carmOne k) := by
  simp only [uVec, k.2, dite_true]

theorem conj_uVec {c : ZMod 2} {w : CarmichaelIndex n → Fin n → ZMod 2}
    (hw : ∀ k, NormAt k (w k)) (hc : ∀ k, w k (carmZero k) = c) (k : CarmichaelIndex n) :
    ofVec (uVec c w) * ofPerm (carmichaelPerm k) * (ofVec (uVec c w))⁻¹ =
      ofPerm (carmichaelPerm k) * ofVec (w k) := by
  have hconj : ∀ (u : Fin n → ZMod 2) (σ : Equiv.Perm (Fin n)),
      ofVec u * ofPerm σ * (ofVec u)⁻¹ = ⟨fun y => u y + u (σ.symm y), σ⟩ := by
    intro u σ
    refine Wr.ext (funext fun y => ?_) ?_
    · rw [mul_vec, mul_vec, inv_vec]
      show u y + 0 + u ((1 : Equiv.Perm (Fin n)) ((1 * σ).symm y)) = u y + u (σ.symm y)
      rw [add_zero, one_mul, Equiv.Perm.one_apply]
    · show 1 * σ * (1 : Equiv.Perm (Fin n))⁻¹ = σ
      rw [one_mul, inv_one, mul_one]
  rw [hconj, ofPerm_mul_ofVec]
  congr 1
  funext y
  by_cases h0 : (y : ℕ) = 0
  · obtain rfl : y = carmZero k := Fin.ext h0
    rw [carmichaelPerm_symm_zero, (hw k).2, hc k, uVec_zero, uVec_idx, zero_add]
  by_cases h1 : (y : ℕ) = 1
  · obtain rfl : y = carmOne k := Fin.ext h1
    rw [carmichaelPerm_symm_one, hc k, uVec_one, uVec_zero, add_zero]
  by_cases hyk : y = k.1
  · subst hyk
    rw [carmichaelPerm_symm_self, uVec_idx, uVec_one, add_comm c, add_assoc, zmod_two_add_self,
      add_zero]
  · rw [carmichaelPerm_symm_of_ne k h0 h1 hyk, zmod_two_add_self, (hw k).1 y h0 h1 hyk]

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
