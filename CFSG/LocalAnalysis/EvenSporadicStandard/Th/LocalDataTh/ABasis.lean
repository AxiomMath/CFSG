module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Ladder

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped Matrix

theorem bitZ_val (c i : ℕ) : (bitZ c i).val = c / 2 ^ i % 2 := by
  have h : c.testBit i = decide (c / 2 ^ i % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  have h2 : c / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold bitZ
  by_cases hb : c.testBit i = true
  · rw [ite_eq_left hb]
    rw [hb] at h
    have h1 : c / 2 ^ i % 2 = 1 := by simpa using h.symm
    rw [h1]
    rfl
  · rw [ite_eq_right hb]
    have hb' : c.testBit i = false := by simpa using hb
    rw [hb'] at h
    have h1 : c / 2 ^ i % 2 ≠ 1 := by simpa using h.symm
    have h0 : c / 2 ^ i % 2 = 0 := by omega
    rw [h0]
    rfl

abbrev Vec4 : Type := Fin 4 → ZMod 2

theorem uCodes_mem : ∀ j : Fin 3, uCodes.getD j 0 ∈ UCodes := by decide

section Basis

theorem left_comm_J {u v : J} (h : u * v = v * u) (w : J) : u * (v * w) = v * (u * w) := by
  rw [← mul_assoc, h, mul_assoc]

theorem mul4_mul4_J {a b c d a' b' c' d' : J} (hba : b * a' = a' * b) (hca : c * a' = a' * c)
    (hcb : c * b' = b' * c) (hda : d * a' = a' * d) (hdb : d * b' = b' * d)
    (hdc : d * c' = c' * d) :
    a * b * c * d * (a' * b' * c' * d') = a * a' * (b * b') * (c * c') * (d * d') := by
  simp only [mul_assoc]
  rw [left_comm_J hda, left_comm_J hca, left_comm_J hba, left_comm_J hdb, left_comm_J hcb,
    left_comm_J hdc]

@[expose] def uVec (j : Fin 3) : Vec := codeVec 8 (uCodes.getD j 0)

@[expose] noncomputable def aGen : Fin 4 → J :=
  ![z, nf 0 (uVec 0), nf 0 (uVec 1), nf 0 (uVec 2)]

theorem uVec_mem (j : Fin 3) : uVec j ∈ Ksem 3 := Ksem3_iff.2 ⟨_, uCodes_mem j, rfl⟩

theorem nf_zero_uVec_mem (j : Fin 3) : nf 0 (uVec j) ∈ A := ⟨0, uVec j, uVec_mem j, rfl⟩

theorem aGen_mem (i : Fin 4) : aGen i ∈ A := by
  fin_cases i
  · exact z_mem_A
  · exact nf_zero_uVec_mem 0
  · exact nf_zero_uVec_mem 1
  · exact nf_zero_uVec_mem 2

theorem aGen_mul_self (i : Fin 4) : aGen i * aGen i = 1 := by
  rw [← sq]
  exact A_sq _ (aGen_mem i)

theorem pow_val_add_J (i : Fin 4) (a b : ZMod 2) :
    aGen i ^ (a + b).val = aGen i ^ a.val * aGen i ^ b.val := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases a with rfl | rfl <;>
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h11]
    simp [CFSG.Certificates.ExtraspecialNF.val_one_two, aGen_mul_self i]

@[expose] noncomputable def cA (e : Vec4) : J :=
  aGen 0 ^ (e 0).val * aGen 1 ^ (e 1).val * aGen 2 ^ (e 2).val * aGen 3 ^ (e 3).val

theorem cA_mem_of (H : Subgroup J) (h : ∀ i, aGen i ∈ H) (e : Vec4) : cA e ∈ H := by
  unfold cA
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.pow_mem (h 0) _) (H.pow_mem (h 1) _))
    (H.pow_mem (h 2) _)) (H.pow_mem (h 3) _)

theorem cA_mem (e : Vec4) : cA e ∈ A := cA_mem_of A aGen_mem e

theorem cA_zero : cA 0 = 1 := by simp [cA]

theorem cA_add (e e' : Vec4) : cA (e + e') = cA e * cA e' := by
  have hc : ∀ (i j : Fin 4) (k l : ℕ), aGen i ^ k * aGen j ^ l = aGen j ^ l * aGen i ^ k :=
    fun i j k l => A_comm _ (A.pow_mem (aGen_mem i) k) _ (A.pow_mem (aGen_mem j) l)
  unfold cA
  simp only [Pi.add_apply]
  rw [pow_val_add_J 0,
    pow_val_add_J 1,
    pow_val_add_J 2,
    pow_val_add_J 3]
  exact (mul4_mul4_J (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _) (hc _ _ _ _)
    (hc _ _ _ _)).symm

theorem cA_single (j : Fin 4) : cA (Pi.single j 1) = aGen j := by
  fin_cases j <;> simp [cA, CFSG.Certificates.ExtraspecialNF.val_one_two]

theorem nf_zero_pow (v : Vec) (a : ZMod 2) : nf 0 v ^ a.val = nf 0 (a • v) := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases a with rfl | rfl
  · simp [nf_zero_zero]
  · simp [CFSG.Certificates.ExtraspecialNF.val_one_two]

theorem cA_eq_nf (e : Vec4) :
    ∃ s, cA e = nf s (e 1 • uVec 0 + e 2 • uVec 1 + e 3 • uVec 2) := by
  have h0 : aGen 0 ^ (e 0).val = nf (e 0) 0 := (nf_zero_vec (e 0)).symm
  have h1 : aGen 1 ^ (e 1).val = nf 0 (e 1 • uVec 0) := nf_zero_pow _ _
  have h2 : aGen 2 ^ (e 2).val = nf 0 (e 2 • uVec 1) := nf_zero_pow _ _
  have h3 : aGen 3 ^ (e 3).val = nf 0 (e 3 • uVec 2) := nf_zero_pow _ _
  unfold cA
  rw [h0, h1, h2, h3, nf_mul, nf_mul, nf_mul, zero_add]
  exact ⟨_, rfl⟩

theorem eq_zero_of_cA_eq_one {e : Vec4} (h : cA e = 1) : e = 0 := by
  obtain ⟨s, hs⟩ := cA_eq_nf e
  rw [h, ← nf_zero_zero] at hs
  have hv : (0 : Vec) = e 1 • uVec 0 + e 2 • uVec 1 + e 3 • uVec 2 :=
    congrArg Prod.snd (nf_injective (a₁ := (0, 0)) (a₂ := (s, _)) hs)
  have hind := (ptFacts.2.2.2.2.2.2.2.2.2.2 (fun j => e j.succ) (by
    rw [Fin.sum_univ_three]
    simpa [uVec, add_assoc] using hv.symm))
  have e1 : e 1 = 0 := congrFun hind 0
  have e2 : e 2 = 0 := congrFun hind 1
  have e3 : e 3 = 0 := congrFun hind 2
  have e0 : e 0 = 0 := by
    have hc : cA e = aGen 0 ^ (e 0).val := by
      simp [cA, e1, e2, e3]
    rw [hc] at h
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (e 0) with h0 | h0
    · exact h0
    · exfalso
      rw [h0, CFSG.Certificates.ExtraspecialNF.val_one_two, pow_one] at h
      exact z_ne_one h
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem vec4_add_self (e : Vec4) : e + e = 0 := by
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this _

theorem cA_injective : Function.Injective cA := by
  intro e e' h
  have h1 : cA (e + e') = 1 := by
    rw [cA_add, h, ← cA_add, vec4_add_self, cA_zero]
  have h2 := eq_zero_of_cA_eq_one h1
  funext i
  have := congrFun h2 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  have h3 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h3 _ _ this

@[expose] noncomputable def cAA (e : Vec4) : ↥A := ⟨cA e, cA_mem e⟩

theorem cAA_injective : Function.Injective cAA := by
  intro e e' h
  apply cA_injective
  simpa [cAA] using h

theorem exists_cA {g : J} (hg : g ∈ A) : ∃ e : Vec4, cA e = g := by
  have hf := cAA_injective
  have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [A_card]; norm_num)
  have hcard : Nat.card ↥A ≤ Nat.card Vec4 := by
    rw [A_card]
    simp [Nat.card_eq_fintype_card]
  have hb := hf.bijective_of_nat_card_le hcard
  obtain ⟨e, he⟩ := hb.2 ⟨g, hg⟩
  refine ⟨e, ?_⟩
  simpa [cAA] using congrArg Subtype.val he

theorem map_cA (φ : J → J) (hmul : ∀ a ∈ A, ∀ b ∈ A, φ (a * b) = φ a * φ b) (e : Vec4) :
    φ (cA e) = φ (aGen 0) ^ (e 0).val * φ (aGen 1) ^ (e 1).val * φ (aGen 2) ^ (e 2).val *
      φ (aGen 3) ^ (e 3).val := by
  have h1 : φ 1 = 1 := by simpa using hmul 1 A.one_mem 1 A.one_mem
  have hpow : ∀ (i : Fin 4) (a : ZMod 2), φ (aGen i ^ a.val) = φ (aGen i) ^ a.val := by
    intro i a
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases a with rfl | rfl
    · simp [h1]
    · simp [CFSG.Certificates.ExtraspecialNF.val_one_two]
  have hA : ∀ (i : Fin 4) (a : ZMod 2), aGen i ^ a.val ∈ A := fun i a => A.pow_mem (aGen_mem i) _
  unfold cA
  rw [hmul _ (A.mul_mem (A.mul_mem (hA 0 (e 0)) (hA 1 (e 1))) (hA 2 (e 2))) _ (hA 3 (e 3)),
    hmul _ (A.mul_mem (hA 0 (e 0)) (hA 1 (e 1))) _ (hA 2 (e 2)),
    hmul _ (hA 0 (e 0)) _ (hA 1 (e 1)), hpow, hpow, hpow, hpow]

theorem cA_smul (a : ZMod 2) (w : Vec4) : cA (a • w) = cA w ^ a.val := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases a with rfl | rfl
  · simp [cA_zero]
  · simp [CFSG.Certificates.ExtraspecialNF.val_one_two]

theorem cA_sum (v : Fin 4 → Vec4) (e : Vec4) :
    cA (e 0 • v 0 + e 1 • v 1 + e 2 • v 2 + e 3 • v 3) =
      cA (v 0) ^ (e 0).val * cA (v 1) ^ (e 1).val * cA (v 2) ^ (e 2).val *
        cA (v 3) ^ (e 3).val := by
  rw [cA_add, cA_add, cA_add, cA_smul, cA_smul, cA_smul, cA_smul]

theorem mulVec_eq_sum4 (T : Matrix (Fin 4) (Fin 4) (ZMod 2)) (e : Vec4) :
    T *ᵥ e = e 0 • (T *ᵥ Pi.single 0 1) + e 1 • (T *ᵥ Pi.single 1 1) +
      e 2 • (T *ᵥ Pi.single 2 1) + e 3 • (T *ᵥ Pi.single 3 1) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

@[expose] def Acts (n : J) (T : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ e : Vec4, n * cA e * n⁻¹ = cA (T *ᵥ e)

theorem Acts.of_gens {n : J} {T : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ j : Fin 4, n * aGen j * n⁻¹ = cA (T *ᵥ Pi.single j 1)) : Acts n T := by
  intro e
  have hmul : ∀ a ∈ A, ∀ b ∈ A, (fun g => n * g * n⁻¹) (a * b) =
      (fun g => n * g * n⁻¹) a * (fun g => n * g * n⁻¹) b := by
    intro a _ b _
    simp only
    group
  have key := map_cA (fun g => n * g * n⁻¹) hmul e
  simp only [h] at key
  rw [key, mulVec_eq_sum4 T e]
  exact (cA_sum (fun j => T *ᵥ Pi.single j 1) e).symm

theorem Acts.one : Acts 1 1 := fun e => by simp

theorem Acts.mul {n n' : J} {T T' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : Acts n T)
    (h' : Acts n' T') : Acts (n * n') (T * T') := by
  intro e
  have e1 : n * n' * cA e * (n * n')⁻¹ = n * (n' * cA e * n'⁻¹) * n⁻¹ := by group
  rw [e1, h' e, h, Matrix.mulVec_mulVec]

theorem matOfCols_mulVec_single (cs : List ℕ) (j : Fin 4) :
    matOfCols 4 cs *ᵥ Pi.single j 1 = codeVec 4 (cs.getD j 0) := by
  funext i
  simp [matOfCols, codeVec]

end Basis

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
