
module

public import CFSG.GH74.GLS.C3.Prop121.ModelFiveBase

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveInputs
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveInputs
public import Certificates.Certificate5091

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem elt_mem :
    T5b e1 = true ∧ T5b e2 = true ∧ T5b f1 = true ∧ T5b f2 = true ∧
    T5b (e1 * f1) = true ∧ T5b (e2 * f1) = true ∧ T5b (e1 * e2) = true ∧
    T5b (f1 * f2) = true :=
  Certificates.certificate5091.2.1

theorem elt_invol :
    e1 * e1 = 1 ∧ e2 * e2 = 1 ∧ (e1 * f1) * (e1 * f1) = 1 ∧ (e2 * f1) * (e2 * f1) = 1 ∧
    (e1 * e2) * (e1 * e2) = 1 :=
  Certificates.certificate5091.2.2.1

theorem f1_sq : f1 * f1 = 1 :=
  Certificates.certificate5091.2.2.2.1

theorem elt_ne :
    e1 ≠ 1 ∧ e2 ≠ 1 ∧ e1 * f1 ≠ 1 ∧ e2 * f1 ≠ 1 ∧ e1 * e2 ≠ 1 :=
  Certificates.certificate5091.2.2.2.2.1

theorem elt_ne' :
    f1 ≠ 1 ∧ f2 ≠ 1 ∧ f1 * f2 ≠ 1 ∧ e1 ≠ f1 ∧ e1 ≠ e2 :=
  Certificates.certificate5091.2.2.2.2.2.1

theorem elt_ne'' : e1 ≠ f2 ∧ f1 ≠ f2 :=
  Certificates.certificate5091.2.2.2.2.2.2.1

theorem elt_misc :
    f2 * e2 = e2 * f2 ∧ f2 * (e1 * e2) = (e1 * e2) * f2 ∧
    f1.1 = 1 ∧ f2.1 = 1 ∧ (f1 * f2).1 = 1 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.1

theorem elt_misc' : e1.2 = 1 ∧ e2.2 = 1 ∧ (e1 * e2).2 = 1 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.1

theorem conj_e1_e2 :
    (((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).2 * x4 =
        x4 * ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).2 ∧
      sign ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).1 =
        sign ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).2) ∧
    ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5) * e1 *
        ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5)⁻¹ = e2 ∧
    ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5) * (e1 * f1) *
      ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5)⁻¹ = e2 * f1 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.1

theorem conj_e1_e12 :
    (((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).2 * x4 =
        x4 * ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).2 ∧
      sign ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).1 =
        sign ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).2) ∧
    ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5) * e1 *
        ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5)⁻¹ = e1 * e2 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.1

theorem e1_central : ∀ t ∈ allT5, e1 * t = t * e1 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.1

theorem center_T5 : ∀ u ∈ allT5, (∀ s ∈ allT5, u * s = s * u) →
    u = 1 ∨ u = e1 ∨ u = f1 ∨ u = e1 * f1 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Q0_T5 :
    ∀ q ∈ allT5, q.1 = 1 → q = 1 ∨ q = f1 ∨ q = f2 ∨ q = f1 * f2 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem W1 :
    ∀ u₁ ∈ [e1, e1 * f1], ∀ w ∈ allT5, W1P u₁ w :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem U1 :
    ∀ w ∈ [e2, e1 * e2], ∀ u ∈ allT5, U1P w u :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem a0_conj_Q0 :
    ∀ q' ∈ [1, f1, f2, f1 * f2], ∃ v' ∈ [1, e1, e2, e1 * e2],
    a0perm 5 * emb 5 q' * (a0perm 5)⁻¹ = emb 5 v' :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem V1_facts :
    ∀ v' ∈ [1, e1, e2, e1 * e2], T5b v' = true ∧ v'.2 = 1 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem model_five
    (b : Amb 5 → Amb 5) (hb : IsAutOn b) (H1 : b f1 = f1)
    (H2 : ∀ w ∈ T5, ∀ w' ∈ T5, w * w = 1 → w ≠ 1 → w' * w' = 1 → w' ≠ 1 →
      (∃ g ∈ Fgrp 5, g * w * g⁻¹ = w') → nmE (b w) = nmE (b w'))
    (H3 : ∀ q ∈ T5, q.1 = 1 → q ≠ 1 → nmE (b q) = 4) :
    ∀ q ∈ T5, q.1 = 1 → ∃ v ∈ T5, v.2 = 1 ∧
      a0perm 5 * emb 5 (b q) * (a0perm 5)⁻¹ = emb 5 (b v) := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := elt_mem
  have he1 : e1 ∈ T5 := mem_T5_of_b m1
  have he2 : e2 ∈ T5 := mem_T5_of_b m2
  have hf1 : f1 ∈ T5 := mem_T5_of_b m3
  have hf2 : f2 ∈ T5 := mem_T5_of_b m4
  have he1f1 : e1 * f1 ∈ T5 := mem_T5_of_b m5
  have he2f1 : e2 * f1 ∈ T5 := mem_T5_of_b m6
  have he12 : e1 * e2 ∈ T5 := mem_T5_of_b m7
  have hf12 : f1 * f2 ∈ T5 := mem_T5_of_b m8
  obtain ⟨i1, i2, i3, i4, i5⟩ := elt_invol
  obtain ⟨n1, n2, n3, n4, n5⟩ := elt_ne
  obtain ⟨n6, n7, n8, n9, n10⟩ := elt_ne'
  obtain ⟨n11, n12⟩ := elt_ne''
  obtain ⟨c1, c2, c3, c4, c5⟩ := elt_misc
  have hinj : ∀ {p q : Amb 5}, p ∈ T5 → q ∈ T5 → b p = b q → p = q :=
    fun hp hq h => hb.inj _ hp _ hq h
  have hb1 : b 1 = 1 := hb.one
  have hcen : ∀ s ∈ T5, b e1 * s = s * b e1 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hb.surj s hs
    rw [← hb.mul e1 he1 t ht, ← hb.mul t ht e1 he1]
    congr 1
    exact e1_central t (mem_allT5.2 ht)
  have hbe1 : b e1 = e1 ∨ b e1 = e1 * f1 := by
    have hbe1T : b e1 ∈ T5 := hb.mem _ he1
    rcases center_T5 (b e1) (mem_allT5.2 hbe1T) (fun s hs => hcen s (mem_allT5.1 hs)) with
      h | h | h | h
    · exact absurd (hinj he1 (one_mem _) (h.trans hb1.symm)) n1
    · exact Or.inl h
    · exact absurd (hinj he1 hf1 (h.trans H1.symm)) n9
    · exact Or.inr h
  have hbmul1 : ∀ p ∈ T5, b (p * f1) = b p * f1 := fun p hp => by
    rw [hb.mul p hp f1 hf1, H1]
  have h2a : nmE (b e1) = nmE (b e2) := by
    obtain ⟨g1, g2, g3⟩ := conj_e1_e2
    exact H2 e1 he1 e2 he2 i1 n1 i2 n2 ⟨_, mem_Fgrp5.2 g1, g2⟩
  have h2b : nmE (b e1 * f1) = nmE (b e2 * f1) := by
    obtain ⟨g1, g2, g3⟩ := conj_e1_e2
    have := H2 (e1 * f1) he1f1 (e2 * f1) he2f1 i3 n3 i4 n4 ⟨_, mem_Fgrp5.2 g1, g3⟩
    rwa [hbmul1 e1 he1, hbmul1 e2 he2] at this
  have h2c : nmE (b e1) = nmE (b e1 * b e2) := by
    obtain ⟨g1, g2⟩ := conj_e1_e12
    have := H2 e1 he1 (e1 * e2) he12 i1 n1 i5 n5 ⟨_, mem_Fgrp5.2 g1, g2⟩
    rwa [hb.mul e1 he1 e2 he2] at this
  have hW := W1 (b e1) (by rcases hbe1 with h | h <;> simp [h]) (b e2)
    (mem_allT5.2 (hb.mem _ he2))
  obtain ⟨hbe1', hbe2⟩ := hW ⟨h2a, h2b, h2c⟩
  have hne1 : b f2 ≠ 1 := fun h => n7 (hinj hf2 (one_mem _) (h.trans hb1.symm))
  have hne2 : b f2 ≠ f1 := fun h => n12 (hinj hf2 hf1 (h.trans H1.symm)).symm
  have h4a : nmE (b f2) = 4 := H3 f2 hf2 c4 n7
  have h4b : nmE (f1 * b f2) = 4 := by
    have := H3 (f1 * f2) hf12 c5 n8
    rwa [hb.mul f1 hf1 f2 hf2, H1] at this
  have hcomm : b f2 * b e2 = b e2 * b f2 := by
    rw [← hb.mul f2 hf2 e2 he2, ← hb.mul e2 he2 f2 hf2, c1]
  have hU := U1 (b e2) (by rcases hbe2 with h | h <;> simp [h]) (b f2)
    (mem_allT5.2 (hb.mem _ hf2))
  have hbf2 : b f2 = f2 ∨ b f2 = f1 * f2 := hU ⟨hne1, hne2, h4a, h4b, hcomm⟩
  have hQ : ∀ q' ∈ [1, f1, f2, f1 * f2], ∃ v' ∈ [1, e1, e2, e1 * e2],
      a0perm 5 * emb 5 q' * (a0perm 5)⁻¹ = emb 5 v' := a0_conj_Q0
  have hVs : ∀ v' ∈ [1, e1, e2, e1 * e2], ∃ v ∈ [1, e1, e2, e1 * e2], b v = v' := by
    intro v' hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hbe2 with h | h
    · refine ⟨v', ?_, ?_⟩
      · simpa using hv'
      · rcases hv' with rfl | rfl | rfl | rfl
        · exact hb1
        · exact hbe1'
        · exact h
        · rw [hb.mul e1 he1 e2 he2, hbe1', h]
    · rcases hv' with rfl | rfl | rfl | rfl
      · exact ⟨1, by simp, hb1⟩
      · exact ⟨e1, by simp, hbe1'⟩
      · refine ⟨e1 * e2, by simp, ?_⟩
        rw [hb.mul e1 he1 e2 he2, hbe1', h, ← mul_assoc, i1, one_mul]
      · exact ⟨e2, by simp, h⟩
  intro q hq hq1
  have hbq : b q ∈ [1, f1, f2, f1 * f2] := by
    rcases Q0_T5 q (mem_allT5.2 hq) hq1 with rfl | rfl | rfl | rfl
    · simp [hb1]
    · simp [H1]
    · rcases hbf2 with h | h <;> simp [h]
    · rw [hb.mul f1 hf1 f2 hf2, H1]
      rcases hbf2 with h | h
      · simp [h]
      · simp only [h, ← mul_assoc, f1_sq, one_mul]
        simp
  obtain ⟨v', hv', hconj⟩ := hQ (b q) hbq
  obtain ⟨v, hv, hbv⟩ := hVs v' hv'
  have hvf := V1_facts v hv
  exact ⟨v, mem_T5_of_b hvf.1, hvf.2, by rw [hconj, hbv]⟩

theorem nmE_f1 : nmE f1 = 4 :=
  Certificates.certificate5091.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem f1_mem_T5 : f1 ∈ T5 := mem_T5_of_b elt_mem.2.2.1

end CFSG.GH74.GLS.C3.Prop121
