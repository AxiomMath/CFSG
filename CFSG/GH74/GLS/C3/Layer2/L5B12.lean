module

public import CFSG.GH74.GLS.C3.Layer2.L5B5
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B5
public import CFSG.GH74.GLS.C3.Layer2.L5B12Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5B12Inputs
public import Certificates.Certificate5045
public import Certificates.Certificate5048
public import Certificates.Certificate5092

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem mg1_cert_chk : S0l.all (fun Y => S0l.all fun E =>
    imp (decide (Y * Y = 1) && decide (E * E = 1) && decide ((Y * E) ^ 4 = 1) &&
      decide ((Y * E) ^ 2 ≠ 1) && decide ((Y * E) ^ 2 ≠ vS0))
      (X0b Y || X0b (vS0 * Y) || X0b E || X0b (vS0 * E))) = true :=
  Certificates.certificate5048.1

theorem mg1_cert
    {Y E : Perm (Fin 9)} (hY : Y ∈ S0) (hE : E ∈ S0) (hY2 : Y * Y = 1)
    (hE2 : E * E = 1) (h4 : (Y * E) ^ 4 = 1) (h2 : (Y * E) ^ 2 ≠ 1) (hv : (Y * E) ^ 2 ≠ vS0) :
    X0b Y = true ∨ X0b (vS0 * Y) = true ∨ X0b E = true ∨ X0b (vS0 * E) = true := by
  have h := mg1_cert_chk
  simp only [List.all_eq_true, imp_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h
  have := h Y (mem_S0l.2 hY) E (mem_S0l.2 hE) ⟨⟨⟨⟨hY2, hE2⟩, h4⟩, h2⟩, hv⟩
  rcases this with ((h1 | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem exists_yE_chk : allT5.all (fun t₀ =>
    imp (decide ((emb 5 t₀ * a0perm 5) * (emb 5 t₀ * a0perm 5) = 1))
      (allT5.any fun mY => Rml.any fun mE =>
        decide (mY * mY = 1) && decide (mY ∉ Rml) && mixb mE &&
        decide (emb 5 mY * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mY) &&
        decide (emb 5 mE * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mE) &&
        decide ((emb 5 mY * emb 5 mE) ^ 2 = vS0))) = true :=
  Certificates.certificate5048.2.1

theorem exists_yE
    {t₀ : Amb 5} (ht₀ : t₀ ∈ T5)
    (hA : (emb 5 t₀ * a0perm 5) * (emb 5 t₀ * a0perm 5) = 1) :
    ∃ mY ∈ T5, ∃ mE ∈ Rm, mY * mY = 1 ∧ mY ∉ Rm ∧ Mixm mE ∧
      emb 5 mY * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mY ∧
      emb 5 mE * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mE ∧
      (emb 5 mY * emb 5 mE) ^ 2 = vS0 := by
  have h := exists_yE_chk
  simp only [List.all_eq_true, List.any_eq_true, imp_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨mY, hmY, mE, hmE, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩ := h t₀ (mem_allT5.2 ht₀) hA
  exact ⟨mY, mem_allT5.1 hmY, mE, mem_Rm.2 hmE, h1, h2, mixb_iff.1 h3, h4, h5, h6⟩

theorem S0_invol_nm_chk :
    S0l.all (fun p => imp (decide (p * p = 1)) (imp (decide (p ≠ 1))
    (decide (numMoved p = 4 ∨ numMoved p = 8)))) = true :=
  Certificates.certificate5048.2.2.1

theorem S0_invol_nm
    {p : Perm (Fin 9)} (hp : p ∈ S0) (hp2 : p * p = 1) (hp1 : p ≠ 1) :
    numMoved p = 4 ∨ numMoved p = 8 := by
  have h := S0_invol_nm_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h p (mem_S0l.2 hp) hp2 hp1

theorem S0_invol_nT_nm8_chk :
    S0l.all (fun p => imp (decide (p * p = 1)) (imp (decide (p ≠ 1))
    (imp (allT5.all fun m => decide (p ≠ emb 5 m)) (decide (numMoved p = 8))))) = true :=
  Certificates.certificate5048.2.2.2

theorem S0_invol_nT_nm8
    {p : Perm (Fin 9)} (hp : p ∈ S0) (hp2 : p * p = 1) (hp1 : p ≠ 1)
    (hpT : ∀ m ∈ T5, p ≠ emb 5 m) : numMoved p = 8 := by
  have h := S0_invol_nT_nm8_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h p (mem_S0l.2 hp) hp2 hp1 (fun m hm => hpT m (mem_allT5.1 hm))

theorem X0b_iff {q : Perm (Fin 9)} :
    X0b q = true ↔ ∃ p ∈ Pml ++ Qml, p ≠ 1 ∧ emb 5 p = q := by
  unfold X0b
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨p, hp, h.1, h.2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, by simp [h1, h2]⟩

end CFSG.GH74.GLS.C3.Layer2.L5
