module

public import Certificates.Data.Kernel.FiveStdKDiag2
public import CFSG.Certificates.Kernel.FiveStdKDiagSound

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd

theorem memA_decL {A nA : Nat} {x : E} (h : memA A nA (codeE x) = true) : x ∈ decL (f20 A) nA := by
  obtain ⟨i, hi, he⟩ := memA_iff.1 h
  exact mem_decL.2 ⟨i, hi, by rw [he, decE_codeE]⟩

theorem not_beq_true {a b : Nat} (h : a ≠ b) : (!Nat.beq a b) = true := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem dv_sound {A nA B Mc : Nat} (h : dvOK A nA B Mc = true)
    (hB : ∀ k < Mc, validK (f20 B k) = true) :
    ∀ τ ∈ decL (f20 B) Mc, mulE τ τ = oneE → τ ≠ oneE → τ ≠ zE → ∀ b ∈ decL (f20 B) Mc,
      ∃ v ∈ [oneE, zE, τ, mulE zE τ], mulE b (invE v) ∈ decL (f20 A) nA := by
  intro τ hτ hττ h1 hz b hb
  obtain ⟨k, hk, rfl⟩ := mem_decL.1 hτ
  obtain ⟨j, hj, rfl⟩ := mem_decL.1 hb
  have hck := codeE_decE (validK_lt (hB k hk))
  have hcj := codeE_decE (validK_lt (hB j hj))
  have hpt := (allN_iff _ _).1 h k hk
  unfold dvPt at hpt
  rw [letB_eq] at hpt
  have hcond : andB (Nat.beq (mulK (f20 B k) (f20 B k)) oneK)
      (andB (!Nat.beq (f20 B k) oneK) (!Nat.beq (f20 B k) zK)) = true := by
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨?_, not_beq_true fun e => h1 ?_, not_beq_true fun e => hz ?_⟩
    · rw [← hck, ← codeE_mulE, hττ, codeE_oneE]
      exact Nat.beq_refl _
    · exact codeE_eq_oneK.1 (hck.trans e)
    · exact codeE_injective (hck.trans (e.trans codeE_zE.symm))
  have h2 := (ifB_true hpt).1 hcond
  rw [letB_eq] at h2
  have h3 := (allN_iff _ _).1 h2 j hj
  unfold dvIn at h3
  rw [orB_eq, orB_eq, orB_eq, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h3
  have hv : ∀ v : E, memA A nA (mulK (f20 B j) (invK (codeE v))) = true →
      mulE (decE (f20 B j)) (invE v) ∈ decL (f20 A) nA := by
    intro v hm
    apply memA_decL
    rw [codeE_mulE, codeE_invE, hcj]
    exact hm
  rcases h3 with h3 | h3 | h3 | h3
  · refine ⟨oneE, List.mem_cons_self .., hv oneE ?_⟩
    rw [codeE_oneE]
    exact h3
  · refine ⟨zE, by simp, hv zE ?_⟩
    rw [codeE_zE]
    exact h3
  · refine ⟨decE (f20 B k), by simp, hv _ ?_⟩
    rw [hck]
    exact h3
  · refine ⟨mulE zE (decE (f20 B k)), by simp, hv _ ?_⟩
    rw [codeE_mulE, codeE_zE, hck]
    exact h3

end CFSG.KC.FiveStdK

end
