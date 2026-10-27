module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46TE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDSyl

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {A : SDData t L}

variable [Finite X] {C : A.CaseKD} (S : KDBase A C)

theorem R_le_TE : A.R ≤ S.TE := fun _ hr => by
  rw [mem_TE_iff]
  refine ⟨hr.1, ?_⟩
  obtain ⟨v, c, -, hψ⟩ := ψX_mem_R8 hr
  rw [← hψ, mem_PTE]
  exact dbit8_two_mul c

theorem eq_T_of_le {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hTQ : A.T ≤ Q)
    (hQC : Q ≤ centralizer ({t} : Set X)) : Q = A.T := by
  have h1 := card_T_eq_of_le (A := A) hTQ hQC
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have h2 : (Nat.card Q).factorization 2 = n := by
    rw [hn, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  refine (eq_of_le_of_card_ge hTQ ?_).symm
  rw [h1, h2, hn]

theorem k_ne_t : S.k ≠ t := by
  intro h
  have := ψ_k S
  rw [h, ψX_t] at this
  exact absurd this.symm (by decide)

theorem not_conj_k_tk {g : X} (hgC : g ∈ centralizer ({t} : Set X)) :
    g * S.k * g⁻¹ ≠ t * S.k :=
  S.not_conj_k_tk g hgC

end CFSG.OddStandard.SmallF3.L33.KD.KD46
