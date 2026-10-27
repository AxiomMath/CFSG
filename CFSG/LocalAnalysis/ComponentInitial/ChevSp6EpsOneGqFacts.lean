
module

public import Certificates.Certificate3360

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

theorem card_Gq (u : Bool) : Nat.card (Gq u) = if u then 362880 else 56448 :=
  (Certificates.certificate3360 u).1

theorem ker_of_mem {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) (hu : u = true)
    (hB : bOf u (tupleOf σ) = idE) :
    tupleOf σ = idT ∨ tupleOf σ = omT ∨ tupleOf σ = compT omT omT :=
  (Certificates.certificate3360 u).2.2.1 σ hσ hu hB

theorem conj_of_mem {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u)
    (hinv : isInvT (tupleOf σ) = true) (hp : presT u (tupleOf σ) = true) :
    ∃ w, (∀ a ∈ w, a < 3) ∧ ∃ k, k < (killReps u).length ∧
      compT (evalW (tupleOf σ) w) (tupleOf σ) =
        compT ((killReps u).getD k ([], [])).1 (evalW (tupleOf σ) w) :=
  (Certificates.certificate3360 u).2.2.2.1 σ hσ hinv hp

theorem killRep_facts (u : Bool) {k : ℕ} (hk : k < (killReps u).length) :
    validT u ((killReps u).getD k ([], [])).1 = true ∧
      ∃ c, validCert u ((killReps u).getD k ([], [])).1 c = true :=
  (Certificates.certificate3360 u).2.2.2.2 k hk

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
