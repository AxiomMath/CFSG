module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenUniq
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenTransport

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem exists_wreathPair_of_caseIII_root (h : ExactShape z L n)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) {S₀ : Finset (Fin n)} (hS₀ : S₀.card = 3)
    (hIII : CaseIIIAt e z S₀) : ∃ H : Subgroup G, WreathPair L z n H :=
  exists_wreathPair_of_caseIII h e hn fun _ hS =>
    caseIIIAt_transport h e (by omega) hS₀ hS hIII

theorem wreath_unique_of_caseIII_root (h : ExactShape z L n)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) {S₀ : Finset (Fin n)} (hS₀ : S₀.card = 3)
    (hIII : CaseIIIAt e z S₀) {H₁ H₂ : Subgroup G} (h₁ : WreathPair L z n H₁)
    (h₂ : WreathPair L z n H₂) :
    H₂ = H₁ ∨ H₂ = H₁.map (MulAut.conj z).toMonoidHom :=
  wreath_unique (e := e) h hn (fun _ hS => caseIIIAt_transport h e (by omega) hS₀ hS hIII) h₁ h₂

end Main

section Stmts

open CFSG.OddStandard.AltStdBal

theorem stageMRootStmt :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ) (Q : Subgroup G) (z : G)
      (_ : Setting G L n) (_ : Cyc L Q z), Nat.card Q = 2 →
      ∀ e : L ≃* alternatingGroup (Fin n), 12 ≤ n →
        ∀ S₀ : Finset (Fin n), S₀.card = 3 → CaseIIIAt e z S₀ →
          ∃ H : Subgroup G, WreathPair L z n H := by
  intro G _ _ L n Q z hSet d hQ2 e hn S₀ hS₀ hIII
  exact exists_wreathPair_of_caseIII_root (exactShape_of_setting hSet d hQ2) e (by omega) hS₀ hIII

end Stmts

end CFSG.OddStandard.AltStdSec
