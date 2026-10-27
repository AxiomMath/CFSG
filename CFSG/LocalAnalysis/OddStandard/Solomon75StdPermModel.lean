module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] {n : ℕ} {A : Subgroup X}

@[expose] noncomputable def AhatModel.toK (M : AhatModel X n A) : ↥A →* M.K :=
  (M.e : ↥A ⧸ pPrimeCore 2 ↥A →* M.K).comp (QuotientGroup.mk' (pPrimeCore 2 ↥A))

theorem AhatModel.toK_surjective (M : AhatModel X n A) : Function.Surjective M.toK := fun k => by
  obtain ⟨a, ha⟩ := M.surj_mk k
  exact ⟨a, ha⟩

theorem AhatModel.toK_injective (M : AhatModel X n A) (hA : pPrimeCore 2 ↥A = ⊥) :
    Function.Injective M.toK := by
  intro a b hab
  have h1 : (QuotientGroup.mk a : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk b :=
    M.e.injective hab
  rw [QuotientGroup.eq, hA, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.1 h1

@[expose] noncomputable def AhatModel.toKEquiv (M : AhatModel X n A) (hA : pPrimeCore 2 ↥A = ⊥) :
    ↥A ≃* M.K :=
  MulEquiv.ofBijective M.toK ⟨M.toK_injective hA, M.toK_surjective⟩

theorem AhatModel.autOf_toK (M : AhatModel X n A) {c : X} (hc : c ∈ normalizer (A : Set X))
    (a : ↥A) : M.autOf c hc (M.toK a) = M.toK (conjAut hc a) :=
  M.autOf_mk hc a

end CFSG.OddStandard.Solomon75
