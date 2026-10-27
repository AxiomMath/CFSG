module

public import CFSG.GH74.Uniqueness.SU.SU9L196a

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG

theorem lemma196 (h191 : Lemma191Stmt) (h194 : Lemma194Stmt) (h195 : Cor195Stmt)
    (h196c : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
      (A B R : Subgroup G), Ctx19 S U M V x z A B R → ∀ a ∈ A, a ∉ U →
        Nonempty (↥(centralizer ({a} : Set G)) ≃*
            alternatingGroup (Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
          (commutator ↥(centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype = U) :
    Lemma196Stmt := by
  intro G _ _ S U M V x z A B R hc a ha haU
  have h194M : pPrimeCore 2 ↥M = ⊥ := (h194 G S U M V x z A B R hc).1
  obtain ⟨-, hN, -⟩ := h195 G S U M V x z A B R hc
  have hTM' := Cfg.T_normal_M hc hN
  exact ⟨L196.lemma196_a h191 hc h194M hTM' ha haU, L196.lemma196_b h191 hc h194M hTM' ha haU,
    h196c G S U M V x z A B R hc a ha haU⟩

end CFSG.GH74.Uniqueness.SU.SU9
