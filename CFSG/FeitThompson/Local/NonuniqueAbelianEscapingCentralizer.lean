module

public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
import CFSG.FeitThompson.Local.CentralizerControlUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {A B M : Subgroup G}

theorem exists_escaping_centralizer_of_isMulCommutative [Finite G] [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hAcomm : IsMulCommutative ↥A) {M₁ M₂ : Subgroup G} (hM₁ : IsCoatom M₁) (hM₂ : IsCoatom M₂)
    (hM₁₂ : M₁ ≠ M₂) (hAM₁ : A ≤ M₁) (hAM₂ : A ≤ M₂) (hBA : B ≤ A)
    (hBiso : Nonempty (↥B ≃* (Fin 2 → Multiplicative (ZMod p)))) (hM : IsCoatom M)
    (hCM : centralizer (A : Set G) ≤ M) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ L : Subgroup G, IsCoatom L ∧ L ≠ M ∧
      centralizer ({b} : Set G) ≤ L ∧ centralizer (A : Set G) ≤ L := by
  have := Fact.mk hp
  have hAC : A ≤ centralizer (A : Set G) := have := hAcomm; Subgroup.le_centralizer A
  have hBM : B ≤ M := hBA.trans (hAC.trans hCM)
  by_cases hcent : ∀ b ∈ B, b ≠ 1 → centralizer ({b} : Set G) ≤ M
  ·
    exfalso
    have hu : IsUniqueMaximalOvergroup B M :=
      isUniqueMaximalOvergroup_of_centralizer_le_pi hp hna hodd hsolv hM hBiso le_rfl hBM hcent
    have hAtop : A ≠ ⊤ := fun h => hM₁.1 (top_le_iff.1 (h ▸ hAM₁))
    have hu' : IsUniqueMaximalOvergroup A M := hu.mono hBA hAtop
    exact hM₁₂ ((hu'.eq_of_isCoatom hM₁ hAM₁).trans (hu'.eq_of_isCoatom hM₂ hAM₂).symm)
  ·
    simp only [not_forall] at hcent
    obtain ⟨b, hbB, hb1, hbM⟩ := hcent
    obtain ⟨L, hL, hCL⟩ :=
      exists_isCoatom_ge_of_ne_top (centralizer_singleton_lt_top hna hb1).ne
    exact ⟨b, hbB, hb1, L, hL, fun h => hbM (h ▸ hCL), hCL,
      (centralizer_le (Set.singleton_subset_iff.2 (hBA hbB))).trans hCL⟩

theorem exists_escaping_centralizer [Finite G] [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hAcomm : IsMulCommutative ↥A) (_hAp : IsPGroup p ↥A) {M₁ M₂ : Subgroup G}
    (hM₁ : IsCoatom M₁) (hM₂ : IsCoatom M₂) (hM₁₂ : M₁ ≠ M₂) (hAM₁ : A ≤ M₁) (hAM₂ : A ≤ M₂)
    (hBA : B ≤ A) (hBiso : Nonempty (↥B ≃* (Fin 2 → Multiplicative (ZMod p)))) (hM : IsCoatom M)
    (hCM : centralizer (A : Set G) ≤ M) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ L : Subgroup G, IsCoatom L ∧ L ≠ M ∧
      centralizer ({b} : Set G) ≤ L ∧ centralizer (A : Set G) ≤ L :=
  exists_escaping_centralizer_of_isMulCommutative hp hna hodd hsolv hAcomm hM₁ hM₂ hM₁₂ hAM₁ hAM₂
    hBA hBiso hM hCM

theorem exists_escaping_centralizer_of_isElementaryAbelian [Finite G] [IsSimpleGroup G]
    (hp : p.Prime) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hAcomm : IsMulCommutative ↥A) {M₁ M₂ : Subgroup G} (hM₁ : IsCoatom M₁) (hM₂ : IsCoatom M₂)
    (hM₁₂ : M₁ ≠ M₂) (hAM₁ : A ≤ M₁) (hAM₂ : A ≤ M₂) (hBA : B ≤ A)
    (hBe : IsElementaryAbelian p B) (hBcard : Nat.card ↥B = p ^ 2) (hM : IsCoatom M)
    (hCM : centralizer (A : Set G) ≤ M) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ L : Subgroup G, IsCoatom L ∧ L ≠ M ∧
      centralizer ({b} : Set G) ≤ L ∧ centralizer (A : Set G) ≤ L :=
  exists_escaping_centralizer_of_isMulCommutative hp hna hodd hsolv hAcomm hM₁ hM₂ hM₁₂ hAM₁ hAM₂
    hBA (nonempty_mulEquiv_pi_of_isElementaryAbelian hp hBe hBcard) hM hCM

end

end CFSG.FeitThompson
