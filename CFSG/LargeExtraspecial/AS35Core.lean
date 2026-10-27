module

public import CFSG.LargeExtraspecial.AS35Weak
public import CFSG.LargeExtraspecial.AS35Sp
public import CFSG.LargeExtraspecial.AS35R3
public import CFSG.LargeExtraspecial.AS35U2
public import CFSG.LargeExtraspecial.S14Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open

theorem psu_of_threeTransposition
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hn : 3 ≤ S.width)
    (h3 : ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) :
    Nonempty (G ≃* timmesfeldPSU (S.width + 2)) := by
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned G {g | IsConj S.z g}
      ⟨S.z, rfl⟩ (fun _ hd => S.orderOf_of_isConj hd)
      (fun _ hd _ he => S.orderOf_mul_mem_of_isConj h3 hd he) S.closure_conj_eq_top
      S.center_eq_bot S.isSimpleGroup_commutator with
    ⟨m, -, φ, hφ⟩ | ⟨m, -, b, halt, hnd, h2⟩ | ⟨m, -, Q, hnd, -, h3'⟩ | ⟨m, hm, h4⟩ |
      ⟨m, hm, f, hsymm, hnd, h5⟩ | ⟨φ, -⟩ | ⟨φ, -⟩ | ⟨φ, -⟩
  · exact (S.false_of_perm φ ((hφ S.z).mp (IsConj.refl _))).elim
  · exact (S.false_of_case2 halt hnd h2).elim
  · exact (S.false_of_case3 hnd h3').elim
  · exact S.psu_of_case4 (by omega) hm h4
  · exact (S.false_of_case5 hn hm hsymm hnd h5).elim
  · exact (S.false_of_sporadic h3 (Or.inl ⟨φ⟩)).elim
  · exact (S.false_of_sporadic h3 (Or.inr (Or.inl ⟨φ⟩))).elim
  · exact (S.false_of_sporadic h3 (Or.inr (Or.inr ⟨φ⟩))).elim

namespace Setting

variable {G : Type} [Group G] [Finite G]

@[expose] def MbarTwoBound (S : Setting G) (e : ℕ) : Prop :=
  ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ e

theorem MbarTwoBound.of (S : Setting G) {e : ℕ}
    (h : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ e) : S.MbarTwoBound e :=
  h

theorem MbarTwoBound.card_le {S : Setting G} {e : ℕ} (h : S.MbarTwoBound e) (P : Subgroup S.Mbar)
    (hP : IsPGroup 2 P) : Nat.card P ≤ 2 ^ e :=
  h P hP

end Setting

namespace S14

@[expose] def AschbacherThreeTranspositionCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 4 ≤ S.width →
    (5 ≤ S.width ∨ S.MbarTwoBound 7) →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
      ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)

theorem AschbacherSmithW4Input.psu (hAS : AschbacherSmithW4Input) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 4) (hP : S.MbarTwoBound 7)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) :
    Nonempty (G ≃* timmesfeldPSU 6) :=
  hAS G S hw hP.card_le hW

theorem aschbacherSmithWideInput_of_core
    (h : AschbacherThreeTranspositionCore) : AschbacherSmithWideInput := by
  intro G _ _ _ S hn hW
  exact psu_of_threeTransposition S (by omega) (h G S (by omega) (Or.inl hn) hW)

theorem aschbacherSmithW4Input_of_core
    (h : AschbacherThreeTranspositionCore) : AschbacherSmithW4Input := by
  intro G _ _ _ S hw hP hW
  have hU := psu_of_threeTransposition S (by omega)
    (h G S (by omega) (Or.inr (Setting.MbarTwoBound.of S hP)) hW)
  rw [hw] at hU
  exact hU

@[expose] def AschbacherSmith35Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 3 ≤ S.width →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
      (∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) ∨
        (S.width = 4 ∧ Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co2))

theorem aschbacherSmith35Input_of_core
    (h : AschbacherSmith35Core) : AschbacherSmith35Input := by
  intro G _ _ _ S hn hW
  rcases h G S hn hW with h3 | hCo
  · exact Or.inl (psu_of_threeTransposition S hn h3)
  · exact Or.inr hCo

end S14

end CFSG.LargeExtraspecial
