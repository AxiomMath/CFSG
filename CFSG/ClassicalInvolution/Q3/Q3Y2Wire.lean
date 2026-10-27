module

public import CFSG.ClassicalInvolution.Q3.Q3Y2Orth
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSp
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSL
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSL
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y2

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Wire

theorem top_le_sup_sup_of_sup_eq_top {G : Type} [Group G] {A B C : Subgroup G}
    (h : A ⊔ B = ⊤) : (⊤ : Subgroup G) ≤ A ⊔ B ⊔ C := by
  rw [h, top_sup_eq]

theorem twinStrong3_psp {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1) :
    TwinStrong3 (Generic.fundamentalSubgroups .PSp
      (Generic.modelUniv .PSp n 3 1 Nat.prime_three).D) := by
  have key : TwinStrong3 (G := StatedSp n 𝔽₃)
      (fundamentalSubgroups .PSp (modelUniv .PSp n 3 1 Nat.prime_three).D) := by
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _ r₁ hr₁ r₂ hr₂ hsq₁ hsq₂
    obtain ⟨-, -, -, hgen⟩ := sp_twin_gen hadm.2.2.1 e₁ e₂ (isLongRootSp2_sl2Inv hadm hR₁ e₁)
      (isLongRootSp2_sl2Inv hadm hR₂ e₂) hne hcen
    exact top_le_sup_sup_of_sup_eq_top (hgen r₁ hr₁ r₂ hr₂ hsq₁ hsq₂)
  exact key

theorem twinStrong3_psl_four :
    TwinStrong3 (Generic.fundamentalSubgroups .PSL
      (Generic.modelUniv .PSL 4 3 1 Nat.prime_three).D) := by
  have key : TwinStrong3 (G := SL(4, 𝔽₃))
      (fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D) := by
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _ r₁ hr₁ r₂ hr₂ hsq₁ hsq₂
    obtain ⟨-, -, -, hgen⟩ := sl4_twin_gen (isLongRootSL2_sl2Inv_four hR₁ e₁)
      (isLongRootSL2_sl2Inv_four hR₂ e₂) hne hcen
    exact top_le_sup_sup_of_sup_eq_top (hgen r₁ hr₁ r₂ hr₂ hsq₁ hsq₂)
  exact key

theorem twinStrong3_psl_ne_four {k : ℕ} (hadm : StatedLieAdmissible .PSL k 3 1) (hk : k ≠ 4) :
    TwinStrong3 (Generic.fundamentalSubgroups .PSL
      (Generic.modelUniv .PSL k 3 1 Nat.prime_three).D) := by
  have hk2 : 2 ≤ k := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hL := fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := m) (by omega)
  have key : TwinStrong3 (G := SL(m + 1, 𝔽₃))
      (fundamentalSubgroups .PSL (modelUniv .PSL (m + 1) 3 1 Nat.prime_three).D) := by
    intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _
    exfalso
    have hR₁' : R₁ ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ m + 1) := by rw [← hL]; exact hR₁
    have hR₂' : R₂ ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ m + 1) := by rw [← hL]; exact hR₂
    obtain ⟨i₁, hi₁⟩ := hR₁'
    obtain ⟨i₂, hi₂⟩ := hR₂'
    have hi₁e : i₁ = sl2Inv e₁ :=
      eq_sl2Inv_of_orderOf_eq_two hodd e₁ hi₁.mem ((hi₁.isClassicalSL2 h2).orderOf_eq_two)
    have hi₂e : i₂ = sl2Inv e₂ :=
      eq_sl2Inv_of_orderOf_eq_two hodd e₂ hi₂.mem ((hi₂.isClassicalSL2 h2).orderOf_eq_two)
    exact hne (eq_of_central_ratio_longRoot (by omega) hk hi₁ hi₂
      (by rw [hi₁e, hi₂e]; exact hcen))
  exact key

end Wire

end CFSG.ClassicalInvolution.Q3.Q3Y2
