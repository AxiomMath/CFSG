module

public import CFSG.GF2Type.Smith1979.W4InspOrdA
public import CFSG.Sporadic.Co1Patterson.SettingOmega
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Timmesfeld.Outcome

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.Orders

variable {G : Type} [Group G] [Finite G]

theorem card_O_cases (S : Setting G) (hw : S.width = 4) :
    Nat.card S.O = 348364800 ∨ Nat.card S.O = 394813440 := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have h8 : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  rcases CFSG.Sporadic.Co1Patterson.natCard_orthogonalGroup_of_finrank_eight
    S.q_nondegenerate h8 with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem card_Xbar_dvd (S : Setting G) (g : G) (hw : S.width = 4) :
    Nat.card (S.Xbar12 g) ∣ 348364800 ∨ Nat.card (S.Xbar12 g) ∣ 394813440 := by
  have h := Subgroup.card_subgroup_dvd_card (S.Xbar12 g)
  rcases card_O_cases S hw with h' | h'
  · exact Or.inl (h' ▸ h)
  · exact Or.inr (h' ▸ h)

namespace Survivors

theorem psl {X : Type} [Group X] {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (h : LieModel X .PSL n 2 f) (hd : Nat.card X ∣ 348364800 ∨ Nat.card X ∣ 394813440) :
    LieModel X .PSL 3 2 1 ∨ LieModel X .PSL 3 2 2 ∨ LieModel X .PSL 4 2 1 := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (h.statedClassicalModel (by decide))).1 rfl
  rw [hc] at hd
  rcases psl_numeric hn hf hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem psp {X : Type} [Group X] {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (h : LieModel X .PSp n 2 f) (hd : Nat.card X ∣ 348364800 ∨ Nat.card X ∣ 394813440) :
    LieModel X .PSp 3 2 1 := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (h.statedClassicalModel (by decide))).2.2.1 rfl
  rw [hc] at hd
  obtain ⟨rfl, rfl⟩ := psp_numeric hn hf hd
  exact h

theorem pomegaPlus {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (h : LieModel X .POmegaPlus n 2 f) (hd : Nat.card X ∣ 348364800 ∨ Nat.card X ∣ 394813440) :
    LieModel X .POmegaPlus 4 2 1 := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (h.statedClassicalModel (by decide))).2.2.2.1 rfl
  rw [hc] at hd
  obtain ⟨rfl, rfl⟩ := pomegaPlus_numeric hn hf hd
  exact h

theorem pomegaMinus {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (h : LieModel X .POmegaMinus n 2 f) (hd : Nat.card X ∣ 348364800 ∨ Nat.card X ∣ 394813440) :
    LieModel X .POmegaMinus 4 2 1 := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (h.statedClassicalModel (by decide))).2.2.2.2 rfl
  rw [hc] at hd
  obtain ⟨rfl, rfl⟩ := pomegaMinus_numeric hn hf hd
  exact h

end Survivors

section Orders


namespace Survivors

theorem false_of_exceptional {X : Type} [Group X] {τ : StatedLieTag} {f : ℕ} (hf : 1 ≤ f)
    (hτ : τ ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (hG2 : τ = .G2 → 2 ≤ f) (h : LieModel X τ 0 2 f)
    (hd : Nat.card X ∣ 348364800 ∨ Nat.card X ∣ 394813440) : False := by
  have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
    (CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by revert hτ; cases τ <;> decide))
  rw [hc] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact g2_numeric (hG2 rfl) hd
  · exact trialityD4_numeric hf hd
  · exact false_of_profile (profile_ordF4 hf) (by omega) hd
  · exact false_of_profile (profile_ordE6 hf) (by omega) hd
  · exact false_of_profile (profile_ordTwistedE6 hf) (by omega) hd
  · exact false_of_profile (profile_ordE7 hf) (by omega) hd
  · exact false_of_profile (profile_ordE8 hf) (by omega) hd

end Survivors

theorem outcome_survivors {X : Type} [Group X] [Finite X] (h : CFSG.Timmesfeld.Outcome X)
    (hd : Nat.card X ∣ 348364800 ∨ Nat.card X ∣ 394813440) :
    LieModel X .PSL 3 2 1 ∨ LieModel X .PSL 3 2 2 ∨ LieModel X .PSL 4 2 1 ∨
      LieModel X .PSp 3 2 1 ∨ LieModel X .POmegaPlus 4 2 1 ∨ LieModel X .POmegaMinus 4 2 1 ∨
      LieModel X .PSU 3 3 1 ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic X .J2 := by
  rcases h with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
    ⟨f, hf, τ, hτ, h⟩ | h | he | hJ
  · rcases Survivors.psl hn hf h hd with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Survivors.psp hn hf h hd))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Survivors.pomegaPlus hn hf h hd)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Survivors.pomegaMinus hn hf h hd))))))
  · exact (Survivors.false_of_exceptional (by omega) (by decide) (fun _ => hf) h hd).elim
  · exact (Survivors.false_of_exceptional hf (by revert hτ; cases τ <;> decide)
      (fun hG => by subst hG; exact absurd hτ (by decide)) h hd).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ)))))))

end Orders

end CFSG.GF2Type.Smith1979.W4Insp
