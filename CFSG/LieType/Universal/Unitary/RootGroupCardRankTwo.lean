module

public import CFSG.LieType.Universal.Unitary.Extras
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.LieType.Universal.Unitary.Extras.Basic
import CFSG.LieType.Universal.Unitary.RootGroupCard

public section

namespace CFSG.LieType.Universal.Unitary

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary.SUExtras

variable {F : Type} [Field F]

theorem rootHom_range_rev_le {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (hij' : Fin.rev j ≠ Fin.rev i)
    (hi' : Fin.rev j ≠ Fin.rev (Fin.rev j)) (hj' : Fin.rev i ≠ Fin.rev (Fin.rev i)) :
    (rootHom σ hσ hij' hi' hj').range ≤ (rootHom σ hσ hij hi hj).range := by
  rintro _ ⟨c, rfl⟩
  refine ⟨Multiplicative.ofAdd (-(σ c.toAdd)), ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext a b
  simp only [coe_rootHom, rootMatrix, Fin.rev_rev, hσ, map_neg, toAdd_ofAdd,
    Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  have hB : (if i = a ∧ j = b then -σ (Multiplicative.toAdd c) else 0) =
      -(if i = a ∧ j = b then σ (Multiplicative.toAdd c) else 0) := by
    split_ifs <;> ring
  have hC : (if Fin.rev j = a ∧ Fin.rev i = b then -Multiplicative.toAdd c else 0) =
      -(if Fin.rev j = a ∧ Fin.rev i = b then Multiplicative.toAdd c else 0) := by
    split_ifs <;> ring
  rw [hB, hC]
  ring

theorem rootGroup_four_zero {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) :
    rootGroup σ hσ 4 (Pi.single 0 1) =
      (rootHom σ hσ (i := 0) (j := 1) (by decide) (by decide) (by decide)).range := by
  have hto : toStd 4 (Pi.single 0 1) = weight 4 0 - weight 4 1 := by decide
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      rw [hto] at hw
      rcases eq_of_weight_sub_eq_sub (i := 0) (j := 1) (by decide) (by decide) (by decide)
        (by decide) hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact le_rfl
      · exact rootHom_range_rev_le (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      rw [hto] at hw
      exfalso
      obtain ⟨h0, h1⟩ := eq_of_weight_sub_eq_two_smul (i := i) hi hw.symm
      have hi0 : i = 0 := h0.symm
      subst hi0
      exact absurd h1 (by decide)
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact rootHom_mem hσ (by decide) (by decide) (by decide) (by decide) hto.symm c

theorem rootGroup_four_one {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) :
    rootGroup σ hσ 4 (Pi.single 1 1) = (longRootHom σ (i := (1 : Fin 4)) (by decide)).range := by
  have hto : toStd 4 (Pi.single 1 1) = 2 • weight 4 1 := by decide
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      rw [hto] at hw
      obtain ⟨hi1, hj1⟩ := eq_of_weight_sub_eq_two_smul (i := 1) (by decide) hw
      subst hi1
      subst hj1
      exact absurd rfl hji
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      rw [hto] at hw
      have hwi : weight 4 i - weight 4 (Fin.rev i) = 2 • weight 4 1 := by
        calc weight 4 i - weight 4 (Fin.rev i)
            = weight 4 i + weight 4 i := by rw [weight_rev', sub_neg_eq_add]
          _ = 2 • weight 4 i := by rw [two_smul]
          _ = 2 • weight 4 1 := hw
      obtain ⟨hi1, -⟩ := eq_of_weight_sub_eq_two_smul (i := 1) (by decide) hwi
      subst hi1
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ (by decide) hto.symm c

theorem rootGroup_five_zero {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) :
    rootGroup σ hσ 5 (Pi.single 0 1) =
      (rootHom σ hσ (i := 0) (j := 1) (by decide) (by decide) (by decide)).range := by
  have hto : toStd 5 (Pi.single 0 1) = weight 5 0 - weight 5 1 := by decide
  have hmid : Fin.rev (2 : Fin 5) = 2 := by decide
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      rw [hto] at hw
      rcases eq_of_weight_sub_eq_sub (i := 0) (j := 1) (by decide) (by decide) (by decide)
        (by decide) hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact le_rfl
      · exact rootHom_range_rev_le (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      rw [hto] at hw
      exfalso
      obtain ⟨h0, h1⟩ := eq_of_weight_sub_eq_two_smul (i := i) hi hw.symm
      have hi0 : i = 0 := h0.symm
      subst hi0
      exact absurd h1 (by decide)
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      rw [hto] at hw
      exfalso
      rcases eq_of_weight_sub_eq_weight (i := i) (k := 2) hi hmid hw.symm with
        ⟨-, hk1⟩ | ⟨hk0, -⟩
      · exact absurd hk1 (by decide)
      · exact absurd hk0 (by decide)
  · rintro _ ⟨c, rfl⟩
    exact rootHom_mem hσ (by decide) (by decide) (by decide) (by decide) hto.symm c

theorem rootGroup_five_one {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) :
    rootGroup σ hσ 5 (Pi.single 1 1) =
      heisenbergSubgroup σ hσ (i := 1) (k := 2) (by decide) (by decide) (by decide) := by
  have hto : toStd 5 (Pi.single 1 1) = weight 5 1 := by decide
  have hmid : Fin.rev (2 : Fin 5) = 2 := by decide
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      rw [hto] at hw
      rcases eq_of_weight_sub_eq_weight (i := 1) (k := 2) (by decide) hmid hw with
        ⟨-, hj2⟩ | ⟨hi2, -⟩
      · subst hj2
        exact absurd hmid.symm hj
      · subst hi2
        exact absurd hmid.symm hi
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      rw [hto] at hw
      exfalso
      revert hw
      fin_cases i <;> decide
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      rw [hto] at hw
      have h0 : weight 5 2 = 0 := by decide
      have h : weight 5 1 - weight 5 2 = weight 5 i := by
        rw [h0, sub_zero]
        exact hw.symm
      rcases eq_of_weight_sub_eq_weight (i := i) (k := 2) hi hmid h with
        ⟨hi1, hk2⟩ | ⟨hk1, -⟩
      · have hk_eq : k = 2 := by
          revert hk
          fin_cases k <;> decide
        subst hi1
        subst hk_eq
        exact le_rfl
      · exact absurd hk1 (by decide)
  · exact heisenberg_le hσ (by decide) (by decide) (by decide) hto.symm

theorem card_rootGroup_four_zero_ne_one [Finite F] [CharP F 2] [Fact (Nat.Prime 2)] {f : ℕ}
    (hcard : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card ((rootDatum hcard 4).rootGroup (Pi.single (0 : Fin 2) 1)) ≠
      Nat.card ((rootDatum hcard 4).rootGroup (Pi.single (1 : Fin 2) 1)) := by
  have hσ := unitaryInvolution_involutive hcard
  change Nat.card (rootGroup (unitaryInvolution F 2 f) hσ 4 (Pi.single (0 : Fin 2) 1)) ≠
    Nat.card (rootGroup (unitaryInvolution F 2 f) hσ 4 (Pi.single (1 : Fin 2) 1))
  rw [rootGroup_four_zero hσ, rootGroup_four_one hσ]
  rw [card_rootHom_range hσ (by decide) (by decide) (by decide) (by decide),
    card_longRootHom_range (by decide),
    CFSG.LieType.Steinberg.card_traceZero hcard, hcard]
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero, one_pow] at hcard
      have h1 := Finite.one_lt_card (α := F)
      omega
    · exact h
  have hlt : 2 ^ f < (2 ^ f) ^ 2 := by
    simpa using Nat.pow_lt_pow_right (Nat.one_lt_two_pow hf.ne') (by norm_num : 1 < 2)
  exact ne_of_gt hlt

theorem card_rootGroup_five_zero_ne_one [Finite F] [CharP F 2] [Fact (Nat.Prime 2)] {f : ℕ}
    (hcard : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card ((rootDatum hcard 5).rootGroup (Pi.single (0 : Fin 2) 1)) ≠
      Nat.card ((rootDatum hcard 5).rootGroup (Pi.single (1 : Fin 2) 1)) := by
  have hσ := unitaryInvolution_involutive hcard
  change Nat.card (rootGroup (unitaryInvolution F 2 f) hσ 5 (Pi.single (0 : Fin 2) 1)) ≠
    Nat.card (rootGroup (unitaryInvolution F 2 f) hσ 5 (Pi.single (1 : Fin 2) 1))
  rw [rootGroup_five_zero hσ, rootGroup_five_one hσ]
  rw [card_rootHom_range hσ (by decide) (by decide) (by decide) (by decide),
    card_heisenbergSubgroup hcard (by decide) (by decide) (by decide), hcard]
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero, one_pow] at hcard
      have h1 := Finite.one_lt_card (α := F)
      omega
    · exact h
  have hlt : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 := by
    simpa using Nat.pow_lt_pow_right (Nat.one_lt_two_pow hf.ne') (by norm_num : 2 < 3)
  exact ne_of_lt hlt

end CFSG.LieType.Universal.Unitary
