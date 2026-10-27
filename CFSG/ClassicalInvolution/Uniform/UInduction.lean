module

public import CFSG.ClassicalInvolution.Uniform.UFacade
public import CFSG.ClassicalInvolution.Q3.Induction
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Induction

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Class

variable {Y : Type} [Group Y]

structure InClassU (t : MemberType) (Λ : Set (Subgroup Y)) : Prop where
  nonempty : Λ.Nonempty
  conjInvariant : ConjInvariant Λ
  generated : ⨆ L ∈ Λ, L = ⊤
  classical : ∀ L ∈ Λ, ∃ z : Y, IsClassicalMemberU t L z

theorem InClassU.admissible {t : MemberType} {Λ : Set (Subgroup Y)} (h : InClassU t Λ) :
    t.Admissible := by
  obtain ⟨L, hL⟩ := h.nonempty
  obtain ⟨z, hz⟩ := h.classical L hL
  exact hz.admissible

theorem eq_three_one_of_pow_eq_three {p f : ℕ} (hp : p.Prime) (h : p ^ f = 3) :
    p = 3 ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h
  have hdvd : p ∣ 3 := by
    rw [← h]
    exact dvd_pow_self p hf
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h)⟩

section Facades

variable {Λ : Set (Subgroup Y)}

theorem inClassU_iff_inClass {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    InClassU (.sl2 p f) Λ ↔ InClass p f Λ := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  refine ⟨fun h => ⟨h.nonempty, h.conjInvariant, h.generated, fun L hL => ?_⟩,
    fun h => ⟨h.nonempty, h.conjInvariant, h.generated, fun L hL => ?_⟩⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, hz.toGeneric hq⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, IsClassicalMemberU.ofGeneric hp2 hf hz⟩

theorem inClassU_three_iff : InClassU (.sl2 3 1) Λ ↔ Q3.InClass3 Λ := by
  refine ⟨fun h => ⟨h.nonempty, h.conjInvariant, h.generated, fun L hL => ?_⟩,
    fun h => ⟨h.nonempty, h.conjInvariant, h.generated, fun L hL => ?_⟩⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, hz.toQ3 (by norm_num)⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, IsClassicalMemberU.ofQ3 hz⟩

theorem inClassU_twoA7_iff : InClassU .twoA7 Λ ↔ Hat2A7.InClass2A7 Λ := by
  refine ⟨fun h => ⟨h.nonempty, h.conjInvariant, h.generated, fun L hL => ?_⟩,
    fun h => ⟨h.nonempty, h.conjInvariant, h.generated, fun L hL => ?_⟩⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, hz.to2A7⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, IsClassicalMemberU.of2A7 hz⟩

end Facades

end Class

section Conclusion

variable {Y : Type} [Group Y]

@[expose] def LieSystemModU (t : MemberType) (Λ : Set (Subgroup Y)) : Prop :=
  match t with
  | .sl2 p f => ∃ _ : Fact p.Prime,
      if p ^ f = 3 then Q3.LieSystemMod3 Λ else LieSystemMod p f Λ
  | .twoA7 => Hat2A7.A7SystemMod Λ

variable {Λ : Set (Subgroup Y)}

theorem lieSystemModU_sl2_of_ne_three {p f : ℕ} [Fact p.Prime] (h3 : p ^ f ≠ 3) :
    LieSystemModU (.sl2 p f) Λ ↔ LieSystemMod p f Λ := by
  simp only [LieSystemModU, h3, ite_false]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨inferInstance, h⟩⟩

theorem lieSystemModU_sl2_of_eq_three {p f : ℕ} [Fact p.Prime] (h3 : p ^ f = 3) :
    LieSystemModU (.sl2 p f) Λ ↔ Q3.LieSystemMod3 Λ := by
  simp only [LieSystemModU, h3, ite_true]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨inferInstance, h⟩⟩

theorem lieSystemModU_twoA7 : LieSystemModU .twoA7 Λ ↔ Hat2A7.A7SystemMod Λ := Iff.rfl

end Conclusion

section Induction

@[expose] def CITBelowT (t : MemberType) (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ Λ : Set (Subgroup Y), InClassU t Λ → LieSystemModU t Λ

@[expose] def CITInductiveT (t : MemberType) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClassU t Λ → LieSystemModU t Λ

@[expose] def CITStepT (t : MemberType) (n : ℕ) : Prop :=
  CITBelowT t n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ Λ : Set (Subgroup Y), InClassU t Λ → LieSystemModU t Λ

theorem CITBelowT.mono {t : MemberType} {m n : ℕ} (h : m ≤ n) (hn : CITBelowT t n) :
    CITBelowT t m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ

theorem citInductiveT_of_step {t : MemberType} (h : ∀ n, CITStepT t n) : CITInductiveT t := by
  have key : ∀ n, ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
      ∀ Λ : Set (Subgroup Y), InClassU t Λ → LieSystemModU t Λ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y _ _ hY Λ hΛ
      exact h n (fun Y' _ _ hlt Λ' hΛ' => ih _ hlt Y' rfl Λ' hΛ') Y hY Λ hΛ
  intro Y _ _ Λ hΛ
  exact key _ Y rfl Λ hΛ

theorem citBelowT_iff_citBelowU {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (n : ℕ) : CITBelowT (.sl2 p f) n ↔ CITBelowU p f n := by
  have h3 : p ^ f ≠ 3 := by omega
  refine ⟨fun h Y _ _ hY Λ hΛ => ?_, fun h Y _ _ hY Λ hΛ => ?_⟩
  · exact (lieSystemModU_sl2_of_ne_three h3).mp (h Y hY Λ ((inClassU_iff_inClass hp2 hq).mpr hΛ))
  · exact (lieSystemModU_sl2_of_ne_three h3).mpr (h Y hY Λ ((inClassU_iff_inClass hp2 hq).mp hΛ))

theorem citBelowT_three_iff {p f : ℕ} [Fact p.Prime] (h3 : p ^ f = 3) (n : ℕ) :
    CITBelowT (.sl2 p f) n ↔ Q3.CIT3Below n := by
  obtain ⟨rfl, rfl⟩ := eq_three_one_of_pow_eq_three Fact.out h3
  refine ⟨fun h Y _ _ hY Λ hΛ => ?_, fun h Y _ _ hY Λ hΛ => ?_⟩
  · exact (lieSystemModU_sl2_of_eq_three h3).mp (h Y hY Λ (inClassU_three_iff.mpr hΛ))
  · exact (lieSystemModU_sl2_of_eq_three h3).mpr (h Y hY Λ (inClassU_three_iff.mp hΛ))

theorem citBelowT_twoA7_iff (n : ℕ) : CITBelowT .twoA7 n ↔ Hat2A7.CITBelow2A7 n := by
  refine ⟨fun h Y _ _ hY Λ hΛ => ?_, fun h Y _ _ hY Λ hΛ => ?_⟩
  · exact (h Y hY Λ (inClassU_twoA7_iff.mpr hΛ))
  · exact (h Y hY Λ (inClassU_twoA7_iff.mp hΛ))

@[expose] def CITBelowAllT (p : ℕ) (n : ℕ) : Prop :=
  ∀ e : ℕ, 3 ≤ p ^ e → CITBelowT (.sl2 p e) n

end Induction

end CFSG.ClassicalInvolution.Uniform
