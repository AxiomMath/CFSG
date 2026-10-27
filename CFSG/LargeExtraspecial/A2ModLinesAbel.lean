module

public import CFSG.LargeExtraspecial.A2ModBasicThird
public import CFSG.LargeExtraspecial.A2ModBasicPoint
public import CFSG.LargeExtraspecial.A2ModLines

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2

namespace A2Action

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {A : Subgroup X}

omit [FiniteDimensional (ZMod 2) V] in
theorem mul_mem_of_mem (hA : A2Action D Q ρ) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) {a b : X}
    (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hab : a ≠ b) : a * b ∈ D ∧ a * b ≠ 1 := by
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hA.mul_self (hAD a ha ha1))
    rw [← hinv]
    exact (eq_inv_of_mul_eq_one_right h).symm
  exact ⟨hAD _ (mul_mem ha hb) hab1, hab1⟩

theorem inf_ne_bot_of_mem (hA : A2Action D Q ρ) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) {a b : X}
    (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    commSpace (ρ a) ⊓ commSpace (ρ b) ≠ ⊥ := by
  by_cases hab : a = b
  · subst hab
    rw [inf_idem]
    intro h
    have h2 := (hA.isTypeA (hAD a ha ha1)).2.2.2.1
    rw [h, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  · have hmul := hA.isTypeA (hA.mul_mem_of_mem hAD ha hb ha1 hab).1
    rw [map_mul] at hmul
    exact (timmesfeld_12_1 hA.nondegenerate (hA.isTypeA (hAD a ha ha1))
      (hA.isTypeA (hAD b hb hb1)) hmul).2.1

theorem card_commSpaceOf_of_common_point (hA : A2Action D Q ρ)
    (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) (hA1 : A ≠ ⊥) {P : V} (hP : P ≠ 0)
    (hPA : ∀ a ∈ A, a ≠ 1 → P ∈ commSpace (ρ a)) :
    2 ^ finrank (ZMod 2) (commSpaceOf ρ A) = 2 * Nat.card A := by
  classical
  have hQ := hA.nondegenerate
  obtain ⟨a₀, ha₀, ha₀1⟩ := (A.bot_or_exists_ne_one).resolve_left hA1
  have hqP : Q P = 0 := (hA.isTypeA (hAD a₀ ha₀ ha₀1)).2.2.2.2 P (hPA a₀ ha₀ ha₀1)
  have hN : ∀ a ∈ A, ρ a ∈ pointRadical Q P := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1, map_one]
      exact one_mem _
    exact hA.mem_pointRadical_of_mem_commSpace hP (hAD a ha ha1) (hPA a ha ha1)
  obtain ⟨v₀, hv₀⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hQ hP
  have hv₀1 : polar Q v₀ P = 1 := by
    rw [polar_comm]
    exact zmod2_eq_one_of_ne_zero hv₀
  let u : A → V := fun a => ρ a v₀ - v₀
  have hu_mem : ∀ a : A, u a ∈ commSpace (ρ a) := fun a => sub_mem_commSpace _ _
  have hu_sing : ∀ a : A, Q (u a) = 0 := by
    intro a
    by_cases ha1 : (a : X) = 1
    · simp [u, ha1]
    · exact (hA.isTypeA (hAD a a.2 ha1)).2.2.2.2 _ (hu_mem a)
  have hu_v₀ : ∀ a : A, polar Q v₀ (u a) = 0 := by
    intro a
    have h := map_sub_eq_polar (hA.mem_orthogonalGroup a) v₀
    have h0 : Q (ρ a v₀ - v₀) = 0 := hu_sing a
    rw [h0] at h
    change polar Q v₀ (ρ a v₀ - v₀) = 0
    rw [polar_sub_right, polar_self_eq_zero, sub_zero, polar_comm, ← h]
  have hu_P : ∀ a : A, polar Q P (u a) = 0 := fun a => (hN a a.2).2.2.2 v₀
  have hu_one : u 1 = 0 := by simp [u]
  have hu_mul : ∀ a b : A, u (a * b) = u a + u b := by
    intro a b
    have hw : ρ a (u b) - u b ∈ (ZMod 2) ∙ P := (hN a a.2).2.2.1 (u b) (hu_P b)
    have hsum : u (a * b) = u a + u b + (ρ a (u b) - u b) := by
      simp only [u, Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply, map_sub]
      abel
    have hpol : polar Q v₀ (ρ a (u b) - u b) = 0 := by
      have h := congrArg (polar Q v₀) hsum
      rw [polar_add_right, polar_add_right, hu_v₀, hu_v₀, hu_v₀, zero_add, zero_add] at h
      exact h.symm
    rcases mem_span_singleton_iff.mp hw with h0 | hPw
    · rw [hsum, h0, add_zero]
    · rw [hPw, hv₀1] at hpol
      exact absurd hpol one_ne_zero
  have hu_ne : ∀ a : A, (a : X) ≠ 1 → u a ≠ 0 := by
    intro a ha1 h0
    have hfix : v₀ ∈ fixSpace (ρ a) := mem_fixSpace.mpr (sub_eq_zero.mp h0)
    rw [fixSpace_eq_orthogonal_commSpace_of_mem hQ (hA.mem_orthogonalGroup a)] at hfix
    have h := mem_orthogonal_iff_polar.mp hfix P (hPA a a.2 ha1)
    rw [hv₀1] at h
    exact one_ne_zero h
  have hu_inj : Function.Injective u := by
    intro a b hab
    have hinv : u b⁻¹ = u b := by
      have h := hu_mul b b⁻¹
      rw [mul_inv_cancel, hu_one] at h
      calc u b⁻¹ = u b + (u b + u b⁻¹) := by rw [← add_assoc, vec_add_self, zero_add]
        _ = u b := by rw [← h, add_zero]
    have h := hu_mul a b⁻¹
    rw [hinv, hab, vec_add_self] at h
    by_contra hne
    have hne1 : ((a * b⁻¹ : A) : X) ≠ 1 := fun h1 =>
      hne (mul_inv_eq_one.mp (Subtype.ext h1))
    exact hu_ne _ hne1 h
  let T : Submodule (ZMod 2) V :=
    { carrier := Set.range u
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, hu_mul a b⟩
      zero_mem' := ⟨1, hu_one⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
        · exact ⟨1, by rw [hu_one, zero_smul]⟩
        · exact ⟨a, by rw [one_smul]⟩ }
  have hmemT : ∀ a : A, u a ∈ T := fun a => ⟨a, rfl⟩
  have hcardT : Nat.card T = Nat.card A := Nat.card_range_of_injective hu_inj
  have hfinT : Nat.card T = 2 ^ finrank (ZMod 2) T := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle1 : commSpaceOf ρ A ≤ T ⊔ (ZMod 2) ∙ P := by
    rw [commSpaceOf_le_iff]
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1, map_one, commSpace_eq_bot_iff.mpr rfl]
      exact bot_le
    have hli : LinearIndependent (ZMod 2) ![P, u ⟨a, ha⟩] := by
      refine linearIndependent_pair_iff.mpr ⟨hP, hu_ne ⟨a, ha⟩ ha1, fun h => ?_⟩
      have h' := hu_v₀ ⟨a, ha⟩
      rw [← h, hv₀1] at h'
      exact one_ne_zero h'
    have hsp : Submodule.span (ZMod 2) {P, u ⟨a, ha⟩} = commSpace (ρ a) := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le]
        rintro z (rfl | rfl)
        · exact hPA a ha ha1
        · exact hu_mem ⟨a, ha⟩
      · rw [finrank_span_pair hli, (hA.isTypeA (hAD a ha ha1)).2.2.2.1]
    rw [← hsp, Submodule.span_le]
    rintro z (rfl | rfl)
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · exact Submodule.mem_sup_left (hmemT ⟨a, ha⟩)
  have hle2 : T ⊔ (ZMod 2) ∙ P ≤ commSpaceOf ρ A := by
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact commSpace_le_commSpaceOf ρ a.2 (hu_mem a)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact commSpace_le_commSpaceOf ρ ha₀ (hPA a₀ ha₀ ha₀1)
  have hdisj : T ⊓ (ZMod 2) ∙ P = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvT, hvP⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a, rfl⟩ : v ∈ Set.range u := hvT
    rcases mem_span_singleton_iff.mp hvP with h | h
    · rw [h]
      exact Submodule.zero_mem _
    · have h' := hu_v₀ a
      rw [h, hv₀1] at h'
      exact absurd h' one_ne_zero
  have hdim : finrank (ZMod 2) (commSpaceOf ρ A) = finrank (ZMod 2) T + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq T ((ZMod 2) ∙ P)
    rw [hdisj, finrank_bot, finrank_span_singleton hP, add_zero] at h
    rw [le_antisymm hle1 hle2, h]
  rw [hdim, pow_succ, ← hfinT, hcardT, mul_comm]

theorem finrank_commSpaceOf_of_common_point (hA : A2Action D Q ρ)
    (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) (hA1 : A ≠ ⊥) {r : ℕ} (hr : Nat.card A = 2 ^ r) {P : V}
    (hP : P ≠ 0) (hPA : ∀ a ∈ A, a ≠ 1 → P ∈ commSpace (ρ a)) :
    finrank (ZMod 2) (commSpaceOf ρ A) = r + 1 := by
  have h := hA.card_commSpaceOf_of_common_point hAD hA1 hP hPA
  rw [hr, ← pow_succ'] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem commSpace_injOn (hA : A2Action D Q ρ) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) :
    Set.InjOn (fun a => commSpace (ρ a)) {a | a ∈ A ∧ a ≠ 1} := by
  rintro a ⟨ha, ha1⟩ b ⟨hb, hb1⟩ hab
  exact hA.eq_of_commSpace_eq (hAD a ha ha1) (hAD b hb hb1) hab

theorem common_point_or_finrank_le_three (hA : A2Action D Q ρ)
    (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) :
    (∃ P : V, P ≠ 0 ∧ ∀ a ∈ A, a ≠ 1 → P ∈ commSpace (ρ a)) ∨
      finrank (ZMod 2) (commSpaceOf ρ A) ≤ 3 := by
  have h2 : ∀ L ∈ (fun a => commSpace (ρ a)) '' {a | a ∈ A ∧ a ≠ 1},
      finrank (ZMod 2) L = 2 := by
    rintro _ ⟨a, ⟨ha, ha1⟩, rfl⟩
    exact (hA.isTypeA (hAD a ha ha1)).2.2.2.1
  have hmeet : ∀ L ∈ (fun a => commSpace (ρ a)) '' {a | a ∈ A ∧ a ≠ 1},
      ∀ M ∈ (fun a => commSpace (ρ a)) '' {a | a ∈ A ∧ a ≠ 1}, L ⊓ M ≠ ⊥ := by
    rintro _ ⟨a, ⟨ha, ha1⟩, rfl⟩ _ ⟨b, ⟨hb, hb1⟩, rfl⟩
    exact hA.inf_ne_bot_of_mem hAD ha hb ha1 hb1
  rcases concurrent_or_coplanar h2 hmeet with ⟨P, hP, hPL⟩ | ⟨W, hW, hle⟩
  · exact Or.inl ⟨P, hP, fun a ha ha1 => hPL _ ⟨a, ⟨ha, ha1⟩, rfl⟩⟩
  · refine Or.inr ((Submodule.finrank_mono ?_).trans hW)
    rw [commSpaceOf_le_iff]
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1, map_one, commSpace_eq_bot_iff.mpr rfl]
      exact bot_le
    · exact hle _ ⟨a, ⟨ha, ha1⟩, rfl⟩

theorem finrank_commSpaceOf_le_max (hA : A2Action D Q ρ) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D)
    {r : ℕ} (hr : Nat.card A = 2 ^ r) : finrank (ZMod 2) (commSpaceOf ρ A) ≤ max (r + 1) 3 := by
  rcases eq_or_ne A ⊥ with h | hA1
  · rw [h, commSpaceOf_bot, finrank_bot]
    exact Nat.zero_le _
  rcases hA.common_point_or_finrank_le_three hAD with ⟨P, hP, hPA⟩ | h
  · rw [hA.finrank_commSpaceOf_of_common_point hAD hA1 hr hP hPA]
    exact le_max_left _ _
  · exact h.trans (le_max_right _ _)

theorem exists_common_point (hA : A2Action D Q ρ) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D)
    (h8 : 8 < Nat.card A) : ∃ P : V, P ≠ 0 ∧ ∀ a ∈ A, a ≠ 1 → P ∈ commSpace (ρ a) := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hS : {a : X | a ∈ A ∧ a ≠ 1}.ncard = Nat.card A - 1 := by
    have e : {a : X | a ∈ A ∧ a ≠ 1} = (A : Set X) \ {1} := by
      ext a
      simp
    rw [e, Set.ncard_sdiff_singleton_of_mem (one_mem A), ← Nat.card_coe_set_eq]
    rfl
  have hL : ((fun a => commSpace (ρ a)) '' {a | a ∈ A ∧ a ≠ 1}).ncard = Nat.card A - 1 := by
    rw [(hA.commSpace_injOn hAD).ncard_image, hS]
  obtain ⟨P, hP, hPL⟩ := concurrent_of_eight_le_ncard (V := V)
    (𝓛 := (fun a => commSpace (ρ a)) '' {a | a ∈ A ∧ a ≠ 1})
    (by rintro _ ⟨a, ⟨ha, ha1⟩, rfl⟩; exact (hA.isTypeA (hAD a ha ha1)).2.2.2.1)
    (by
      rintro _ ⟨a, ⟨ha, ha1⟩, rfl⟩ _ ⟨b, ⟨hb, hb1⟩, rfl⟩
      exact hA.inf_ne_bot_of_mem hAD ha hb ha1 hb1)
    (by omega)
  exact ⟨P, hP, fun a ha ha1 => hPL _ ⟨a, ⟨ha, ha1⟩, rfl⟩⟩

theorem common_point_unique (hA : A2Action D Q ρ) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D)
    (h2 : 2 < Nat.card A) {P P' : V} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (hPA : ∀ a ∈ A, a ≠ 1 → P ∈ commSpace (ρ a))
    (hP'A : ∀ a ∈ A, a ≠ 1 → P' ∈ commSpace (ρ a)) : P = P' := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hS : {a : X | a ∈ A ∧ a ≠ 1}.ncard = Nat.card A - 1 := by
    have e : {a : X | a ∈ A ∧ a ≠ 1} = (A : Set X) \ {1} := by
      ext a
      simp
    rw [e, Set.ncard_sdiff_singleton_of_mem (one_mem A), ← Nat.card_coe_set_eq]
    rfl
  have hSfin : {a : X | a ∈ A ∧ a ≠ 1}.Finite := (Set.toFinite (A : Set X)).subset fun a h => h.1
  obtain ⟨a, b, ⟨ha, ha1⟩, ⟨hb, hb1⟩, hab⟩ := (Set.one_lt_ncard_iff hSfin).mp (by omega)
  have hne : commSpace (ρ a) ≠ commSpace (ρ b) := fun h =>
    hab (hA.commSpace_injOn hAD ⟨ha, ha1⟩ ⟨hb, hb1⟩ h)
  exact eq_of_mem_inf_of_ne (hA.isTypeA (hAD a ha ha1)).2.2.2.1
    (hA.isTypeA (hAD b hb hb1)).2.2.2.1 hne
    (Submodule.mem_inf.mpr ⟨hPA a ha ha1, hPA b hb hb1⟩)
    (Submodule.mem_inf.mpr ⟨hP'A a ha ha1, hP'A b hb hb1⟩) hP hP'

end A2Action

end CFSG.LargeExtraspecial.A2Mod
