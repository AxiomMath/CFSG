module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812PermDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Equiv Equiv.Perm Subgroup

private def FixedBy (V : Subgroup (Perm (Fin 11))) (x : Fin 11) : Prop := ∀ v ∈ V, v x = x

private theorem fixedBy_stable {T V : Subgroup (Perm (Fin 11))}
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11)))) {t : Perm (Fin 11)} (ht : t ∈ T)
    {x : Fin 11} (hx : FixedBy V x) : FixedBy V (t x) := by
  intro v hv
  have hmem : t⁻¹ * v * t ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (hn (T.inv_mem ht)) v).mp hv
    simpa using this
  have h1 := hx _ hmem
  rwa [Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq] at h1

private theorem fixedBy_iff {T V : Subgroup (Perm (Fin 11))}
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11)))) {t : Perm (Fin 11)} (ht : t ∈ T)
    (x : Fin 11) : FixedBy V (t x) ↔ FixedBy V x :=
  ⟨fun h => by simpa using fixedBy_stable hn (T.inv_mem ht) h, fixedBy_stable hn ht⟩

private theorem fix_cases (y : Fin 11) : y.val < 8 ∨ (y = 8 ∨ y = 9) ∨ y = 10 := by
  revert y; decide

private theorem fixedBy_key {T V : Subgroup (Perm (Fin 11))} (hT : SylData T)
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11)))) (x : Fin 11) :
    FixedBy V x ↔ ((x.val < 8 ∧ FixedBy V 0) ∨ ((x = 8 ∨ x = 9) ∧ FixedBy V 8) ∨
      (x = 10 ∧ FixedBy V 10)) := by
  rcases fix_cases x with hx | hx | rfl
  · obtain ⟨t, ht, htx⟩ := hT.trans8 0 x (by decide) hx
    have e : FixedBy V x ↔ FixedBy V 0 := by
      have := fixedBy_iff hn ht 0
      rwa [htx] at this
    have n : ∀ y : Fin 11, y.val < 8 → ¬ (y = 8 ∨ y = 9) ∧ y ≠ 10 := by decide
    constructor
    · exact fun h => Or.inl ⟨hx, e.mp h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact e.mpr h
      · exact absurd h (n x hx).1
      · exact absurd h (n x hx).2
  · have e : FixedBy V x ↔ FixedBy V 8 := by
      rcases hx with rfl | rfl
      · exact Iff.rfl
      · obtain ⟨t, ht, ht8⟩ := hT.swap89
        have := fixedBy_iff hn ht 8
        rwa [ht8] at this
    have n : ∀ y : Fin 11, (y = 8 ∨ y = 9) → ¬ y.val < 8 ∧ y ≠ 10 := by decide
    constructor
    · exact fun h => Or.inr (Or.inl ⟨hx, e.mp h⟩)
    · rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h (n x hx).1
      · exact e.mpr h
      · exact absurd h (n x hx).2
  · constructor
    · exact fun h => Or.inr (Or.inr ⟨rfl, h⟩)
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h

private def fixSet (b0 b8 b10 : Bool) : Finset (Fin 11) :=
  Finset.univ.filter fun x =>
    (x.val < 8 ∧ b0 = true) ∨ ((x = 8 ∨ x = 9) ∧ b8 = true) ∨ (x = 10 ∧ b10 = true)

private theorem fixSet_cases : ∀ b0 b8 b10 : Bool, 11 ≡ (fixSet b0 b8 b10).card [MOD 3] →
    (b0 = true ∧ b8 = false ∧ b10 = false) ∨ (b0 = false ∧ b8 = true ∧ b10 = false) ∨
      (b0 = true ∧ b8 = true ∧ b10 = true) := by
  decide

private theorem fixedBy_card {V : Subgroup (Perm (Fin 11))} (hV : IsPGroup 3 ↥V) :
    ∃ S : Finset (Fin 11), (∀ x, x ∈ S ↔ FixedBy V x) ∧ 11 ≡ S.card [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := IsPGroup.card_modEq_card_fixedPoints hV (Fin 11)
  rw [Nat.card_fin, Nat.card_eq_card_toFinset] at hmod
  refine ⟨(MulAction.fixedPoints ↥V (Fin 11)).toFinset, fun x => ?_, hmod⟩
  rw [Set.mem_toFinset, MulAction.mem_fixedPoints]
  constructor
  · intro h v hv
    exact h ⟨v, hv⟩
  · intro h m
    exact h m m.2

theorem fixDichotomy_of_sylData {T : Subgroup (Perm (Fin 11))} (hT : SylData T) :
    FixDichotomy T := by
  intro V hV hV1 hn
  classical
  obtain ⟨S, hS, hmod⟩ := fixedBy_card hV
  have hSeq : S = fixSet (decide (FixedBy V 0)) (decide (FixedBy V 8))
      (decide (FixedBy V 10)) := by
    ext x
    rw [hS, fixedBy_key hT hn x]
    simp [fixSet]
  rw [hSeq] at hmod
  have hb := fixSet_cases _ _ _ hmod
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb
  rcases hb with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · left
    intro x
    show FixedBy V x ↔ x.val < 8
    have := fixedBy_key hT hn x
    simp only [a, b, c] at this
    simpa using this
  · right
    intro x
    show FixedBy V x ↔ x = 8 ∨ x = 9
    have := fixedBy_key hT hn x
    simp only [a, b, c] at this
    simpa using this
  · exfalso
    have hall : ∀ x, FixedBy V x := fun x => by
      rw [fixedBy_key hT hn x]
      rcases fix_cases x with h | h | h
      · exact Or.inl ⟨h, a⟩
      · exact Or.inr (Or.inl ⟨h, b⟩)
      · exact Or.inr (Or.inr ⟨h, c⟩)
    refine hV1 ((Subgroup.eq_bot_iff_forall V).mpr fun v hv => Equiv.ext fun x => ?_)
    simpa using hall x v hv

private theorem fix_eq_of {σ π : Perm (Fin 11)} (h : ∀ x : Fin 11, x.val < 8 → σ x = x)
    (hπ : ∀ x : Fin 11, x.val < 8 → π x = x) {a b c : Fin 11}
    (e8 : σ 8 = a) (e9 : σ 9 = b) (e10 : σ 10 = c)
    (p8 : π 8 = a) (p9 : π 9 = b) (p10 : π 10 = c) : σ = π := by
  ext x
  by_cases hx : x.val < 8
  · rw [h x hx, hπ x hx]
  · have hc : ∀ y : Fin 11, ¬ y.val < 8 → y = 8 ∨ y = 9 ∨ y = 10 := by decide
    rcases hc x hx with rfl | rfl | rfl
    · rw [e8, p8]
    · rw [e9, p9]
    · rw [e10, p10]

private theorem fix_mem_zpowers {σ : Perm (Fin 11)} (hs : sign σ = 1)
    (h : ∀ x : Fin 11, x.val < 8 → σ x = x) : σ ∈ zpowers c3 := by
  have hge : ∀ y : Fin 11, 8 ≤ y.val → 8 ≤ (σ y).val := by
    intro y hy
    by_contra hlt
    push Not at hlt
    have h2 : σ y = y := σ.injective (h _ hlt)
    rw [h2] at hlt
    omega
  have hcase : ∀ y : Fin 11, 8 ≤ y.val → y = 8 ∨ y = 9 ∨ y = 10 := by decide
  rcases hcase _ (hge 8 (by decide)) with e8 | e8 | e8 <;>
  rcases hcase _ (hge 9 (by decide)) with e9 | e9 | e9 <;>
  rcases hcase _ (hge 10 (by decide)) with e10 | e10 | e10
  all_goals first
    | exact absurd (σ.injective (e8.trans e9.symm)) (by decide)
    | exact absurd (σ.injective (e8.trans e10.symm)) (by decide)
    | exact absurd (σ.injective (e9.trans e10.symm)) (by decide)
    | (rw [fix_eq_of (π := 1) h (by decide) e8 e9 e10 (by decide) (by decide) (by decide)]
       exact one_mem _)
    | (rw [fix_eq_of (π := c3) h (by decide) e8 e9 e10 (by decide) (by decide) (by decide)]
       exact mem_zpowers _)
    | (rw [fix_eq_of (π := c3⁻¹) h (by decide) e8 e9 e10 (by decide) (by decide) (by decide)]
       exact inv_mem (mem_zpowers _))
    | (rw [fix_eq_of (π := swap 8 9) h (by decide) e8 e9 e10 (by decide) (by decide) (by decide),
         sign_swap (by decide)] at hs
       exact absurd hs (by decide))
    | (rw [fix_eq_of (π := swap 8 10) h (by decide) e8 e9 e10 (by decide) (by decide) (by decide),
         sign_swap (by decide)] at hs
       exact absurd hs (by decide))
    | (rw [fix_eq_of (π := swap 9 10) h (by decide) e8 e9 e10 (by decide) (by decide) (by decide),
         sign_swap (by decide)] at hs
       exact absurd hs (by decide))

theorem eq_zpowers_c3_of_fix8 {V : Subgroup (Perm (Fin 11))}
    (hAlt : V ≤ alternatingGroup (Fin 11)) (hV1 : V ≠ ⊥)
    (hfix : ∀ x : Fin 11, x.val < 8 → ∀ v ∈ V, v x = x) : V = zpowers c3 := by
  have hle : V ≤ zpowers c3 := fun v hv =>
    fix_mem_zpowers (mem_alternatingGroup.mp (hAlt hv)) (fun x hx => hfix x hx v hv)
  have hdvd : Nat.card V ∣ 3 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [card_zpowers_c3] at this
  have h3 : Nat.card V = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hV1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_zpowers_c3, h3])

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
