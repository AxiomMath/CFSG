module

public import CFSG.ClassicalInvolution.Uniform.UThmStmtB

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups

section IH8

variable (p f : ℕ) [Fact p.Prime]

structure IH8T (n : ℕ) : Prop where
  thm2 : Thm2BelowU p f n
  thm4 : Thm4BelowU p f n
  thm5 : Thm5BelowU p f n
  thm6 : Thm6TypedBelowU p f n
  thm7 : Thm7TypedBelowU p f n
  thm8 : Thm8TypedBelowU p f n
  muTable : MuTableBelowU p f n
  thm3 : Thm3TypedBelowExactU p f n

@[expose] def IH8AllT (n : ℕ) : Prop :=
  ∀ e : ℕ, 3 ≤ p ^ e → IH8T p e n

variable {p f}

theorem ih8T_iff (h3 : p ^ f ≠ 3) (n : ℕ) : IH8T p f n ↔ IH8 p f n :=
  ⟨fun h => ⟨(thm2BelowU_iff h3 n).mp h.thm2, (thm4BelowU_iff h3 n).mp h.thm4,
      (thm5BelowU_iff h3 n).mp h.thm5, (thm6TypedBelowU_iff h3 n).mp h.thm6,
      (thm7TypedBelowU_iff h3 n).mp h.thm7, (thm8TypedBelowU_iff h3 n).mp h.thm8,
      (muTableBelowU_iff h3 n).mp h.muTable, (thm3TypedBelowExactU_iff h3 n).mp h.thm3⟩,
   fun h => ⟨(thm2BelowU_iff h3 n).mpr h.thm2, (thm4BelowU_iff h3 n).mpr h.thm4,
      (thm5BelowU_iff h3 n).mpr h.thm5, (thm6TypedBelowU_iff h3 n).mpr h.thm6,
      (thm7TypedBelowU_iff h3 n).mpr h.thm7, (thm8TypedBelowU_iff h3 n).mpr h.thm8,
      (muTableBelowU_iff h3 n).mpr h.muTable, (thm3TypedBelowExactU_iff h3 n).mpr h.thm3⟩⟩

theorem IH8T.toIH8U {n : ℕ} (h : IH8T p f n) : IH8U p f n :=
  fun hq => (ih8T_iff (by omega) n).mp h

theorem IH8AllT.toIH8AllU {n : ℕ} (h : IH8AllT p n) : IH8AllU p n :=
  fun e he => (h e he).toIH8U

theorem ih8AllT_iff_ih8All (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n : ℕ) : IH8AllT p n ↔ IH8All p n := by
  have key : ∀ e : ℕ, p ^ e ≠ 3 := fun e he =>
    hp3 (eq_three_one_of_pow_eq_three Fact.out he).1
  refine ⟨fun h e he => ?_, fun h e he => ?_⟩
  · exact (ih8T_iff (key e) n).mp (h e (by omega))
  · exact (ih8T_iff (key e) n).mpr (h e ((three_le_iff_five_le hp2 (key e)).mp he))

theorem ih8AllT_three_iff (n : ℕ) :
    IH8AllT 3 n ↔ IH8All 3 n ∧ IH8T 3 1 n := by
  refine ⟨fun h => ⟨fun e he => ?_, h 1 (by norm_num)⟩, fun ⟨h, h1⟩ e he => ?_⟩
  · have : (3 : ℕ) ^ e ≠ 3 := by
      intro h3
      have := (eq_three_one_of_pow_eq_three Nat.prime_three h3).2
      subst this
      omega
    exact (ih8T_iff this n).mp (h e (by omega))
  · by_cases h1e : e = 1
    · subst h1e
      exact h1
    · have he0 : e ≠ 0 := by rintro rfl; simp at he
      have h5 : 5 ≤ 3 ^ e := by
        calc 5 ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (ih8T_iff (by omega) n).mpr (h e h5)

end IH8

section Rest

variable (p f : ℕ) [Fact p.Prime]

@[expose] def IHInterfaceU : Prop :=
  ∀ n : ℕ, CITBelowT (.sl2 p f) n → Thm4BelowU p f n ∧ Thm2BelowU p f n

@[expose] def IH8RestU : Prop :=
  ∀ n : ℕ, CITBelowT (.sl2 p f) n →
    Thm5BelowU p f n ∧ Thm6TypedBelowU p f n ∧ Thm7TypedBelowU p f n ∧ Thm8TypedBelowU p f n ∧
      MuTableBelowU p f n ∧ Thm3TypedBelowExactU p f n

variable {p f}

theorem ih8T_of_rest (hI : IHInterfaceU p f) (h : IH8RestU p f) {n : ℕ}
    (hn : CITBelowT (.sl2 p f) n) : IH8T p f n :=
  have h24 := hI n hn
  have h5 := h n hn
  ⟨h24.2, h24.1, h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2.1, h5.2.2.2.2.2⟩

theorem ih8AllT_of_rest (hI : ∀ e : ℕ, 3 ≤ p ^ e → IHInterfaceU p e)
    (h : ∀ e : ℕ, 3 ≤ p ^ e → IH8RestU p e) {n : ℕ} (hn : CITBelowAllT p n) : IH8AllT p n :=
  fun e he => ih8T_of_rest (hI e he) (h e he) (hn e he)

theorem ihInterfaceU_iff (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : IHInterfaceU p f ↔ IHInterface p f := by
  have h3 : p ^ f ≠ 3 := by omega
  simp only [IHInterfaceU, IHInterface, citBelowT_iff_citBelowU hp2 hq, thm4BelowU_iff h3,
    thm2BelowU_iff h3]

theorem ih8RestU_iff (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : IH8RestU p f ↔ IH8Rest p f := by
  have h3 : p ^ f ≠ 3 := by omega
  simp only [IH8RestU, IH8Rest, citBelowT_iff_citBelowU hp2 hq, thm5BelowU_iff h3,
    thm6TypedBelowU_iff h3, thm7TypedBelowU_iff h3, thm8TypedBelowU_iff h3,
    muTableBelowU_iff h3, thm3TypedBelowExactU_iff h3]

end Rest

section Stand

variable (p f : ℕ) [Fact p.Prime]

structure AscStandT {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  odd : p ≠ 2
  three : 3 ≤ p ^ f
  hyp : HypOmegaModU (.sl2 p f) Ω
  below : CITBelowAllT p (Nat.card G)
  ih : IH8AllT p (Nat.card G)
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤

variable {p f} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}

theorem AscStandT.toAscStandU (h : AscStandT p f Ω K) : AscStandU p f Ω K where
  odd := h.odd
  three := h.three
  hyp := h.hyp
  below := h.below
  ih := h.ih.toIH8AllU
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen

theorem AscStandT.toAscStand (h : AscStandT p f Ω K) (hq : 5 ≤ p ^ f) : AscStand p f Ω K :=
  h.toAscStandU.toAscStand hq

theorem AscStandT.of_ascStand (hp3 : p ≠ 3) (h : AscStand p f Ω K) : AscStandT p f Ω K where
  odd := h.odd
  three := by have := h.five; omega
  hyp := (hypOmegaModU_iff_hypOmegaMod h.odd h.five).mpr h.hyp
  below := (citBelowAllT_iff_citBelowAll h.odd hp3 _).mpr h.below
  ih := (ih8AllT_iff_ih8All h.odd hp3 _).mpr h.ih
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen

end Stand

end CFSG.ClassicalInvolution.Uniform
