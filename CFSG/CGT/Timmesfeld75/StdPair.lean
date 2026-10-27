module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

section Transvections

variable (n : ℕ) (K : Type) [Field K]

theorem one_add_vecMulVec_mul_center (c a b : Fin n → K) (h : a ⬝ᵥ c = 0) :
    (1 + vecMulVec c a) * (1 + vecMulVec c b) = 1 + vecMulVec c (a + b) := by
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero, add_zero,
    vecMulVec_add]
  abel

theorem one_add_vecMulVec_mul_axis (a v w : Fin n → K) (h : a ⬝ᵥ w = 0) :
    (1 + vecMulVec v a) * (1 + vecMulVec w a) = 1 + vecMulVec (v + w) a := by
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero, add_zero,
    add_vecMulVec]
  abel

@[expose] def transvCenter (c : Fin n → K) : Subgroup (GL (Fin n) K) where
  carrier := {g | ∃ a : Fin n → K, a ⬝ᵥ c = 0 ∧
    (g : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec c a}
  one_mem' := ⟨0, by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨a, ha, hg⟩ ⟨b, hb, hh⟩
    refine ⟨a + b, by simp [ha, hb], ?_⟩
    rw [Units.val_mul, hg, hh, one_add_vecMulVec_mul_center n K c a b ha]
  inv_mem' := by
    rintro g ⟨a, ha, hg⟩
    refine ⟨-a, by simp [ha], ?_⟩
    rw [Matrix.coe_units_inv, hg]
    apply Matrix.inv_eq_right_inv
    rw [one_add_vecMulVec_mul_center n K c a (-a) ha, add_neg_cancel, vecMulVec_zero, add_zero]

@[expose] def transvAxis (a : Fin n → K) : Subgroup (GL (Fin n) K) where
  carrier := {g | ∃ v : Fin n → K, a ⬝ᵥ v = 0 ∧
    (g : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec v a}
  one_mem' := ⟨0, by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨v, hv, hg⟩ ⟨w, hw, hh⟩
    refine ⟨v + w, by simp [dotProduct_add, hv, hw], ?_⟩
    rw [Units.val_mul, hg, hh, one_add_vecMulVec_mul_axis n K a v w hw]
  inv_mem' := by
    rintro g ⟨v, hv, hg⟩
    refine ⟨-v, by simp [hv], ?_⟩
    rw [Matrix.coe_units_inv, hg]
    apply Matrix.inv_eq_right_inv
    rw [one_add_vecMulVec_mul_axis n K a v (-v) (by simp [hv]), add_neg_cancel, zero_vecMulVec,
      add_zero]

@[expose] def transvImage (U : Subgroup (GL (Fin n) K)) : Subgroup (StatedProj (StatedSL n K)) :=
  (U.subgroupOf (StatedSL n K)).map (QuotientGroup.mk' _)

end Transvections

@[expose] def ConjTwoTransitive (G : Type) [Group G] (T : Subgroup G) : Prop :=
  ∀ a b c d : G, conjSubgroup a T ≠ conjSubgroup b T → conjSubgroup c T ≠ conjSubgroup d T →
    ∃ g : G, conjSubgroup (g * a) T = conjSubgroup c T ∧ conjSubgroup (g * b) T = conjSubgroup d T

@[expose] def BorelTwoTransitive (G : Type) [Group G] (T : Subgroup G) : Prop :=
  ConjTwoTransitive G T ∧ ∃ S : Sylow 2 G, Subgroup.normalizer (T : Set G) =
    Subgroup.normalizer ((S : Subgroup G) : Set G)

@[expose] def StdPair (G : Type) [Group G] (T : Subgroup G) : Prop :=
  ListGroup G ∧
  (∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y) ∧
  (∀ f : ℕ, StatedClassicalModel G .PSL 2 2 f →
    Nat.card T = 2 ^ f ∧ (∃ S : Sylow 2 G, (S : Subgroup G) = T) ∧ BorelTwoTransitive G T) ∧
  (∀ m f : ℕ, 3 ≤ m → ∀ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f →
    ∀ e : G ≃* StatedProj (StatedSL m K), Nat.card T = 2 ^ (f * (m - 1)) ∧
      ((∃ c : Fin m → K, c ≠ 0 ∧ T.map e.toMonoidHom = transvImage m K (transvCenter m K c)) ∨
       (∃ a : Fin m → K, a ≠ 0 ∧ T.map e.toMonoidHom = transvImage m K (transvAxis m K a)))) ∧
  (∀ s : ℕ, Odd s → 3 ≤ s → CFSG.Blueprint.LieModel G .twistedB2 0 2 s →
    Nat.card T = 2 ^ s ∧
      (∃ S : Sylow 2 G, T = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) ∧
      BorelTwoTransitive G T) ∧
  (∀ s : ℕ, 2 ≤ s → StatedClassicalModel G .PSU 3 2 s →
    Nat.card T = 2 ^ s ∧
      (∃ S : Sylow 2 G, T = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) ∧
      BorelTwoTransitive G T) ∧
  (∀ k : ℕ, 6 ≤ k → k ≤ 9 → Nonempty (G ≃* alternatingGroup (Fin k)) →
    Nat.card T = if k ≤ 7 then 4 else 8) ∧
  (CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨
    CFSG.Blueprint.NativeSporadic.IsSporadic G .M23 ∨
    CFSG.Blueprint.NativeSporadic.IsSporadic G .M24 → Nat.card T = 16)

@[expose] def ListWCIdentification : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ] [IsSimpleGroup Λ], ListGroup Λ →
    ∀ S : Subgroup Λ, IsWC S → 4 ≤ Nat.card S → StdPair Λ S

theorem StdPair.listGroup {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T) :
    ListGroup G :=
  h.1

theorem StdPair.transitive {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y :=
  h.2.1

theorem StdPair.of_psl2 {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T) {f : ℕ}
    (hf : StatedClassicalModel G .PSL 2 2 f) :
    Nat.card T = 2 ^ f ∧ (∃ S : Sylow 2 G, (S : Subgroup G) = T) ∧ BorelTwoTransitive G T :=
  h.2.2.1 f hf

theorem StdPair.of_psl {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T) {m f : ℕ}
    (hm : 3 ≤ m) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : G ≃* StatedProj (StatedSL m K)) :
    Nat.card T = 2 ^ (f * (m - 1)) ∧
      ((∃ c : Fin m → K, c ≠ 0 ∧ T.map e.toMonoidHom = transvImage m K (transvCenter m K c)) ∨
       (∃ a : Fin m → K, a ≠ 0 ∧ T.map e.toMonoidHom = transvImage m K (transvAxis m K a))) :=
  h.2.2.2.1 m f hm K inferInstance inferInstance hK e

theorem StdPair.of_sz {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T) {s : ℕ}
    (hs : Odd s) (hs3 : 3 ≤ s) (hG : CFSG.Blueprint.LieModel G .twistedB2 0 2 s) :
    Nat.card T = 2 ^ s ∧
      (∃ S : Sylow 2 G, T = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) ∧
      BorelTwoTransitive G T :=
  h.2.2.2.2.1 s hs hs3 hG

theorem StdPair.of_psu3 {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T) {s : ℕ}
    (hs : 2 ≤ s) (hG : StatedClassicalModel G .PSU 3 2 s) :
    Nat.card T = 2 ^ s ∧
      (∃ S : Sylow 2 G, T = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) ∧
      BorelTwoTransitive G T :=
  h.2.2.2.2.2.1 s hs hG

theorem StdPair.card_alternating {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T) {k : ℕ}
    (hk6 : 6 ≤ k) (hk9 : k ≤ 9) (hG : Nonempty (G ≃* alternatingGroup (Fin k))) :
    Nat.card T = if k ≤ 7 then 4 else 8 :=
  h.2.2.2.2.2.2.1 k hk6 hk9 hG

theorem StdPair.card_sporadic {G : Type} [Group G] {T : Subgroup G} (h : StdPair G T)
    (hG : CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M24) : Nat.card T = 16 :=
  h.2.2.2.2.2.2.2 hG

end CFSG.CGT.Timmesfeld75
