module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Subgroup

variable {M : Type*} [Group M]

private theorem join_comm_aux {A B : Subgroup M} (h : A ≤ centralizer (B : Set M)) :
    ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n =>
  (h m.2 n n.2).symm

private theorem join_range {A B : Subgroup M} (h : A ≤ centralizer (B : Set M)) :
    (MonoidHom.noncommCoprod A.subtype B.subtype (join_comm_aux h)).range = A ⊔ B := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (join_comm_aux h)
  rwa [Subgroup.range_subtype, Subgroup.range_subtype] at hr

private theorem join_facts {A B : Subgroup M} {p : ℕ} (h : A ≤ centralizer (B : Set M))
    (hAB : A ⊓ B = ⊥) (hA : IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1)
    (hB : IsMulCommutative B ∧ ∀ x ∈ B, x ^ p = 1) :
    IsMulCommutative (A ⊔ B : Subgroup M) ∧ (∀ x ∈ A ⊔ B, x ^ p = 1) ∧
      (Finite A → Finite B → Nat.card (A ⊔ B : Subgroup M) = Nat.card A * Nat.card B) := by
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype (join_comm_aux h) with hφ
  have hrange := join_range h
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hAB
  obtain ⟨hAc, hAe⟩ := hA
  obtain ⟨hBc, hBe⟩ := hB
  refine ⟨⟨⟨?_⟩⟩, ?_, ?_⟩
  · intro x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    rw [← hrange] at hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    apply Subtype.ext
    show φ u * φ v = φ v * φ u
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (congrArg Subtype.val (hAc.is_comm.comm u.1 v.1))
    · exact Subtype.ext (congrArg Subtype.val (hBc.is_comm.comm u.2 v.2))
  · intro x hx
    rw [← hrange] at hx
    obtain ⟨u, rfl⟩ := hx
    rw [← map_pow]
    have : u ^ p = 1 := Prod.ext (Subtype.ext (hAe _ u.1.2 |> fun h' => by simpa using h'))
      (Subtype.ext (hBe _ u.2.2 |> fun h' => by simpa using h'))
    rw [this, map_one]
  · intro hAf hBf
    have e : (A × B) ≃ (A ⊔ B : Subgroup M) :=
      (MonoidHom.ofInjective hinj).toEquiv.trans (MulEquiv.subgroupCongr hrange).toEquiv
    rw [← Nat.card_prod, Nat.card_congr e]

theorem exists_elemAbelian_join
    {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {I : Type*} [Fintype I] (Y E : I → Subgroup M) (C0 : Subgroup M) (q : ℕ)
    (hYcomm : ∀ i j, i ≠ j → Y i ≤ Subgroup.centralizer (Y j : Set M))
    (hEY : ∀ i, E i ≤ Y i)
    (hYz : ∀ i, ∀ y ∈ Y i, (∀ y' ∈ Y i, y * y' = y' * y) → y = 1)
    (hCY : ∀ i, C0 ≤ Subgroup.centralizer (Y i : Set M))
    (hC : IsMulCommutative C0 ∧ ∀ x ∈ C0, x ^ p = 1)
    (hE : ∀ i, IsMulCommutative (E i) ∧ (∀ x ∈ E i, x ^ p = 1) ∧ Nat.card (E i) = p ^ q) :
    ∃ P : Subgroup M, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card C0 * p ^ (q * Fintype.card I) ∧
      ∀ T : Subgroup M, C0 ≤ Subgroup.centralizer (T : Set M) →
        (∀ i, E i ≤ Subgroup.centralizer (T : Set M)) → P ≤ Subgroup.centralizer (T : Set M) := by
  classical
  have key : ∀ s : Finset I, IsMulCommutative (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ∧
      (∀ x ∈ (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M), x ^ p = 1) ∧
      Nat.card (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) = Nat.card C0 * p ^ (q * s.card) ∧
      ∀ j ∉ s, (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ≤ centralizer (Y j : Set M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset I), E i : Subgroup M) = ⊥ := by simp
      rw [h0, sup_bot_eq]
      exact ⟨hC.1, hC.2, by simp, fun j _ => hCY j⟩
    | insert j s hj ih =>
      obtain ⟨ihc, ihe, ihn, ihy⟩ := ih
      have hJ : (C0 ⊔ ⨆ i ∈ insert j s, E i : Subgroup M) =
          (C0 ⊔ ⨆ i ∈ s, E i) ⊔ E j := by
        rw [Finset.iSup_insert, sup_comm (E j), sup_assoc]
      have hle : (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ≤ centralizer (E j : Set M) :=
        (ihy j hj).trans (Subgroup.centralizer_le (hEY j))
      have hinf : (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ⊓ E j = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        rw [Subgroup.mem_bot]
        refine hYz j y (hEY j hy.2) fun y' hy' => ?_
        exact (ihy j hj hy.1 y' hy').symm
      obtain ⟨hc, he, hn⟩ := join_facts hle hinf ⟨ihc, ihe⟩ ⟨(hE j).1, (hE j).2.1⟩
      rw [hJ]
      refine ⟨hc, he, ?_, ?_⟩
      · rw [hn inferInstance inferInstance, ihn, (hE j).2.2, Finset.card_insert_of_notMem hj]
        rw [mul_add_one, pow_add, mul_assoc]
      · intro i hi
        rw [Finset.mem_insert, not_or] at hi
        exact sup_le (ihy i hi.2) ((hEY j).trans (hYcomm j i (Ne.symm hi.1)))
  obtain ⟨hc, he, hn, -⟩ := key Finset.univ
  refine ⟨C0 ⊔ ⨆ i ∈ (Finset.univ : Finset I), E i, hc, he, ?_, ?_⟩
  · rw [hn, Finset.card_univ]
  · intro T hC0 hET
    exact sup_le hC0 (iSup₂_le fun i _ => hET i)

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
