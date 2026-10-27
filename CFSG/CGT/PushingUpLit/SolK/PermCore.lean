module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.CGT.PushingUpLit.SolK

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def stabAlt (o : α) : Subgroup (Perm α) :=
  alternatingGroup α ⊓ MulAction.stabilizer (Perm α) o

theorem mem_stabAlt {o : α} {σ : Perm α} : σ ∈ stabAlt o ↔ sign σ = 1 ∧ σ o = o := by
  simp [stabAlt, Equiv.Perm.mem_alternatingGroup, MulAction.mem_stabilizer_iff]

theorem mem_stabAlt_of_isThreeCycle {o : α} {σ : Perm α} (h3 : σ.IsThreeCycle) (ho : σ o = o) :
    σ ∈ stabAlt o :=
  mem_stabAlt.2 ⟨h3.sign, ho⟩

theorem stabAlt_le_closure_threeCycles (o : α) :
    stabAlt o ≤ Subgroup.closure {σ : Perm α | σ.IsThreeCycle ∧ σ o = o} := by
  intro h hh
  rw [mem_stabAlt] at hh
  let p : α → Prop := fun x => x ≠ o
  have hp : ∀ x, p (h x) ↔ p x := fun x => by
    simp only [p, ne_eq]
    constructor
    · intro hx hxo
      exact hx (by rw [hxo, hh.2])
    · intro hx hxo
      apply hx
      have : h x = h o := by rw [hxo, hh.2]
      exact h.injective this
  have hfix : ∀ x, h x ≠ x → p x := fun x hx hxo => hx (by rw [hxo, hh.2])
  have h1 : ofSubtype (h.subtypePerm hp) = h := ofSubtype_subtypePerm hp hfix
  have h2 : h.subtypePerm hp ∈ alternatingGroup {x // p x} := by
    rw [mem_alternatingGroup, sign_subtypePerm h hp hfix]
    exact hh.1
  rw [← closure_three_cycles_eq_alternating] at h2
  rw [← h1]
  refine Subgroup.closure_induction (p := fun x _ => ofSubtype x ∈
    Subgroup.closure {σ : Perm α | σ.IsThreeCycle ∧ σ o = o}) ?_ ?_ ?_ ?_ h2
  · intro x hx
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · show (ofSubtype x).cycleType = {3}
      rw [cycleType_ofSubtype]
      exact hx
    · exact ofSubtype_apply_of_not_mem x (by simp [p])
  · simp only [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

theorem hom_stabAlt_eq_one (o : α) {K : Type*} [Group K] (hK : ∀ k : K, k ^ 2 = 1)
    (f : ↥(stabAlt o) →* K) (h : ↥(stabAlt o)) : f h = 1 := by
  set N : Subgroup (Perm α) := f.ker.map (stabAlt o).subtype with hN
  have hS : {σ : Perm α | σ.IsThreeCycle ∧ σ o = o} ⊆ N := by
    rintro σ ⟨h3, ho⟩
    have hmem : σ ∈ stabAlt o := mem_stabAlt_of_isThreeCycle h3 ho
    refine ⟨⟨σ, hmem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hord : σ ^ 3 = 1 := by rw [← h3.orderOf]; exact pow_orderOf_eq_one σ
    have hsq : σ = (σ ^ 2) ^ 2 := by
      calc σ = σ * σ ^ 3 := by rw [hord, mul_one]
        _ = (σ ^ 2) ^ 2 := by group
    have h2mem : σ ^ 2 ∈ stabAlt o := (stabAlt o).pow_mem hmem 2
    have : (⟨σ, hmem⟩ : ↥(stabAlt o)) = (⟨σ ^ 2, h2mem⟩ : ↥(stabAlt o)) ^ 2 :=
      Subtype.ext (by simpa using hsq)
    rw [this, map_pow]
    exact hK _
  have hle : Subgroup.closure {σ : Perm α | σ.IsThreeCycle ∧ σ o = o} ≤ N :=
    (Subgroup.closure_le N).2 hS
  obtain ⟨x, hx, hxh⟩ := hle (stabAlt_le_closure_threeCycles o h.2)
  have : x = h := Subtype.ext hxh
  rw [← this]
  exact hx

end CFSG.CGT.PushingUpLit.SolK
