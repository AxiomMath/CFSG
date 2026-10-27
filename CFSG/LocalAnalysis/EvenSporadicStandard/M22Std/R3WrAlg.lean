module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrGrp

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

namespace Wr

@[expose] def flag : Wr →* ℤˣ where
  toFun x := if x.e then -1 else 1
  map_one' := rfl
  map_mul' := by
    rintro ⟨a, b, e⟩ ⟨a', b', e'⟩
    cases e <;> cases e' <;> simp

theorem flag_eq_one_iff (x : Wr) : flag x = 1 ↔ x.e = false := by
  rcases x with ⟨a, b, e⟩
  cases e <;> simp [flag]

theorem flag_eq_neg_one_iff (x : Wr) : flag x = -1 ↔ x.e = true := by
  rcases x with ⟨a, b, e⟩
  cases e <;> simp [flag]

@[expose] def inclP : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6) →* Wr where
  toFun p := ⟨p.1, p.2, false⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def baseSub (A : Subgroup (Equiv.Perm (Fin 6))) : Subgroup Wr :=
  (A.prod A).map inclP

theorem mem_baseSub_iff {A : Subgroup (Equiv.Perm (Fin 6))} {x : Wr} :
    x ∈ baseSub A ↔ x.e = false ∧ x.a ∈ A ∧ x.b ∈ A := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨rfl, hp.1, hp.2⟩
  · rintro ⟨he, ha, hb⟩
    exact ⟨(x.a, x.b), ⟨ha, hb⟩, by rcases x with ⟨a, b, e⟩; cases he; rfl⟩

theorem baseSub_normal {A : Subgroup (Equiv.Perm (Fin 6))} (hA : A.Normal) :
    (baseSub A).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_baseSub_iff] at hx ⊢
  obtain ⟨he, ha, hb⟩ := hx
  rcases x with ⟨c, d, e⟩
  rcases g with ⟨p, q, ε⟩
  simp only at he ha hb
  subst he
  cases ε
  · simp only [Wr.mul_ff, Wr.inv_f]
    exact ⟨trivial, hA.conj_mem _ ha _, hA.conj_mem _ hb _⟩
  · simp only [Wr.inv_t, Wr.mul_def, Bool.not_false, ↓reduceIte, Bool.not_true]
    exact ⟨trivial, by simpa [mul_assoc] using hA.conj_mem _ hb p, by
      simpa [mul_assoc] using hA.conj_mem _ ha q⟩

@[expose] def leftSub (A : Subgroup (Equiv.Perm (Fin 6))) : Subgroup Wr :=
  (A.prod ⊥).map inclP

@[expose] def rightSub (A : Subgroup (Equiv.Perm (Fin 6))) : Subgroup Wr :=
  ((⊥ : Subgroup (Equiv.Perm (Fin 6))).prod A).map inclP

theorem mem_leftSub_iff {A : Subgroup (Equiv.Perm (Fin 6))} {x : Wr} :
    x ∈ leftSub A ↔ x.e = false ∧ x.a ∈ A ∧ x.b = 1 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨rfl, hp.1, Subgroup.mem_bot.1 hp.2⟩
  · rintro ⟨he, ha, hb⟩
    exact ⟨(x.a, x.b), ⟨ha, Subgroup.mem_bot.2 hb⟩, by rcases x with ⟨a, b, e⟩; cases he; rfl⟩

theorem mem_rightSub_iff {A : Subgroup (Equiv.Perm (Fin 6))} {x : Wr} :
    x ∈ rightSub A ↔ x.e = false ∧ x.a = 1 ∧ x.b ∈ A := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨rfl, Subgroup.mem_bot.1 hp.1, hp.2⟩
  · rintro ⟨he, ha, hb⟩
    exact ⟨(x.a, x.b), ⟨Subgroup.mem_bot.2 ha, hb⟩, by rcases x with ⟨a, b, e⟩; cases he; rfl⟩

theorem leftSub_le_baseSub (A : Subgroup (Equiv.Perm (Fin 6))) : leftSub A ≤ baseSub A := by
  intro x hx
  rw [mem_leftSub_iff] at hx
  rw [mem_baseSub_iff]
  exact ⟨hx.1, hx.2.1, hx.2.2 ▸ A.one_mem⟩

theorem rightSub_le_baseSub (A : Subgroup (Equiv.Perm (Fin 6))) : rightSub A ≤ baseSub A := by
  intro x hx
  rw [mem_rightSub_iff] at hx
  rw [mem_baseSub_iff]
  exact ⟨hx.1, hx.2.1 ▸ A.one_mem, hx.2.2⟩

theorem leftSub_comm_rightSub (A : Subgroup (Equiv.Perm (Fin 6))) {x y : Wr} (hx : x ∈ leftSub A)
    (hy : y ∈ rightSub A) : x * y = y * x := by
  rw [mem_leftSub_iff] at hx
  rw [mem_rightSub_iff] at hy
  rcases x with ⟨a, b, e⟩
  rcases y with ⟨a', b', e'⟩
  simp only at hx hy
  obtain ⟨he, -, hb⟩ := hx
  obtain ⟨he', ha', -⟩ := hy
  subst he he' hb ha'
  simp

theorem baseSub_le_sup (A : Subgroup (Equiv.Perm (Fin 6))) {x : Wr} (hx : x ∈ baseSub A) :
    x = ⟨x.a, 1, false⟩ * ⟨1, x.b, false⟩ := by
  rw [mem_baseSub_iff] at hx
  rcases x with ⟨a, b, e⟩
  simp only at hx ⊢
  obtain ⟨rfl, -, -⟩ := hx
  simp

end Wr

end CFSG.EvenSporadicStandard.M22Std
