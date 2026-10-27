module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.KGroups.Checks

public section

namespace CFSG.ComponentClassification.RankTwoL33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : ℕ}

@[expose] def centList (L : List (Equiv.Perm (Fin n))) (s : Equiv.Perm (Fin n)) :
    List (Equiv.Perm (Fin n)) :=
  L.filter fun g => decide (g * s = s * g)

@[expose] def invList (L : List (Equiv.Perm (Fin n))) : List (Equiv.Perm (Fin n)) :=
  L.filter fun g => decide (g ^ 2 = 1) && decide (g ≠ 1)

@[expose] def cent48Check (LP : List (Equiv.Perm (Fin n))) : Bool :=
  (invList LP).all fun s => decide ((centList LP s).length = 48)

@[expose] def order13Pair (Cs Cb : List (Equiv.Perm (Fin n))) : Bool :=
  Cs.any fun c₁ => Cb.any fun c₂ => decide ((c₁ * c₂) ^ 13 = 1) && decide (c₁ * c₂ ≠ 1)

@[expose] def order13Check (LA LP : List (Equiv.Perm (Fin n))) : Bool :=
  let I := invList LA
  I.all fun s =>
    let Cs := centList LP s
    bif decide (Cs.length = 48) then
      I.all fun b => bif decide (b ≠ s) && decide (b * s = s * b) then
        order13Pair Cs (centList LP b) else true
    else true

@[expose] def fourGenCheck (LA LP : List (Equiv.Perm (Fin n))) : Bool :=
  cent48Check LP && order13Check LA LP

theorem mem_invList {L : List (Equiv.Perm (Fin n))} {g : Equiv.Perm (Fin n)} :
    g ∈ invList L ↔ g ∈ L ∧ g ^ 2 = 1 ∧ g ≠ 1 := by
  simp [invList]

theorem mem_centList {L : List (Equiv.Perm (Fin n))} {s g : Equiv.Perm (Fin n)} :
    g ∈ centList L s ↔ g ∈ L ∧ g * s = s * g := by
  simp [centList]

theorem fourGenCheck_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (h : fourGenCheck (elemsT QA) (elemsT QP) = true) :
    (∀ s ∈ QP.originalSubgroup, s ^ 2 = 1 → s ≠ 1 →
      Nat.card ↥(QP.originalSubgroup ⊓
        Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin n)))) = 48) ∧
    (∀ s ∈ QA.originalSubgroup, s ^ 2 = 1 → s ≠ 1 →
      Nat.card ↥(QP.originalSubgroup ⊓
        Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin n)))) = 48 →
      ∀ b ∈ QA.originalSubgroup, b ^ 2 = 1 → b ≠ 1 → b ≠ s → b * s = s * b →
      ∃ c₁ ∈ QP.originalSubgroup ⊓ Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin n))),
      ∃ c₂ ∈ QP.originalSubgroup ⊓ Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin n))),
        (c₁ * c₂) ^ 13 = 1 ∧ c₁ * c₂ ≠ 1) := by
  simp only [fourGenCheck, Bool.and_eq_true] at h
  obtain ⟨h48, h13⟩ := h
  refine ⟨fun s hs hs2 hs1 => ?_, fun s hs hs2 hs1 hcs b hb hb2 hb1 hbs hcomm => ?_⟩
  · have h1 := List.all_eq_true.1 h48 s
      (mem_invList.2 ⟨(mem_elemsT QP hQP s).2 hs, hs2, hs1⟩)
    rw [card_inf_centralizer QP hQP s]
    exact of_decide_eq_true h1
  · have hcs' : (centList (elemsT QP) s).length = 48 := by
      rw [card_inf_centralizer QP hQP s] at hcs
      exact hcs
    have h1 := List.all_eq_true.1 h13 s
      (mem_invList.2 ⟨(mem_elemsT QA hQA s).2 hs, hs2, hs1⟩)
    simp only at h1
    have h2 := (bif_imp _ _).1 h1 (by simp [hcs'])
    have h3 := (bif_imp _ _).1 (List.all_eq_true.1 h2 b
      (mem_invList.2 ⟨(mem_elemsT QA hQA b).2 hb, hb2, hb1⟩)) (by simp [hbs, hcomm])
    simp only [order13Pair, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h3
    obtain ⟨c₁, hc₁, c₂, hc₂, h13', h1'⟩ := h3
    rw [mem_centList] at hc₁ hc₂
    exact ⟨c₁, ⟨(mem_elemsT QP hQP c₁).1 hc₁.1,
        Subgroup.mem_centralizer_singleton_iff.2 hc₁.2⟩,
      c₂, ⟨(mem_elemsT QP hQP c₂).1 hc₂.1,
        Subgroup.mem_centralizer_singleton_iff.2 hc₂.2⟩, h13', h1'⟩

end CFSG.ComponentClassification.RankTwoL33
