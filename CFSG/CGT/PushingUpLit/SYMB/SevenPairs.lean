module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap
public import CFSG.CGT.PushingUpLit.BHS6.SymAltFacts
public import CFSG.CGT.PushingUpLit.BHS7.FifteenComp
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

section Pts

variable {n : ℕ}

@[expose] def Ωs (t₁ t₂ : Equiv.Perm (Fin n)) (c : Fin n) : Finset (Fin n) :=
  t₁.support ∪ t₂.support ∪ {c}

theorem mem_setStab_of_support_subset {Ω : Finset (Fin n)} {t : Equiv.Perm (Fin n)}
    (h : t.support ⊆ Ω) : t ∈ setStab Ω := by
  rw [mem_setStab]
  intro x
  by_cases hx : t x = x
  · rw [hx]
  · have hxs : x ∈ t.support := Equiv.Perm.mem_support.2 hx
    exact ⟨fun _ => h hxs, fun _ => h (Equiv.Perm.apply_mem_support.2 hxs)⟩

theorem mem_setStab_of_disjoint {Ω : Finset (Fin n)} {t : Equiv.Perm (Fin n)}
    (h : Disjoint t.support Ω) : t ∈ setStab Ω := by
  rw [mem_setStab]
  intro x
  have hfix : ∀ y ∈ Ω, t y = y := fun y hy => by
    by_contra hne
    exact Finset.disjoint_left.1 h (Equiv.Perm.mem_support.2 hne) hy
  constructor
  · intro hx
    have h1 : t (t x) = t x := hfix _ hx
    have h2 : t x = x := t.injective h1
    rw [h2] at hx
    exact hx
  · intro hx
    rw [hfix x hx]
    exact hx

variable {T' : Set (Equiv.Perm (Fin n))}

theorem card_Ωs (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    {t₁ t₂ : Equiv.Perm (Fin n)} (h1 : t₁ ∈ T') (h2 : t₂ ∈ T') (hne : t₁ ≠ t₂) {c : Fin n}
    (hcf : ∀ s ∈ T', s c = c) : (Ωs t₁ t₂ c).card = 5 := by
  classical
  have hd : Disjoint t₁.support t₂.support :=
    disjoint_support_of_commute (hs t₁ h1) (hs t₂ h2) (hc t₁ h1 t₂ h2) hne
  have hc1 : c ∉ t₁.support := fun h => (Equiv.Perm.mem_support.1 h) (hcf t₁ h1)
  have hc2 : c ∉ t₂.support := fun h => (Equiv.Perm.mem_support.1 h) (hcf t₂ h2)
  have hcu : c ∉ t₁.support ∪ t₂.support := by
    simp [hc1, hc2]
  unfold Ωs
  rw [Finset.union_comm (t₁.support ∪ t₂.support) {c}, ← Finset.insert_eq,
    Finset.card_insert_of_notMem hcu, Finset.card_union_of_disjoint hd,
    Equiv.Perm.card_support_eq_two.2 (hs t₁ h1), Equiv.Perm.card_support_eq_two.2 (hs t₂ h2)]

theorem stab_Ωs (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    {t₁ t₂ : Equiv.Perm (Fin n)} (h1 : t₁ ∈ T') (h2 : t₂ ∈ T') {c : Fin n}
    (hcf : ∀ s ∈ T', s c = c) : ∀ t ∈ T', t ∈ setStab (Ωs t₁ t₂ c) := by
  classical
  intro t ht
  by_cases e1 : t = t₁
  · subst e1
    exact mem_setStab_of_support_subset fun x hx => by
      unfold Ωs
      simp [hx]
  · by_cases e2 : t = t₂
    · subst e2
      exact mem_setStab_of_support_subset fun x hx => by
        unfold Ωs
        simp [hx]
    · refine mem_setStab_of_disjoint ?_
      have hd1 := disjoint_support_of_commute (hs t ht) (hs t₁ h1) (hc t ht t₁ h1) e1
      have hd2 := disjoint_support_of_commute (hs t ht) (hs t₂ h2) (hc t ht t₂ h2) e2
      have hct : c ∉ t.support := fun h => (Equiv.Perm.mem_support.1 h) (hcf t ht)
      unfold Ωs
      rw [Finset.disjoint_left]
      intro x hx hxΩ
      simp only [Finset.mem_union, Finset.mem_singleton] at hxΩ
      rcases hxΩ with (h | h) | h
      · exact Finset.disjoint_left.1 hd1 hx h
      · exact Finset.disjoint_left.1 hd2 hx h
      · exact hct (h ▸ hx)

end Pts

end CFSG.CGT.PushingUpLit.SYMB
