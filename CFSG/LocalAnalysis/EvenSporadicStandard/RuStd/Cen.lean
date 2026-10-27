module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Fusion

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup

variable {G : Type} [Group G]

theorem centralizer_eq_of_closure_eq {S T : Set G} (h : closure S = closure T) :
    centralizer S = centralizer T := by
  rw [← Subgroup.centralizer_closure S, ← Subgroup.centralizer_closure T, h]

theorem card_centralizer_conj_image (g : G) (S : Set G) :
    Nat.card (centralizer ((fun s => g * s * g⁻¹) '' S)) = Nat.card (centralizer S) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun x => ?_).symm
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx t ht
    obtain ⟨s, hs, rfl⟩ := ht
    have := hx s hs
    show g * s * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * s * g⁻¹)
    calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
      _ = g * (x * s) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group
  · intro h s hs
    have := h (g * s * g⁻¹) ⟨s, hs, rfl⟩
    change g * s * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * s * g⁻¹) at this
    have h2 : g * (s * x) * g⁻¹ = g * (x * s) * g⁻¹ := by
      calc g * (s * x) * g⁻¹ = g * s * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * s * g⁻¹) := this
        _ = g * (x * s) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

variable [Finite G] {L : Subgroup G} {z : G}

omit [Finite G] in
theorem Config.centralizer_cons_eq (hc : Config G L z) (S : Set L) :
    centralizer (insert z ((fun l : L => (l : G)) '' S)) =
      ((centralizer S).map L.subtype) ⊔ zpowers z := by
  ext h
  constructor
  · intro hh
    have hzh : z * h = h * z := mem_centralizer_iff.1 hh z (Set.mem_insert _ _)
    have hS : ∀ s ∈ S, (s : G) * h = h * (s : G) := fun s hs =>
      mem_centralizer_iff.1 hh (s : G) (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩)
    have hHz : h ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hzh.symm
    rcases hc.mem_cases hHz with hhL | ⟨l, hl, rfl⟩
    · refine mem_sup_left ⟨⟨h, hhL⟩, ?_, rfl⟩
      show (⟨h, hhL⟩ : L) ∈ centralizer S
      rw [mem_centralizer_iff]
      intro s hs
      exact Subtype.ext (hS s hs)
    · have hlS : (⟨l, hl⟩ : L) ∈ centralizer S := by
        rw [mem_centralizer_iff]
        intro s hs
        apply Subtype.ext
        have h1 := hS s hs
        have h2 : (s : G) * z = z * (s : G) := hc.comm s s.2
        show (s : G) * l = l * (s : G)
        apply mul_left_cancel (a := z)
        calc z * ((s : G) * l) = ((z * (s : G))) * l := by group
          _ = ((s : G) * z) * l := by rw [h2]
          _ = (s : G) * (z * l) := by group
          _ = (z * l) * (s : G) := h1
          _ = z * (l * (s : G)) := by group
      have hmem : l ∈ (centralizer S).map L.subtype := ⟨⟨l, hl⟩, hlS, rfl⟩
      have : z * l = l * z := (hc.comm l hl).symm
      rw [this]
      exact mul_mem (mem_sup_left hmem) (mem_sup_right (mem_zpowers z))
  · intro hh
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := (centralizer S).map L.subtype) (B := zpowers z) (by
        rw [zpowers_le]
        rw [mem_centralizer_iff]
        rintro _ ⟨l, _, rfl⟩
        exact hc.comm l l.2) hh
    obtain ⟨l, hlS, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    rw [mem_centralizer_iff]
    intro t ht
    have hzt : ∀ s : L, Commute (s : G) z := fun s => hc.comm s s.2
    have hzk : ∀ s : L, Commute (s : G) (z ^ k) := fun s => (hzt s).zpow_right k
    rcases ht with ht | ⟨s, hs, ht⟩
    · rw [ht]
      exact (((hzt l).symm).mul_right (Commute.refl z |>.zpow_right k)).eq
    · rw [← ht]
      have hs' : Commute (s : G) (l : G) := by
        have := mem_centralizer_iff.1 hlS s hs
        exact congrArg Subtype.val this
      exact (hs'.mul_right (hzk s)).eq

omit [Finite G] in
theorem Config.card_centralizer_cons (hc : Config G L z) (S : Set L) :
    Nat.card (centralizer (insert z ((fun l : L => (l : G)) '' S))) =
      2 * Nat.card (centralizer S : Subgroup L) := by
  rw [hc.centralizer_cons_eq S]
  set A := (centralizer S).map L.subtype with hA
  have hAL : A ≤ L := by
    rintro _ ⟨l, _, rfl⟩
    exact l.2
  have hdisj : Disjoint A (zpowers z) := hc.disjoint.mono_left hAL
  have hle : zpowers z ≤ centralizer (A : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨l, _, rfl⟩
    exact hc.comm l l.2
  have e := (mulEquivProdSup hle hdisj).toEquiv
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zpowers, hc.orderOf_z,
    Subgroup.card_map_of_injective L.subtype_injective, mul_comm]

theorem centralizer_pair_eq_inf {Y : Type*} [Group Y] (a b : Y) :
    centralizer ({a, b} : Set Y) = centralizer ({a} : Set Y) ⊓ centralizer ({b} : Set Y) := by
  ext x
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, mem_inf]

omit [Finite G] in
theorem Config.card_centralizer_pair (hc : Config G L z) (ℓ : L) :
    Nat.card (centralizer ({z, (ℓ : G)} : Set G)) = 2 * Nat.card (centralizer ({ℓ} : Set L)) := by
  have := hc.card_centralizer_cons {ℓ}
  rwa [Set.image_singleton] at this

omit [Finite G] in
theorem Config.card_centralizer_triple (hc : Config G L z) (ℓ m : L) :
    Nat.card (centralizer ({z, (ℓ : G), (m : G)} : Set G)) =
      2 * Nat.card ↥(centralizer ({ℓ} : Set L) ⊓ centralizer ({m} : Set L)) := by
  have := hc.card_centralizer_cons {ℓ, m}
  rwa [Set.image_pair, centralizer_pair_eq_inf] at this

end CFSG.EvenSporadicStandard.RuStd
