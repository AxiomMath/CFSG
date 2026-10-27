module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.CocodeFacts2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.GolayEven
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.Cocode

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Balance

open CFSG.Blueprint CFSG.EvenSporadicStandard.Wong77 CFSG.EvenSporadicStandard.Wong77.Module
open CFSG.Blueprint.NativeSporadic (Carrier)

section Counting

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem exists_card_filter_const {G : Type*} (f : G → Equiv.Perm X) (k : ℕ)
    (htrans : ∀ s t : Finset X, s.card = k → t.card = k → ∃ g, s.image (f g) = t)
    (O : Finset (Finset X)) (hO : ∀ g, ∀ T ∈ O, T.image (f g) ∈ O) :
    ∃ lam : ℕ, ∀ s : Finset X, s.card = k → (O.filter fun T => s ⊆ T).card = lam := by
  have hle : ∀ s t : Finset X, s.card = k → t.card = k →
      (O.filter fun T => s ⊆ T).card ≤ (O.filter fun T => t ⊆ T).card := by
    intro s t hs ht
    obtain ⟨g, hg⟩ := htrans s t hs ht
    refine Finset.card_le_card_of_injOn (fun T => T.image (f g)) ?_ ?_
    · intro T hT
      rw [Finset.coe_filter] at hT ⊢
      obtain ⟨hTO, hsT⟩ := hT
      refine ⟨hO g T hTO, ?_⟩
      rw [← hg]
      exact Finset.image_subset_image hsT
    · intro T _ T' _ h
      exact Finset.image_injective (f g).injective h
  by_cases h : ∃ s₀ : Finset X, s₀.card = k
  · obtain ⟨s₀, hs₀⟩ := h
    exact ⟨_, fun s hs => le_antisymm (hle s s₀ hs hs₀) (hle s₀ s hs₀ hs)⟩
  · exact ⟨0, fun s hs => absurd ⟨s, hs⟩ h⟩

theorem card_mul_choose_eq (k w : ℕ) (O : Finset (Finset X)) (hw : ∀ T ∈ O, T.card = w)
    (lam : ℕ) (hlam : ∀ s : Finset X, s.card = k → (O.filter fun T => s ⊆ T).card = lam) :
    O.card * Nat.choose w k = Nat.choose (Fintype.card X) k * lam := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Finset.powersetCard k (Finset.univ : Finset X)) (t := O)
    (fun s T => s ⊆ T)
  have h1 : ∑ s ∈ Finset.powersetCard k (Finset.univ : Finset X),
      (O.bipartiteAbove (fun s T => s ⊆ T) s).card =
      Nat.choose (Fintype.card X) k * lam := by
    rw [Finset.sum_congr rfl (g := fun _ => lam)]
    · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      exact hlam s hs.2
  have h2 : ∑ T ∈ O, ((Finset.powersetCard k (Finset.univ : Finset X)).bipartiteBelow
      (fun s T => s ⊆ T) T).card = O.card * Nat.choose w k := by
    rw [Finset.sum_congr rfl (g := fun _ => Nat.choose w k)]
    · rw [Finset.sum_const, smul_eq_mul]
    · intro T hT
      rw [← hw T hT, ← Finset.card_powersetCard]
      congr 1
      ext s
      simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      tauto
  rw [← h1, ← h2]
  exact h.symm

end Counting

@[expose] def supp (v : Word) : Finset (Fin 23) := Finset.univ.filter fun i => v i ≠ 0

theorem ind_supp (v : Word) : ind (supp v) = v := by
  funext i
  have : v i = 0 ∨ v i = 1 := by
    generalize v i = t
    revert t
    decide
  rcases this with h | h <;> simp [ind, supp, h]

theorem golayEven_orbit_large
    (u : ↥golayEven) (hu : u ≠ 0) :
    23 < (Set.range fun g : Carrier .M23 => golayRep g u).ncard := by
  classical
  have : Finite (Carrier .M23) := inferInstanceAs (Finite NativeSporadic.M23)
  let _ : Fintype (Carrier .M23) := Fintype.ofFinite _
  have hu0 : (u : Word) ≠ 0 := fun h => hu (Subtype.ext h)
  have hw : (supp (u : Word)).card = 8 ∨ (supp (u : Word)).card = 12 ∨
      (supp (u : Word)).card = 16 := golayEven_weight (u : Word) u.2 hu0
  set T := supp (u : Word) with hT
  have hind : (u : Word) = ind T := (ind_supp _).symm
  let O : Finset (Finset (Fin 23)) :=
    Finset.univ.image fun g : Carrier .M23 => T.image (toPerm g)
  have hOmem : ∀ T', T' ∈ O ↔ ∃ g : Carrier .M23, T.image (toPerm g) = T' := by
    intro T'
    simp [O]
  have horb : ∀ g : Carrier .M23,
      ((golayRep g u : ↥golayEven) : Word) = ind (T.image (toPerm g)) := by
    intro g
    rw [golayRep_apply, hind, wordRep_ind]
  have hcard : (Set.range fun g : Carrier .M23 => golayRep g u).ncard = O.card := by
    have h1 : (Subtype.val '' Set.range fun g : Carrier .M23 => golayRep g u) =
        ind '' (O : Set (Finset (Fin 23))) := by
      ext v
      simp only [Set.mem_image, Set.mem_range, Finset.mem_coe, hOmem]
      constructor
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨_, ⟨g, rfl⟩, (horb g).symm⟩
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨_, ⟨g, rfl⟩, horb g⟩
    calc (Set.range fun g : Carrier .M23 => golayRep g u).ncard
        = (Subtype.val '' Set.range fun g : Carrier .M23 => golayRep g u).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ = (ind '' (O : Set (Finset (Fin 23)))).ncard := by rw [h1]
      _ = (O : Set (Finset (Fin 23))).ncard := Set.ncard_image_of_injective _ ind_injective
      _ = O.card := Set.ncard_coe_finset O
  have hO : ∀ g : Carrier .M23, ∀ T' ∈ O, T'.image (toPerm g) ∈ O := by
    intro g T' hT'
    obtain ⟨h, rfl⟩ := (hOmem T').1 hT'
    refine (hOmem _).2 ⟨g * h, ?_⟩
    rw [Finset.image_image]
    congr 1
  have hwO : ∀ T' ∈ O, T'.card = T.card := by
    intro T' hT'
    obtain ⟨g, rfl⟩ := (hOmem T').1 hT'
    exact Finset.card_image_of_injective _ (toPerm g).injective
  have htrans : ∀ s t : Finset (Fin 23), s.card = 3 → t.card = 3 →
      ∃ g : Carrier .M23, s.image (toPerm g) = t := fun s t hs ht =>
    exists_image_eq_of_card_eq s t (hs.trans ht.symm) (by omega)
  obtain ⟨lam, hlam⟩ := exists_card_filter_const toPerm 3 htrans O hO
  have hmain := card_mul_choose_eq 3 T.card O hwO lam hlam
  rw [Fintype.card_fin] at hmain
  have hpos : 0 < O.card :=
    Finset.card_pos.2 ⟨T, (hOmem T).2 ⟨1, by simp [toPerm]⟩⟩
  have h23 : Nat.choose 23 3 = 1771 := by decide
  rw [hcard]
  rcases hw with h | h | h
  · rw [h, show Nat.choose 8 3 = 56 by decide, h23] at hmain
    omega
  · rw [h, show Nat.choose 12 3 = 220 by decide, h23] at hmain
    omega
  · rw [h, show Nat.choose 16 3 = 560 by decide, h23] at hmain
    omega

theorem cocode_orbit_points
    (x : Cocode) (hx : x ≠ 0)
    (h : (Set.range fun g : Carrier .M23 => cocodeRep g x).ncard ≤ 23) : ∃ i, x = pt i := by
  classical
  have : Finite Cocode := Finite.of_surjective coMk coMk_surjective
  obtain ⟨s, hs3, rfl⟩ := exists_card_le_three x
  have hs0 : s.card ≠ 0 := by
    intro h0
    apply hx
    rw [Finset.card_eq_zero.1 h0, ind_empty, map_zero]
  have hs1 : s.card = 1 := by
    by_contra hne
    have h2 : 2 ≤ s.card := by omega
    set k := s.card with hk
    have hsub : (fun t : Finset (Fin 23) => coMk (ind t)) ''
        ((Finset.powersetCard k (Finset.univ : Finset (Fin 23)) : Finset (Finset (Fin 23))) :
          Set (Finset (Fin 23))) ⊆
        Set.range fun g : Carrier .M23 => cocodeRep g (coMk (ind s)) := by
      rintro _ ⟨t, ht, rfl⟩
      rw [Finset.mem_coe, Finset.mem_powersetCard] at ht
      obtain ⟨g, hg⟩ := exists_image_eq_of_card_eq s t ht.2.symm hs3
      refine ⟨g, ?_⟩
      show cocodeRep g (coMk (ind s)) = coMk (ind t)
      rw [cocodeRep_ind]
      have : s.image (toPerm g) = t := hg
      rw [this]
    have hinj : Set.InjOn (fun t : Finset (Fin 23) => coMk (ind t))
        ((Finset.powersetCard k (Finset.univ : Finset (Fin 23)) : Finset (Finset (Fin 23))) :
          Set (Finset (Fin 23))) := by
      intro t ht t' ht' hh
      rw [Finset.mem_coe, Finset.mem_powersetCard] at ht ht'
      have := coMk_ind_injective (a₁ := ⟨t, by omega⟩) (a₂ := ⟨t', by omega⟩) hh
      exact congrArg Subtype.val this
    have hcardimg : ((fun t : Finset (Fin 23) => coMk (ind t)) ''
        ((Finset.powersetCard k (Finset.univ : Finset (Fin 23)) : Finset (Finset (Fin 23))) :
          Set (Finset (Fin 23)))).ncard = Nat.choose 23 k := by
      rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hcardimg] at hle
    have h3 : k ≤ 3 := hs3
    interval_cases k
    · rw [show Nat.choose 23 2 = 253 by decide] at hle
      omega
    · rw [show Nat.choose 23 3 = 1771 by decide] at hle
      omega
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs1
  exact ⟨i, by rw [pt, ← ind_singleton]⟩

end CFSG.EvenSporadicStandard.Induction.Balance
