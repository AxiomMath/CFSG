module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Group

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

def puncturedConjSupport (H : Subgroup G) : Set G :=
  Group.conjugatesOfSet ((H : Set G) \ {1})

variable {H K : Subgroup G}

theorem mem_puncturedConjSupport_iff {x : G} :
    x ∈ puncturedConjSupport H ↔ (∃ g : G, g * x * g⁻¹ ∈ H) ∧ x ≠ 1 := by
  simp only [puncturedConjSupport, Group.mem_conjugatesOfSet_iff, Set.mem_sdiff,
    SetLike.mem_coe, Set.mem_singleton_iff, isConj_iff]
  constructor
  · rintro ⟨a, ⟨haH, ha1⟩, c, rfl⟩
    refine ⟨⟨c⁻¹, ?_⟩, ?_⟩
    · simpa [mul_assoc] using haH
    · simpa using ha1
  · rintro ⟨⟨g, hg⟩, hx⟩
    refine ⟨g * x * g⁻¹, ⟨hg, ?_⟩, g⁻¹, by group⟩
    simpa using hx

theorem puncturedConjSupport_eq_iUnion (H : Subgroup G) :
    puncturedConjSupport H = ⋃ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) := by
  ext x
  simp only [puncturedConjSupport, Group.mem_conjugatesOfSet_iff, Set.mem_iUnion, Set.mem_image,
    isConj_iff]
  constructor
  · rintro ⟨a, ha, c, rfl⟩
    exact ⟨c⁻¹, a, ha, by group⟩
  · rintro ⟨g, a, ha, rfl⟩
    exact ⟨a, ha, g⁻¹, by group⟩

theorem ne_one_of_mem_puncturedConjSupport {x : G} (hx : x ∈ puncturedConjSupport H) : x ≠ 1 :=
  (mem_puncturedConjSupport_iff.mp hx).2

theorem one_notMem_puncturedConjSupport (H : Subgroup G) :
    (1 : G) ∉ puncturedConjSupport H := fun hx =>
  ne_one_of_mem_puncturedConjSupport hx rfl

theorem sdiff_subset_puncturedConjSupport (H : Subgroup G) :
    (H : Set G) \ {1} ⊆ puncturedConjSupport H :=
  Group.subset_conjugatesOfSet

theorem puncturedConjSupport_mono (h : H ≤ K) :
    puncturedConjSupport H ⊆ puncturedConjSupport K :=
  Group.conjugatesOfSet_mono (Set.sdiff_subset_sdiff_left h)

@[simp]
theorem puncturedConjSupport_bot : puncturedConjSupport (⊥ : Subgroup G) = ∅ := by
  ext x
  simp only [mem_puncturedConjSupport_iff, Subgroup.mem_bot, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro ⟨g, hg⟩
  simpa using hg

theorem puncturedConjSupport_nonempty (hH : H ≠ ⊥) : (puncturedConjSupport H).Nonempty := by
  obtain ⟨⟨x, hxH⟩, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  exact ⟨x, sdiff_subset_puncturedConjSupport H ⟨hxH, by simpa using hx⟩⟩

theorem orderOf_dvd_natCard_of_mem_puncturedConjSupport {x : G}
    (hx : x ∈ puncturedConjSupport H) : orderOf x ∣ Nat.card H := by
  obtain ⟨⟨g, hg⟩, -⟩ := mem_puncturedConjSupport_iff.mp hx
  have h := H.orderOf_dvd_natCard hg
  rwa [show orderOf (g * x * g⁻¹) = orderOf x from by
    simpa [MulAut.conj] using
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x] at h

variable {I : Type*} {H : I → Subgroup G}

theorem pairwise_disjoint_puncturedConjSupport
    (hcop : Pairwise fun i j => (Nat.card (H i)).Coprime (Nat.card (H j))) :
    Pairwise fun i j =>
      Disjoint (puncturedConjSupport (H i)) (puncturedConjSupport (H j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hx1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcop hij)
      (orderOf_dvd_natCard_of_mem_puncturedConjSupport hxi)
      (orderOf_dvd_natCard_of_mem_puncturedConjSupport hxj)
  exact ne_one_of_mem_puncturedConjSupport hxi (orderOf_eq_one_iff.mp hx1)

theorem pairwise_natCard_ne_of_pairwise_coprime
    (hcop : Pairwise fun i j => (Nat.card (H i)).Coprime (Nat.card (H j)))
    (hne : ∀ i, H i ≠ ⊥) : Pairwise fun i j => Nat.card (H i) ≠ Nat.card (H j) := by
  intro i j hij hcard
  have hco : (Nat.card (H i)).Coprime (Nat.card (H j)) := hcop hij
  rw [hcard, Nat.coprime_self] at hco
  exact hne j (Subgroup.card_eq_one.mp hco)

theorem injective_natCard_of_pairwise_coprime
    (hcop : Pairwise fun i j => (Nat.card (H i)).Coprime (Nat.card (H j)))
    (hne : ∀ i, H i ≠ ⊥) : Function.Injective fun i => Nat.card (H i) := fun _ _ hij =>
  not_not.mp fun h => pairwise_natCard_ne_of_pairwise_coprime hcop hne h hij

theorem pairwise_disjoint_and_one_notMem_and_pairwise_natCard_ne
    (hcop : Pairwise fun i j => (Nat.card (H i)).Coprime (Nat.card (H j)))
    (hne : ∀ i, H i ≠ ⊥) :
    (Pairwise fun i j =>
        Disjoint (puncturedConjSupport (H i)) (puncturedConjSupport (H j))) ∧
      (∀ i, (1 : G) ∉ puncturedConjSupport (H i)) ∧
      Pairwise fun i j => Nat.card (H i) ≠ Nat.card (H j) :=
  ⟨pairwise_disjoint_puncturedConjSupport hcop, fun i => one_notMem_puncturedConjSupport (H i),
    pairwise_natCard_ne_of_pairwise_coprime hcop hne⟩

end

end CFSG.FeitThompson
