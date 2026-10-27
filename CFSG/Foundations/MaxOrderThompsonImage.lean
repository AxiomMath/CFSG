module

public import CFSG.Foundations.MaxCardThompson
public import CFSG.GroupTheory.ThompsonIsomorphism
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

open Subgroup

universe u v

variable {G : Type u} [Group G]

section Injective

variable {H : Type v} [Group H]

private theorem map_map_subtype_eq (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    ∃ e : S ≃* S.map f, f.comp S.subtype = (S.map f).subtype.comp e.toMonoidHom :=
  ⟨MulEquiv.ofBijective (f.subgroupMap S)
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.subgroupMap_surjective S⟩, by ext; rfl⟩

theorem map_ambientOrderThompson_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    (ambientOrderThompson S).map f = ambientOrderThompson (S.map f) := by
  obtain ⟨e, he⟩ := map_map_subtype_eq f S hf
  unfold ambientOrderThompson
  rw [map_map, he, ← map_map, map_orderThompson e]

theorem map_ambientOrderZJ_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    (ambientOrderZJ S).map f = ambientOrderZJ (S.map f) := by
  obtain ⟨e, he⟩ := map_map_subtype_eq f S hf
  unfold ambientOrderZJ
  rw [map_map, he, ← map_map, map_orderZJ e]

theorem map_maxCardZJ_map_subtype_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    ((maxCardZJ S).map S.subtype).map f = (maxCardZJ (S.map f)).map (S.map f).subtype := by
  obtain ⟨e, he⟩ := map_map_subtype_eq f S hf
  rw [map_map, he, ← map_map, maxCardZJ_map_mulEquiv e]

theorem injective_comp_subtype_of_coprime_card_ker [Finite G] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hker : Nat.Coprime p (Nat.card f.ker)) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    Function.Injective (f.comp Q.subtype) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hdisj : Disjoint Q f.ker :=
    disjoint_of_coprime_natCard (by rw [hn]; exact hker.pow_left n)
  refine (injective_iff_map_eq_one _).mpr fun x hx => Subtype.ext ?_
  exact disjoint_def.mp hdisj x.2 hx

theorem map_ambientOrderZJ_of_coprime_card_ker [Finite G] {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker)) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    (ambientOrderZJ Q).map f = ambientOrderZJ (Q.map f) :=
  map_ambientOrderZJ_of_injective f Q (injective_comp_subtype_of_coprime_card_ker f hker hQ)

end Injective

end CFSG
