module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoRankTwo

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII

variable {G K : Type*} [Group G] [Group K]

theorem point_class_image (f : G →* K) (hf : Function.Surjective f) (z : G) :
    f '' involutionPointClass z = involutionPointClass (f z) := by
  ext x
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact ⟨f g, by simp only [rightConjugateElem, map_mul, map_inv]⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨a, rfl⟩ := hf g
    exact ⟨rightConjugateElem z a, ⟨a, rfl⟩,
      by simp only [rightConjugateElem, map_mul, map_inv]⟩

theorem point_hull_map (f : G →* K) (hf : Function.Surjective f) (z : G) :
    (involutionPointHull z).map f = involutionPointHull (f z) := by
  unfold involutionPointHull
  rw [f.map_closure, point_class_image f hf z]

theorem point_hull_map_le (f : G →* K) (z : G) :
    (involutionPointHull z).map f ≤ involutionPointHull (f z) := by
  have h := Subgroup.map_normalClosure_le ({z} : Set G) f
  simpa only [Set.image_singleton, tightly_embedded_point_hull_eq_normalClosure] using h

@[expose] def pointHullHom (f : G →* K) (z : G) :
    involutionPointHull z →* involutionPointHull (f z) :=
  (f.comp (involutionPointHull z).subtype).codRestrict
    (involutionPointHull (f z)) (fun x =>
      point_hull_map_le f z (Subgroup.mem_map_of_mem f x.property))

theorem pointHullHom_apply (f : G →* K) (z : G) (x : involutionPointHull z) :
    (pointHullHom f z x : K) = f (x : G) := rfl

theorem pointHullHom_surjective (f : G →* K) (hf : Function.Surjective f) (z : G) :
    Function.Surjective (pointHullHom f z) := by
  rintro ⟨y, hy⟩
  rw [← point_hull_map f hf z] at hy
  obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

theorem pointHullHom_ker (f : G →* K) (z : G) :
    (pointHullHom f z).ker = f.ker.subgroupOf (involutionPointHull z) := by
  ext x
  change (pointHullHom f z x = 1) ↔ f (x : G) = 1
  exact Subtype.ext_iff

theorem pointHullHom_odd_ker (f : G →* K) (hodd : Odd (Nat.card f.ker)) (z : G) :
    Odd (Nat.card (pointHullHom f z).ker) := by
  rw [pointHullHom_ker]
  have hcard : Nat.card (f.ker.subgroupOf (involutionPointHull z)) =
      Nat.card (f.ker ⊓ involutionPointHull z : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
  rw [hcard]
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

variable [Finite G]

theorem point_hull_image_perfect_of_rank_two_Q (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (f : G →* K) (hf : Function.Surjective f) :
    Group.IsPerfect (involutionPointHull (f z)) := by
  let : Group.IsPerfect (involutionPointHull z) :=
    point_hull_perfect_of_rank_two_Q Q hodd hnormal hrank z hzQ hz
  exact Group.IsPerfect.ofSurjective (pointHullHom_surjective f hf z)

theorem point_hull_image_commutative_factor_subsingleton (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (f : G →* K) (hf : Function.Surjective f)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B]
    (e : involutionPointHull (f z) ≃* A × B) : Subsingleton A := by
  let : Group.IsPerfect (involutionPointHull (f z)) :=
    point_hull_image_perfect_of_rank_two_Q Q hodd hnormal hrank z hzQ hz f hf
  let p : involutionPointHull (f z) →* A := (MonoidHom.fst A B).comp e.toMonoidHom
  have hp : Function.Surjective p := by
    intro a
    refine ⟨e.symm (a, 1), ?_⟩
    change (e (e.symm (a, 1))).1 = a
    rw [e.apply_symm_apply]
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective hp
  exact Group.IsPerfect.subsingleton_of_isMulCommutative

theorem point_hull_image_split_second_equiv (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (f : G →* K) (hf : Function.Surjective f)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B]
    (e : involutionPointHull (f z) ≃* A × B) :
    ∃ e' : involutionPointHull (f z) ≃* B, ∀ x, e' x = (e x).2 := by
  let : Subsingleton A := point_hull_image_commutative_factor_subsingleton
    Q hodd hnormal hrank z hzQ hz f hf e
  let : Unique A := ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
  exact ⟨e.trans ((MulEquiv.prodComm : A × B ≃* B × A).trans MulEquiv.prodUnique),
    fun _ => rfl⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
