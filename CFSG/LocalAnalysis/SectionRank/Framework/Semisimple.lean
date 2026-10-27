module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.SectionRank

open Subgroup CFSG.LocalCores
open scoped commutatorElement

theorem commutatorElement_mul_mem_center {X : Type*} [Group X] (a b : X) {z w : X}
    (hz : z ∈ center X) (hw : w ∈ center X) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    Commute.commutator_eq (mem_center_iff.mp hz (b * w)).symm, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, Commute.commutator_eq (mem_center_iff.mp hw a),
    mul_one, mul_inv_cancel_right]

theorem perfect_central_supplement {X : Type*} [Group X] (hX : Group.IsPerfect X) :
    (∀ Y : Subgroup X, Y ⊔ center X = ⊤ → Y = ⊤) ∧ center X ≤ frattini X := by
  have h1 : ∀ Y : Subgroup X, Y ⊔ center X = ⊤ → Y = ⊤ := by
    intro Y hY
    have hmem : ∀ g : X, ∃ y ∈ Y, ∃ z ∈ center X, y * z = g := fun g => by
      have hg : g ∈ ((Y ⊔ center X : Subgroup X) : Set X) := by
        rw [hY]
        exact mem_top g
      rwa [mul_normal, Set.mem_mul] at hg
    rw [eq_top_iff, ← hX.commutator_eq_top, commutator_def, commutator_le]
    intro g _ h _
    obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := hmem g
    obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := hmem h
    rw [commutatorElement_mul_mem_center y₁ y₂ hz₁ hz₂]
    exact commutator_le_self Y (commutator_mem_commutator hy₁ hy₂)
  refine ⟨h1, ?_⟩
  refine le_iInf₂ fun M (hM : IsCoatom M) => ?_
  by_contra hZM
  exact hM.1 (h1 M (hM.2 _ (lt_of_le_of_ne le_sup_left
    fun h => hZM (le_sup_right.trans h.symm.le))))

theorem semisimple_solvable_quotient {S : Type*} [Group S] [Finite S] (hS : layer S = ⊤)
    (A : Subgroup S) [A.Normal] (hA : Group.IsSolvable A) :
    A ≤ center S ∧ layer (S ⧸ A) = ⊤ := by
  refine ⟨?_, layer_eq_top_of_surjective hS _ (QuotientGroup.mk'_surjective A)⟩
  have h := (component_solvable_centralizer hA (inferInstance : A.Normal).isSubnormal).2
  rw [hS] at h
  exact commutator_top_left_eq_bot_iff_le_center.mp h

theorem perfect_central_semisimple_extension {X : Type*} [Group X] (hX : Group.IsPerfect X)
    (C : Subgroup X) [C.Normal] (hC : C ≤ center X) (hE : layer (X ⧸ C) = ⊤) :
    layer X = ⊤ := by
  have hT : ∀ T : Subgroup (X ⧸ C), IsComponent T → T ≤ (layer X).map (QuotientGroup.mk' C) := by
    intro T hT
    let H := T.comap (QuotientGroup.mk' C)
    let f : H →* T := ((QuotientGroup.mk' C).comp H.subtype).codRestrict T fun h => h.2
    have hf : Function.Surjective f := fun t => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective C (t : X ⧸ C)
      exact ⟨⟨x, show QuotientGroup.mk' C x ∈ T from hx ▸ t.2⟩, Subtype.ext hx⟩
    have hker : f.ker ≤ center H := fun h hh => by
      have hhC : (h : X) ∈ C :=
        (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hh))
      exact mem_center_iff.mpr fun k => Subtype.ext (mem_center_iff.mp (hC hhC) k)
    have hL := quasisimple_central_extension_derived_of_surjective f hf hker hT.1
    obtain ⟨-, -, hsurj⟩ := central_extension_derived_of_surjective f hf hker hT.1.1
    have hLc : IsComponent ((commutator H).map H.subtype) := by
      refine ⟨isQuasisimple_of_mulEquiv
        ((commutator H).equivMapOfInjective _ H.subtype_injective) hL, ?_⟩
      refine IsSubnormal.step _ H (map_subtype_le _) (hT.2.comap _) ?_
      change (((commutator H).map H.subtype).comap H.subtype).Normal
      rw [comap_map_eq_self_of_injective H.subtype_injective]
      infer_instance
    intro t ht
    obtain ⟨⟨x, hx⟩, hxt⟩ := hsurj ⟨t, ht⟩
    exact ⟨(x : X), component_le_layer hLc (mem_map_of_mem _ hx), congrArg Subtype.val hxt⟩
  have hmap : (layer X).map (QuotientGroup.mk' C) = ⊤ := by
    rw [eq_top_iff, ← hE]
    exact sSup_le hT
  have hsup : layer X ⊔ C = ⊤ := by
    rw [← QuotientGroup.ker_mk' C, ← comap_map_eq, hmap, comap_top]
  exact (perfect_central_supplement hX).1 _
    (eq_top_iff.mpr (hsup.symm.le.trans (sup_le_sup_left hC _)))

theorem centerless_semisimple_quotient {S T : Type*} [Group S] [Group T] [Finite S]
    (hE : layer S = ⊤) (hZ : center S = ⊥) (f : S →* T) (hf : Function.Surjective f) :
    layer T = ⊤ ∧ center T = ⊥ := by
  refine ⟨layer_eq_top_of_surjective hE f hf, ?_⟩
  have hdich : ∀ K : Subgroup S, IsComponent K →
      K ≤ f.ker ∨ ⁅K, (center T).comap f⁆ = ⊥ := by
    intro K hK
    refine (component_normal_subgroup hK inferInstance).imp (fun h => ?_) id
    have hKZ : K.map f ≤ center T := map_le_iff_le_comap.mpr h
    rw [← isPerfect_iff.mp hK.1.1, ← Subgroup.map_eq_bot_iff, map_commutator]
    exact le_bot_iff.mp ((commutator_mono hKZ le_rfl).trans (commutator_center_left _).le)
  have hZK : ∀ K : Subgroup S, IsComponent K → center K = ⊥ := by
    intro K hK
    refine eq_bot_iff.mpr fun z hz => ?_
    have hzc := center_component_le_centralizer_layer hK (mem_map_of_mem K.subtype hz)
    rw [hE, coe_top, centralizer_univ, hZ] at hzc
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp hzc))
  refine eq_bot_iff.mpr fun t ht => ?_
  obtain ⟨m, rfl⟩ := hf t
  obtain ⟨x, rfl⟩ := exists_layerMul_eq (hE ▸ mem_top m : m ∈ layer S)
  have hx : ∀ K : ComponentIndex S, (x K : S) ∈ f.ker := by
    intro K
    rcases hdich K.1 K.2 with h | h
    · exact h (x K).2
    · have hc : x K ∈ center K.1 := mem_center_iff.mpr fun k => Subtype.ext ?_
      · rw [hZK K.1 K.2, mem_bot] at hc
        rw [hc]
        exact one_mem _
      have hk : Commute (k : S) (layerMul S x) :=
        (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h k.2) _ ht).symm
      exact ((commute_layerMul_iff x K k.2).mp hk).eq
  exact mem_bot.mpr (MonoidHom.mem_ker.mp (layerMul_mem x hx))

theorem minimal_semisimple_cover {X S : Type*} [Group X] [Group S] [Finite X]
    (hS : layer S = ⊤) (π : X →* S) (hπ : Function.Surjective π)
    (hmin : ∀ Y : Subgroup X, Y ≠ ⊤ → Y.map π ≠ ⊤) :
    Group.IsPerfect X ∧ ((center S).comap π).Normal ∧
      Group.IsNilpotent ((center S).comap π) ∧
      (∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q ((center S).comap π)),
        ((Q : Subgroup ((center S).comap π)).map ((center S).comap π).subtype).Normal) ∧
      (∃ e : X ⧸ (center S).comap π ≃* S ⧸ center S,
        ∀ x : X, e (QuotientGroup.mk x) = QuotientGroup.mk (π x)) ∧
      center (S ⧸ center S) = ⊥ ∧ layer (S ⧸ center S) = ⊤ ∧
      center (X ⧸ (center S).comap π) = ⊥ ∧ layer (X ⧸ (center S).comap π) = ⊤ := by
  have : Finite S := Finite.of_surjective π hπ
  have hmin' : ∀ Y : Subgroup X, Y.map π = ⊤ → Y = ⊤ := fun Y hY =>
    by_contra fun h => hmin Y h hY
  have hSp : Group.IsPerfect S := Group.IsPerfect.top_iff.mp (hS ▸ layer_isPerfect)
  have hXp : Group.IsPerfect X := by
    rw [Group.isPerfect_def]
    refine hmin' _ ?_
    rw [commutator_def, map_commutator, map_top_of_surjective π hπ, ← commutator_def,
      hSp.commutator_eq_top]
  have hsyl : ∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q ((center S).comap π)),
      ((Q : Subgroup ((center S).comap π)).map ((center S).comap π).subtype).Normal := by
    intro q _ Q
    have hF := congrArg (map π) (Sylow.normalizer_sup_eq_top Q)
    rw [Subgroup.map_sup, map_top_of_surjective π hπ] at hF
    have h2 : (normalizer (((Q : Subgroup ((center S).comap π)).map
        ((center S).comap π).subtype : Subgroup X) : Set X)).map π ⊔ center S = ⊤ :=
      eq_top_iff.mpr (hF.symm.le.trans (sup_le_sup_left (map_comap_le _ _) _))
    exact normalizer_eq_top_iff.mp (hmin' _ ((perfect_central_supplement hSp).1 _ h2))
  have hnil : Group.IsNilpotent ((center S).comap π) := by
    refine ((Group.isNilpotent_of_finite_tfae (G := (center S).comap π)).out 4 1).mp ?_
    intro q _ Q
    have hQ := (hsyl q Q).subgroupOf ((center S).comap π)
    rwa [subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)] at hQ
  have hker : (center S).comap π = ((QuotientGroup.mk' (center S)).comp π).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e : X ⧸ (center S).comap π ≃* S ⧸ center S := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hπ))
  have hZ : center (S ⧸ center S) = ⊥ := by
    have := hSp
    exact Group.IsPerfect.center_quotient_center_eq_bot S
  refine ⟨hXp, inferInstance, hnil, hsyl, ⟨e, fun x => rfl⟩, hZ,
    layer_eq_top_of_surjective hS _ (QuotientGroup.mk'_surjective _), ?_,
    layer_eq_top_of_surjective hS (e.symm.toMonoidHom.comp (QuotientGroup.mk' (center S)))
      (e.symm.surjective.comp (QuotientGroup.mk'_surjective _))⟩
  rw [← map_center_eq e.symm, hZ, Subgroup.map_bot]

end CFSG.SectionRank
