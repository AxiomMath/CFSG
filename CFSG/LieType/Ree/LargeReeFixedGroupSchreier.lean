module

public import CFSG.LieType.Ree.LargeReeMinimalBorel
public import CFSG.LieType.Ree.LargeReeSimplePairGeneration
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LieType.Ree.LargeReeB2PairAutomorphism
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LieType.Ree.SmallReeSylowTorusSchreier

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section General

variable {G : Type*} [Group G]

theorem minimal_subgroupOf_iff {H B : Subgroup G} (hB : B ≤ H) (S : Subgroup H) :
    Minimal (fun S : Subgroup H => B.subgroupOf H < S) S ↔
      Minimal (fun T : Subgroup G => B < T ∧ T ≤ H) (S.map H.subtype) := by
  have hP : ∀ S : Subgroup H, (B < S.map H.subtype ∧ S.map H.subtype ≤ H) ↔
      B.subgroupOf H < S := fun S => by
    rw [← Subgroup.map_subtype_lt_map_subtype, Subgroup.map_subgroupOf_eq_of_le hB]
    exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.map_subtype_le _⟩⟩
  constructor
  · rintro ⟨hS, hmin⟩
    refine ⟨(hP S).2 hS, fun ⦃T⦄ hT hTS => ?_⟩
    have hTH : (T.subgroupOf H).map H.subtype = T := Subgroup.map_subgroupOf_eq_of_le hT.2
    rw [← hTH] at hT hTS ⊢
    exact Subgroup.map_subtype_le_map_subtype.2
      (hmin ((hP _).1 hT) (Subgroup.map_subtype_le_map_subtype.1 hTS))
  · rintro ⟨hS, hmin⟩
    refine ⟨(hP S).1 hS, fun ⦃T⦄ hT hTS => ?_⟩
    exact Subgroup.map_subtype_le_map_subtype.1
      (hmin ((hP T).2 hT) (Subgroup.map_subtype_le_map_subtype.2 hTS))

theorem map_subtype_eq_iff {H T : Subgroup G} (hT : T ≤ H) (S : Subgroup H) :
    S.map H.subtype = T ↔ S = T.subgroupOf H := by
  constructor
  · rintro rfl
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective S).symm
  · rintro rfl
    exact Subgroup.map_subgroupOf_eq_of_le hT

theorem inf_subgroupOf_eq (H K L : Subgroup G) :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L :=
  Subgroup.comap_inf H K L.subtype

theorem minimal_map_of_map_eq {B S : Subgroup G} (α : MulAut G)
    (hB : B.map α.toMonoidHom = B) (hS : Minimal (fun S => B < S) S) :
    Minimal (fun S => B < S) (S.map α.toMonoidHom) := by
  have key : ∀ y : Subgroup G, B < α.mapSubgroup y ↔ B < y := fun y => by
    have h := α.mapSubgroup.lt_iff_lt (x := B) (y := y)
    rwa [show α.mapSubgroup B = B from hB] at h
  exact (minimal_apply_orderIso α.mapSubgroup (P := fun S => B < S) (x := S)).2
    (by simpa only [key] using hS)

theorem map_normalizer_of_map_eq {U : Subgroup G} (α : MulAut G)
    (hU : U.map α.toMonoidHom = U) :
    (Subgroup.normalizer (U : Set G)).map α.toMonoidHom = Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.map_equiv_normalizer_eq, hU]

theorem map_subgroupOf_eq_of_forall {M S : Subgroup G} (β : MulAut M)
    (hβ : ∀ m : M, ((β m : M) : G) ∈ S ↔ (m : G) ∈ S) :
    (S.subgroupOf M).map β.toMonoidHom = S.subgroupOf M := by
  ext m
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← hβ,
    MulEquiv.apply_symm_apply]

end General

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

section Opposite

variable
    {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}
  {w₀ : WeylGroup t.tag}
  (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
include hw₀

theorem reeGamma_inf_normalizer_reeFixedNegUnipotent :
    t.reeGamma K a ⊓ Subgroup.normalizer (t.reeFixedNegUnipotent K a : Set (ModGL t.tag K)) =
      t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a := by
  have hn := (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  have hΓ : (t.reeGamma K a).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom = t.reeGamma K a :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)
  calc t.reeGamma K a ⊓ Subgroup.normalizer (t.reeFixedNegUnipotent K a : Set (ModGL t.tag K))
      = (t.reeGamma K a).map (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom ⊓
          (Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K))).map
            (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
        rw [hΓ, Subgroup.map_equiv_normalizer_eq, map_conj_reeFixedPosUnipotent hw₀]
    _ = (t.reeGamma K a ⊓
          Subgroup.normalizer (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K))).map
            (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom :=
        (Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective).symm
    _ = t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a := by
        rw [reeGamma_inf_normalizer_reeFixedPosUnipotent, map_conj_reeFixedBorel hw₀]

end Opposite

theorem normalizer_reeFixedPosUnipotent_subgroupOf :
    Subgroup.normalizer (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :
      Subgroup (F4.reeGamma K a)) : Set (F4.reeGamma K a)) =
        (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) := by
  rw [← Subgroup.subgroupOf_normalizer_eq reeFixedPosUnipotent_le_reeGamma,
    ← reeGamma_inf_normalizer_reeFixedPosUnipotent, Subgroup.inf_subgroupOf_left]

theorem normalizer_reeFixedNegUnipotent_subgroupOf
    {w₀ : WeylGroup F4.tag}
    (hw₀ : ∀ w, (coxeterSystem F4.tag).length w ≤ (coxeterSystem F4.tag).length w₀) :
    Subgroup.normalizer (((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) :
      Subgroup (F4.reeGamma K a)) : Set (F4.reeGamma K a)) =
        (F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) := by
  rw [← Subgroup.subgroupOf_normalizer_eq reeFixedNegUnipotent_le_reeGamma,
    ← reeGamma_inf_normalizer_reeFixedNegUnipotent hw₀, Subgroup.inf_subgroupOf_left]

section Blocks

variable {w₀ : WeylGroup F4.tag}
  (hw₀ : ∀ w, (coxeterSystem F4.tag).length w ≤ (coxeterSystem F4.tag).length w₀)
include hw₀

omit hw₀ in
theorem reeFixedTorus_sup_le_reeGamma :
    F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a ≤ F4.reeGamma K a :=
  sup_le (reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma)
    reeFixedNegUnipotent_le_reeGamma

theorem map_conj_reeLocalParabolic_le
    (j : Fin F4.fixedOrbitCount) :
    (F4.reeLocalParabolic K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom ≤ F4.reeGamma K a := by
  have hn := (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  rw [← map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  exact Subgroup.map_mono inf_le_left

theorem minimal_reeFixedBorel_subgroupOf_iff
    (S : Subgroup (F4.reeGamma K a)) :
    Minimal (fun S => (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) < S) S ↔
      S = (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) ∨
        S = (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a) := by
  rw [minimal_subgroupOf_iff reeFixedBorel_le_reeGamma,
    (large_Ree_minimal_Borel_intersections a K w₀ hw₀).1]
  exact or_congr (map_subtype_eq_iff inf_le_left S) (map_subtype_eq_iff inf_le_left S)

theorem minimal_reeFixedTorus_sup_subgroupOf_iff
    (S : Subgroup (F4.reeGamma K a)) :
    Minimal (fun S => (F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a).subgroupOf
      (F4.reeGamma K a) < S) S ↔
      S = ((F4.reeLocalParabolic K a ⟨0, by decide⟩).map
          (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom).subgroupOf
            (F4.reeGamma K a) ∨
        S = ((F4.reeLocalParabolic K a ⟨1, by decide⟩).map
          (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom).subgroupOf
            (F4.reeGamma K a) := by
  rw [minimal_subgroupOf_iff reeFixedTorus_sup_le_reeGamma,
    (large_Ree_minimal_Borel_intersections a K w₀ hw₀).2.2.2.1]
  exact or_congr (map_subtype_eq_iff (map_conj_reeLocalParabolic_le hw₀ _) S)
    (map_subtype_eq_iff (map_conj_reeLocalParabolic_le hw₀ _) S)

theorem map_reeFixedOrbitNegUnipotent_subgroupOf
    {α : MulAut (F4.reeGamma K a)}
    (hα : α ∈ pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)))
    (j : Fin F4.fixedOrbitCount) :
    ((F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeFixedOrbitNegUnipotent K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) ∨
      ((F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeFixedOrbitNegUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a) := by
  have hB : ((F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
      (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) := by
    rw [← normalizer_reeFixedPosUnipotent_subgroupOf]
    exact map_normalizer_of_map_eq α hα.1
  have hmin : Minimal (fun S => (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) < S)
      ((F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a)) := by
    rw [minimal_subgroupOf_iff reeFixedBorel_le_reeGamma, Subgroup.map_subgroupOf_eq_of_le
      (show F4.reeLocalParabolic K a j ≤ F4.reeGamma K a from inf_le_left)]
    exact (minimal_reeFixedBorel_iff _).2 ⟨j, rfl⟩
  have hP := (minimal_reeFixedBorel_subgroupOf_iff hw₀ _).1 (minimal_map_of_map_eq α hB hmin)
  have hY : ∀ i, (F4.reeFixedOrbitNegUnipotent K a i).subgroupOf (F4.reeGamma K a) =
      (F4.reeLocalParabolic K a i).subgroupOf (F4.reeGamma K a) ⊓
        (F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) := fun i => by
    rw [← inf_subgroupOf_eq, reeLocalParabolic_inf_reeFixedNegUnipotent]
  rw [hY, hY, hY, Subgroup.map_inf_eq _ _ _ α.injective, hα.2]
  rcases hP with h | h
  · left
    rw [h]
  · right
    rw [h]

theorem map_reeFixedOrbitUnipotent_subgroupOf
    {α : MulAut (F4.reeGamma K a)}
    (hα : α ∈ pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)))
    (j : Fin F4.fixedOrbitCount) :
    ((F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) ∨
      ((F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a) := by
  have hB : ((F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a).subgroupOf
      (F4.reeGamma K a)).map α.toMonoidHom =
      (F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) := by
    rw [← normalizer_reeFixedNegUnipotent_subgroupOf hw₀]
    exact map_normalizer_of_map_eq α hα.2
  have hmin : Minimal (fun S => (F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a).subgroupOf
      (F4.reeGamma K a) < S)
      (((F4.reeLocalParabolic K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom).subgroupOf
          (F4.reeGamma K a)) := by
    rw [minimal_subgroupOf_iff reeFixedTorus_sup_le_reeGamma,
      Subgroup.map_subgroupOf_eq_of_le (map_conj_reeLocalParabolic_le hw₀ j)]
    exact (minimal_reeFixedTorus_sup_iff hw₀ _).2 ⟨j, rfl⟩
  have hQ := (minimal_reeFixedTorus_sup_subgroupOf_iff hw₀ _).1
    (minimal_map_of_map_eq α hB hmin)
  have hX : ∀ i, (F4.reeFixedOrbitUnipotent K a i).subgroupOf (F4.reeGamma K a) =
      ((F4.reeLocalParabolic K a i).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom).subgroupOf
          (F4.reeGamma K a) ⊓ (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :=
    fun i => by
      rw [← inf_subgroupOf_eq, (large_Ree_minimal_Borel_intersections a K w₀ hw₀).2.2.2.2.2 i]
  rw [hX, hX, hX, Subgroup.map_inf_eq _ _ _ α.injective, hα.1]
  rcases hQ with h | h
  · left
    rw [h]
  · right
    rw [h]

end Blocks

theorem card_reeFixedOrbitUnipotent_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩) = Nat.card K := by
  rw [← SetLike.coe_sort_coe, coe_reeFixedOrbitUnipotent_zero hK]
  exact Nat.card_range_of_injective fun c c' h => (largeRee_x_inj h).1

theorem card_reeFixedOrbitUnipotent_one
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩) = Nat.card K ^ 2 := by
  have hbij : Function.Bijective (fun p : K × K =>
      (⟨largeReeCoord a K p.1 p.2, largeReeCoord_mem hK _ _⟩ :
        F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩)) := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · have h' : largeReeCoord a K p.1 p.2 = largeReeCoord a K q.1 q.2 := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := largeReeCoord_injective h'
      exact Prod.ext h1 h2
    · obtain ⟨t, v, htv⟩ := exists_largeReeCoord_eq hK x.2
      exact ⟨(t, v), Subtype.ext htv⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, sq]

theorem card_reeFixedOrbitNegUnipotent'
    (j : Fin F4.fixedOrbitCount) :
    Nat.card (F4.reeFixedOrbitNegUnipotent K a j) = Nat.card (F4.reeFixedOrbitUnipotent K a j) := by
  rw [← map_conj_reeFixedOrbitUnipotent]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem card_subgroupOf_reeGamma
    {S : Subgroup (ModGL F4.tag K)} (h : S ≤ F4.reeGamma K a) :
    Nat.card (S.subgroupOf (F4.reeGamma K a)) = Nat.card S :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem map_eq_of_card_ne {G : Type*} [Group G] {α : MulAut G}
    (S : Fin F4.fixedOrbitCount → Subgroup G)
    (hS : Nat.card (S ⟨0, by decide⟩) ≠ Nat.card (S ⟨1, by decide⟩))
    (hperm : ∀ j, (S j).map α.toMonoidHom = S ⟨0, by decide⟩ ∨
      (S j).map α.toMonoidHom = S ⟨1, by decide⟩) (j : Fin F4.fixedOrbitCount) :
    (S j).map α.toMonoidHom = S j := by
  have hcard : ∀ i, Nat.card ((S i).map α.toMonoidHom) = Nat.card (S i) := fun i =>
    Subgroup.card_map_of_injective α.injective
  obtain ⟨j, hj⟩ := j
  change j < 2 at hj
  interval_cases j
  · rcases hperm ⟨0, by decide⟩ with h | h
    · exact h
    · exact absurd ((hcard _).symm.trans (congrArg (fun T : Subgroup G => Nat.card T) h)) hS
  · rcases hperm ⟨1, by decide⟩ with h | h
    · exact absurd ((congrArg (fun T : Subgroup G => Nat.card T) h).symm.trans (hcard _)) hS
    · exact h

theorem map_blocks_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {w₀ : WeylGroup F4.tag}
    (hw₀ : ∀ w, (coxeterSystem F4.tag).length w ≤ (coxeterSystem F4.tag).length w₀)
    {α : MulAut (F4.reeGamma K a)}
    (hα : α ∈ pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)))
    (j : Fin F4.fixedOrbitCount) :
    ((F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a) ∧
      ((F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a) := by
  have hq : 1 < Nat.card K := by
    rw [hK]
    exact Nat.one_lt_two_pow (by omega)
  have hqq : Nat.card K ≠ Nat.card K ^ 2 := fun h => by nlinarith
  have hXΓ : ∀ i, F4.reeFixedOrbitUnipotent K a i ≤ F4.reeGamma K a := fun i =>
    (reeFixedOrbitUnipotent_le_reeLocalBlock i).trans (reeLocalBlock_le_reeGamma i)
  have hYΓ : ∀ i, F4.reeFixedOrbitNegUnipotent K a i ≤ F4.reeGamma K a := fun i =>
    (reeFixedOrbitNegUnipotent_le_reeLocalBlock i).trans (reeLocalBlock_le_reeGamma i)
  refine ⟨map_eq_of_card_ne (fun i => (F4.reeFixedOrbitUnipotent K a i).subgroupOf
      (F4.reeGamma K a)) ?_ (map_reeFixedOrbitUnipotent_subgroupOf hw₀ hα) j,
    map_eq_of_card_ne (fun i => (F4.reeFixedOrbitNegUnipotent K a i).subgroupOf
      (F4.reeGamma K a)) ?_ (map_reeFixedOrbitNegUnipotent_subgroupOf hw₀ hα) j⟩
  · show Nat.card ((F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a)) ≠
      Nat.card ((F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a))
    rw [card_subgroupOf_reeGamma (hXΓ _), card_subgroupOf_reeGamma (hXΓ _),
      card_reeFixedOrbitUnipotent_zero hK, card_reeFixedOrbitUnipotent_one hK]
    exact hqq
  · show Nat.card ((F4.reeFixedOrbitNegUnipotent K a ⟨0, by decide⟩).subgroupOf
        (F4.reeGamma K a)) ≠
      Nat.card ((F4.reeFixedOrbitNegUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a))
    rw [card_subgroupOf_reeGamma (hYΓ _), card_subgroupOf_reeGamma (hYΓ _),
      card_reeFixedOrbitNegUnipotent', card_reeFixedOrbitNegUnipotent',
      card_reeFixedOrbitUnipotent_zero hK, card_reeFixedOrbitUnipotent_one hK]
    exact hqq

theorem large_Ree_fixed_group_Schreier
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ α ∈ pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
        ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)),
      ∀ j : Fin F4.fixedOrbitCount,
        ((F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
          (F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a) ∧
        ((F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
          (F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a)) ∧
    (∃ φ : pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
        ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)) →*
        pairAutSubgroup ((F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).subgroupOf
          (F4.reeLocalBlock K a ⟨0, by decide⟩))
          ((F4.reeFixedOrbitNegUnipotent K a ⟨0, by decide⟩).subgroupOf
            (F4.reeLocalBlock K a ⟨0, by decide⟩)) ×
        pairAutSubgroup ((F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩).subgroupOf
          (F4.reeLocalBlock K a ⟨1, by decide⟩))
          ((F4.reeFixedOrbitNegUnipotent K a ⟨1, by decide⟩).subgroupOf
            (F4.reeLocalBlock K a ⟨1, by decide⟩)),
      Function.Injective φ ∧
      (∀ α (m : F4.reeLocalBlock K a ⟨0, by decide⟩),
        ((((φ α).1 : MulAut (F4.reeLocalBlock K a ⟨0, by decide⟩)) m :
          F4.reeLocalBlock K a ⟨0, by decide⟩) : ModGL F4.tag K) =
          (((α : MulAut (F4.reeGamma K a)) ⟨m, reeLocalBlock_le_reeGamma _ m.2⟩ :
            F4.reeGamma K a) : ModGL F4.tag K)) ∧
      (∀ α (m : F4.reeLocalBlock K a ⟨1, by decide⟩),
        ((((φ α).2 : MulAut (F4.reeLocalBlock K a ⟨1, by decide⟩)) m :
          F4.reeLocalBlock K a ⟨1, by decide⟩) : ModGL F4.tag K) =
          (((α : MulAut (F4.reeGamma K a)) ⟨m, reeLocalBlock_le_reeGamma _ m.2⟩ :
            F4.reeGamma K a) : ModGL F4.tag K))) ∧
    derivedSeries (pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a))) 3 = ⊥ ∧
    derivedSeries (Outer (F4.reeGamma K a)) 3 = ⊥ := by
  classical
  let j₀ : Fin F4.fixedOrbitCount := ⟨0, by decide⟩
  let j₁ : Fin F4.fixedOrbitCount := ⟨1, by decide⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  have hMΓ : ∀ j, F4.reeLocalBlock K a j ≤ F4.reeGamma K a := reeLocalBlock_le_reeGamma
  have hXΓ : ∀ i, F4.reeFixedOrbitUnipotent K a i ≤ F4.reeGamma K a := fun i =>
    (reeFixedOrbitUnipotent_le_reeLocalBlock i).trans (hMΓ i)
  have hYΓ : ∀ i, F4.reeFixedOrbitNegUnipotent K a i ≤ F4.reeGamma K a := fun i =>
    (reeFixedOrbitNegUnipotent_le_reeLocalBlock i).trans (hMΓ i)
  set A := pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
    ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a)) with hAdef
  have hM : ∀ {α : MulAut (F4.reeGamma K a)}, α ∈ A → ∀ j,
      ((F4.reeLocalBlock K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeLocalBlock K a j).subgroupOf (F4.reeGamma K a) := by
    intro α hα j
    obtain ⟨hX, hY⟩ := map_blocks_eq hK hw₀ hα j
    have e : (F4.reeLocalBlock K a j).subgroupOf (F4.reeGamma K a) =
        (F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a) ⊔
          (F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a) :=
      Subgroup.subgroupOf_sup (hXΓ j) (hYΓ j)
    rw [e, Subgroup.map_sup, hX, hY]
  have hA01 : A ≤ pairAutSubgroup
      ((F4.reeLocalBlock K a j₀).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalBlock K a j₁).subgroupOf (F4.reeGamma K a)) :=
    fun α hα => ⟨hM hα _, hM hα _⟩
  have hA10 : A ≤ pairAutSubgroup
      ((F4.reeLocalBlock K a j₁).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalBlock K a j₀).subgroupOf (F4.reeGamma K a)) :=
    fun α hα => ⟨hM hα _, hM hα _⟩
  let ψ₀ : A →* MulAut (F4.reeLocalBlock K a j₀) :=
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe (hMΓ j₀))).toMonoidHom.comp
      ((pairAutRestrict _ _).comp (Subgroup.inclusion hA01))
  let ψ₁ : A →* MulAut (F4.reeLocalBlock K a j₁) :=
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe (hMΓ j₁))).toMonoidHom.comp
      ((pairAutRestrict _ _).comp (Subgroup.inclusion hA10))
  have hψ₀ : ∀ (α : A) (m : F4.reeLocalBlock K a j₀),
      ((ψ₀ α m : F4.reeLocalBlock K a j₀) : ModGL F4.tag K) =
        (((α : MulAut (F4.reeGamma K a)) ⟨m, hMΓ _ m.2⟩ : F4.reeGamma K a) :
          ModGL F4.tag K) := fun _ _ => rfl
  have hψ₁ : ∀ (α : A) (m : F4.reeLocalBlock K a j₁),
      ((ψ₁ α m : F4.reeLocalBlock K a j₁) : ModGL F4.tag K) =
        (((α : MulAut (F4.reeGamma K a)) ⟨m, hMΓ _ m.2⟩ : F4.reeGamma K a) :
          ModGL F4.tag K) := fun _ _ => rfl
  have hmem₀ : ∀ α : A, ψ₀ α ∈ pairAutSubgroup
      ((F4.reeFixedOrbitUnipotent K a j₀).subgroupOf
        (F4.reeLocalBlock K a j₀))
      ((F4.reeFixedOrbitNegUnipotent K a j₀).subgroupOf
        (F4.reeLocalBlock K a j₀)) := fun α => by
    obtain ⟨hX, hY⟩ := map_blocks_eq hK hw₀ α.2 j₀
    refine ⟨map_subgroupOf_eq_of_forall _ fun m => ?_, map_subgroupOf_eq_of_forall _ fun m => ?_⟩
    · rw [hψ₀]
      exact apply_mem_iff_of_map_eq hX ⟨m, hMΓ _ m.2⟩
    · rw [hψ₀]
      exact apply_mem_iff_of_map_eq hY ⟨m, hMΓ _ m.2⟩
  have hmem₁ : ∀ α : A, ψ₁ α ∈ pairAutSubgroup
      ((F4.reeFixedOrbitUnipotent K a j₁).subgroupOf
        (F4.reeLocalBlock K a j₁))
      ((F4.reeFixedOrbitNegUnipotent K a j₁).subgroupOf
        (F4.reeLocalBlock K a j₁)) := fun α => by
    obtain ⟨hX, hY⟩ := map_blocks_eq hK hw₀ α.2 j₁
    refine ⟨map_subgroupOf_eq_of_forall _ fun m => ?_, map_subgroupOf_eq_of_forall _ fun m => ?_⟩
    · rw [hψ₁]
      exact apply_mem_iff_of_map_eq hX ⟨m, hMΓ _ m.2⟩
    · rw [hψ₁]
      exact apply_mem_iff_of_map_eq hY ⟨m, hMΓ _ m.2⟩
  let φ := (ψ₀.codRestrict _ hmem₀).prod (ψ₁.codRestrict _ hmem₁)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro α hα1
    have h0 : ψ₀ α = 1 := congrArg Subtype.val (congrArg Prod.fst hα1)
    have h1 : ψ₁ α = 1 := congrArg Subtype.val (congrArg Prod.snd hα1)
    have hfix0 : ∀ m : F4.reeLocalBlock K a j₀,
        (α : MulAut (F4.reeGamma K a)) ⟨m, hMΓ _ m.2⟩ = ⟨m, hMΓ _ m.2⟩ := fun m =>
      Subtype.ext (congrArg (fun β : MulAut (F4.reeLocalBlock K a j₀) =>
        ((β m : F4.reeLocalBlock K a j₀) : ModGL F4.tag K)) h0)
    have hfix1 : ∀ m : F4.reeLocalBlock K a j₁,
        (α : MulAut (F4.reeGamma K a)) ⟨m, hMΓ _ m.2⟩ = ⟨m, hMΓ _ m.2⟩ := fun m =>
      Subtype.ext (congrArg (fun β : MulAut (F4.reeLocalBlock K a j₁) =>
        ((β m : F4.reeLocalBlock K a j₁) : ModGL F4.tag K)) h1)
    have hle : (F4.reeLocalBlock K a j₀ ⊔
        F4.reeLocalBlock K a j₁).subgroupOf (F4.reeGamma K a) ≤
          MonoidHom.eqLocus (α : MulAut (F4.reeGamma K a)).toMonoidHom (MonoidHom.id _) := by
      rw [Subgroup.subgroupOf_sup (hMΓ _) (hMΓ _), sup_le_iff]
      exact ⟨fun x hx => hfix0 ⟨x, hx⟩, fun x hx => hfix1 ⟨x, hx⟩⟩
    rw [← large_Ree_simple_pair_generation a K hK, Subgroup.subgroupOf_self] at hle
    exact Subtype.ext (MulEquiv.ext fun g => hle (Subgroup.mem_top g))
  have hC0 : derivedSeries (pairAutSubgroup
      ((F4.reeFixedOrbitUnipotent K a j₀).subgroupOf
        (F4.reeLocalBlock K a j₀))
      ((F4.reeFixedOrbitNegUnipotent K a j₀).subgroupOf
        (F4.reeLocalBlock K a j₀))) 2 = ⊥ :=
    (large_Ree_A1_pair_automorphism_bound a K hK).2.2.2.2
  have hC1 : derivedSeries (pairAutSubgroup
      ((F4.reeFixedOrbitUnipotent K a j₁).subgroupOf
        (F4.reeLocalBlock K a j₁))
      ((F4.reeFixedOrbitNegUnipotent K a j₁).subgroupOf
        (F4.reeLocalBlock K a j₁))) 3 = ⊥ := by
    have : CharP K 2 := inferInstanceAs (CharP K F4.prime)
    let _ : Module (ZMod 2) K := Module.compHom K (ZMod.castHom (dvd_refl 2) K)
    obtain ⟨-, σ, -, hσ, -, -, -, -⟩ := large_Ree_field_powers a K hK
    exact (large_Ree_B2_pair_automorphism_bound a ha K hK σ fun c => by
      rw [hσ, pow_succ']).2.2
  have hA3 : derivedSeries A 3 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := map_derivedSeries_le_derivedSeries ((MonoidHom.fst _ _).comp φ) 3 ⟨x, hx, rfl⟩
    have h2 := map_derivedSeries_le_derivedSeries ((MonoidHom.snd _ _).comp φ) 3 ⟨x, hx, rfl⟩
    have h1' := derivedSeries_antitone _ (by norm_num : 2 ≤ 3) h1
    rw [hC0, Subgroup.mem_bot] at h1'
    rw [hC1, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    exact hφinj ((Prod.ext h1' h2).trans (map_one φ).symm)
  have hopp := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).2.2.2.2.2
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (F4.reeGamma K a))).comp A.subtype) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨c, β, hU, hV, rfl⟩ := hopp α
    refine ⟨⟨β, ⟨hU, hV⟩⟩, ?_⟩
    have hc : MulAut.conj c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (F4.reeGamma K a) := ⟨c, rfl⟩
    change QuotientGroup.mk' _ β = QuotientGroup.mk' _ (MulAut.conj c * β)
    rw [map_mul, QuotientGroup.mk'_apply _ (MulAut.conj c), (QuotientGroup.eq_one_iff _).2 hc,
      one_mul]
  refine ⟨fun α hα j => map_blocks_eq hK hw₀ hα j, ⟨φ, hφinj, hψ₀, hψ₁⟩, hA3, ?_⟩
  rw [← map_derivedSeries_eq hsurj, hA3, Subgroup.map_bot]

end ReeTag

end CFSG.LieType.Ree
