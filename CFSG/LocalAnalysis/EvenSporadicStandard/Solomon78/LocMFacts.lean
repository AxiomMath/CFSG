module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHPrim
public import CFSG.Monster.Existence.Compat.Two

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Blueprint

section Transport

variable {X X' : Type} [Group X] [Group X']

@[expose] def centMapEquiv (φ : X ≃* X') (a : X) :
    ↥(centralizer ({a} : Set X)) ≃* ↥(centralizer ({φ a} : Set X')) where
  toFun x := ⟨φ (x : X), mem_centralizer_singleton_iff.2 (by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 x.2])⟩
  invFun y := ⟨φ.symm (y : X'), mem_centralizer_singleton_iff.2 (φ.injective (by
    have := mem_centralizer_singleton_iff.1 y.2
    simpa using this))⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply (x : X))
  right_inv y := Subtype.ext (φ.apply_symm_apply (y : X'))
  map_mul' x y := Subtype.ext (map_mul φ (x : X) (y : X))

theorem centMapEquiv_apply (φ : X ≃* X') (a : X) (x : ↥(centralizer ({a} : Set X))) :
    ((centMapEquiv φ a x : ↥(centralizer ({φ a} : Set X'))) : X') = φ (x : X) := rfl

theorem card_centralizer_map (φ : X ≃* X') (a : X) :
    Nat.card ↥(centralizer ({φ a} : Set X')) = Nat.card ↥(centralizer ({a} : Set X)) :=
  (Nat.card_congr (centMapEquiv φ a).toEquiv).symm

theorem map_centralizer_equiv (φ : X ≃* X') (a : X) :
    (centralizer ({a} : Set X)).map (φ : X →* X') = centralizer ({φ a} : Set X') := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_centralizer_singleton_iff.2 (by
      show φ x * φ a = φ a * φ x
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx])
  · intro hw
    refine ⟨φ.symm w, mem_centralizer_singleton_iff.2 (φ.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact mem_centralizer_singleton_iff.1 hw)), by simp⟩

theorem isCoatom_centralizer_map_iff (φ : X ≃* X') (a : X) :
    IsCoatom (centralizer ({φ a} : Set X')) ↔ IsCoatom (centralizer ({a} : Set X)) := by
  rw [← map_centralizer_equiv φ a]
  simpa using OrderIso.isCoatom_iff φ.mapSubgroup (centralizer ({a} : Set X))

theorem IsTwoACentralizer.map (φ : X ≃* X') {a : X} (h : IsTwoACentralizer a) :
    IsTwoACentralizer (φ a) := by
  obtain ⟨hp, hz, ⟨e⟩⟩ := h
  let f := centMapEquiv φ a
  have hcenter : (center ↥(centralizer ({a} : Set X))).map f.toMonoidHom =
      center ↥(centralizer ({φ a} : Set X')) := Subgroup.map_center_eq f
  refine ⟨Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective, ?_,
    ⟨(QuotientGroup.congr _ _ f hcenter).symm.trans e⟩⟩
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : f.symm g ∈ center ↥(centralizer ({a} : Set X)) := by
      rw [← hcenter] at hg
      obtain ⟨w, hw, rfl⟩ := hg
      simpa using hw
    have hmem : ((f.symm g : ↥(centralizer ({a} : Set X))) : X) ∈ zpowers a := hz ▸ ⟨_, hg', rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : φ ((f.symm g : ↥(centralizer ({a} : Set X))) : X) = ((g : _) : X') := by
      have := centMapEquiv_apply φ a (f.symm g)
      rw [f.apply_symm_apply] at this
      exact this.symm
    show (φ a) ^ k = ((g : ↥(centralizer ({φ a} : Set X'))) : X')
    rw [← h1, ← hk, map_zpow]
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have hak : a ^ k ∈ (center ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype := hz ▸ zpow_mem (mem_zpowers a) k
    obtain ⟨w, hw, hwa⟩ := hak
    refine ⟨f w, ?_, ?_⟩
    · rw [← hcenter]
      exact ⟨w, hw, rfl⟩
    · show φ (w : X) = (φ a) ^ k
      rw [show ((w : ↥(centralizer ({a} : Set X))) : X) = a ^ k from hwa, map_zpow]

end Transport

theorem card_centralizer_of_isTwoACentralizer {X : Type} [Group X] {a : X} (ha : orderOf a = 2)
    (h : IsTwoACentralizer a) (F : TwoAFacts) :
    Nat.card ↥(centralizer ({a} : Set X)) = 2 * monsterBabyOrder := by
  obtain ⟨-, hz, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center ↥(centralizer ({a} : Set X)))
  have hc : Nat.card ↥(center ↥(centralizer ({a} : Set X))) = 2 := by
    rw [← Subgroup.card_map_of_injective (centralizer ({a} : Set X)).subtype_injective, hz,
      Nat.card_zpowers, ha]
  rw [Nat.card_congr e.toEquiv, F.b_card, hc] at h1
  omega

theorem isCoatom_centralizer_of_isConj {X : Type} [Group X] {a b : X} (h : IsConj a b)
    (ha : IsCoatom (centralizer ({a} : Set X))) : IsCoatom (centralizer ({b} : Set X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have := (isCoatom_centralizer_map_iff (MulAut.conj c) a).2 ha
  rwa [MulAut.conj_apply, hc] at this

theorem monsterFacts_of_existence {X : Type} [Group X] (h : MonsterExistenceStatement X)
    (F : TwoAFacts) (hB : AllInner NativeSporadic.B) (hX : AllInner X) : MonsterFacts X := by
  obtain ⟨⟨hfin, hsimple, hnab, hcard⟩, a, z, ha, hz, hnc, hinv, hA, hBz, hgraph⟩ := h
  have hgraph' : MonsterTwoAGraphData a z := monsterTwoAGraphData_of_isTwoAGraphData F ha hgraph
  have hcoat : IsCoatom (centralizer ({a} : Set X)) :=
    haveI := hfin
    isCoatom_centralizer_of_monsterTwoAGraphData hcard ha hgraph'
  refine ⟨hsimple, hnab, hcard, ?_, hX, F.b_simple, hB⟩
  intro u hu2 hge
  rcases hinv u hu2 with h1 | h1
  · have hu : IsTwoACentralizer u := hA u h1
    exact ⟨hu, card_centralizer_of_isTwoACentralizer hu2 hu F,
      isCoatom_centralizer_of_isConj h1 hcoat⟩
  · exfalso
    have h2 := (hBz u h1).2.2.2.2.1
    rw [h2] at hge
    unfold twoBCentralizerOrder monsterBabyOrder at hge
    norm_num at hge

theorem MonsterFacts.of_mulEquiv {Y X : Type} [Group Y] [Group X] (φ : Y ≃* X)
    (hX : MonsterFacts X) (hY : AllInner Y) : MonsterFacts Y where
  simple := @MulEquiv.isSimpleGroup _ _ _ _ hX.simple φ
  nonabelian := by
    obtain ⟨a, b, hab⟩ := hX.nonabelian
    exact ⟨φ.symm a, φ.symm b, fun hc => hab (by simpa using congrArg φ hc)⟩
  card := by
    rw [Nat.card_congr φ.toEquiv]
    exact hX.card
  twoA := by
    intro u hu2 hge
    have hu2' : orderOf (φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu2
    have hge' : 2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({φ u} : Set X)) := by
      rw [card_centralizer_map]
      exact hge
    obtain ⟨hA, hC, hcoat⟩ := hX.twoA (φ u) hu2' hge'
    refine ⟨?_, ?_, (isCoatom_centralizer_map_iff φ u).1 hcoat⟩
    · simpa using IsTwoACentralizer.map φ.symm hA
    · rw [← card_centralizer_map φ u]
      exact hC
  allInner := hY
  baby_simple := hX.baby_simple
  baby_allInner := hX.baby_allInner

end CFSG.EvenSporadicStandard.Solomon78
