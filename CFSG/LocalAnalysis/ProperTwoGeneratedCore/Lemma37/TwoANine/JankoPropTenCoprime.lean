module

public import CFSG.GroupTheory.CoprimeNormalizedSylowIntersection
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimewiseScalarInvolution
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Walter.J1.Tools

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G]

theorem exists_oddNormal {C : Subgroup G}
    (hC : ∀ B : Subgroup G, B ≤ C → IsPGroup 2 B → Nat.card B ≤ 2) :
    ∃ W : Subgroup G, W ≤ C ∧ C ≤ normalizer (W : Set G) ∧ Odd (Nat.card W) ∧
      ∀ R : Subgroup G, R ≤ C → Odd (Nat.card R) → R ≤ W := by
  by_cases hodd : Odd (Nat.card C)
  · exact ⟨C, le_rfl, Subgroup.le_normalizer, hodd, fun R hR _ => hR⟩
  have heven : 2 ∣ Nat.card C := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hPle : Nat.card P ≤ 2 := by
    have := hC ((P : Subgroup C).map C.subtype) (map_subtype_le _) (P.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective C.subtype_injective] at this
  have hPdvd : Nat.card P ∣ 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn] at hPle ⊢
    rcases n with _ | _ | n
    · norm_num
    · norm_num
    · exfalso; rw [pow_succ, pow_succ] at hPle
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
  have hcyc : IsCyclic P := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hPdvd with h1 | h2
    · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp h1).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card h2
  have hp : (Nat.card C).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
  have hK := IsCyclic.isComplement' hp hcyc
  set K := (MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hp)).ker
  have hKn : K.Normal := MonoidHom.normal_ker _
  refine ⟨K.map C.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · calc C = (⊤ : Subgroup C).map C.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (normalizer (K : Set C)).map C.subtype := by rw [Subgroup.normalizer_eq_top]
      _ ≤ _ := Subgroup.le_normalizer_map _
  · rw [Subgroup.card_map_of_injective C.subtype_injective, ← hK.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp P.not_dvd_index)
  · intro R hRC hR x hx
    have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hR (Subgroup.orderOf_dvd_natCard R hx)
    set x' : C := ⟨x, hRC hx⟩
    have h1 : orderOf (QuotientGroup.mk' K x') ∣ 2 := by
      refine (_root_.orderOf_dvd_natCard _).trans ?_
      have : Nat.card (C ⧸ K) = Nat.card P := hK.symm.index_eq_card
      rw [this]; exact hPdvd
    have h2 : Odd (orderOf (QuotientGroup.mk' K x')) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd _ x')
      rwa [Subgroup.orderOf_mk]
    have h3 : orderOf (QuotientGroup.mk' K x') = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at h2; exact absurd h2 (by decide)
    have hxK : x' ∈ K := by
      rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact h3
    exact ⟨x', hxK, rfl⟩

theorem card_le_of_coprime {W X Y : Subgroup G} {t : G} (ht : t * t = 1)
    (hW : Odd (Nat.card W)) (htW : t ∈ normalizer (W : Set G)) (hX : IsSylowOf W 3 X)
    (htX : t ∈ normalizer (X : Set G)) (hY : IsPGroup 3 Y) (hYW : Y ≤ W)
    (hYt : Y ≤ centralizer ({t} : Set G)) :
    Nat.card Y ≤ Nat.card (X ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := hX
  set A : Subgroup G := zpowers t
  have hAW : A ≤ normalizer (W : Set G) := (zpowers_le).mpr htW
  have hAX : A ≤ normalizer (X : Set G) := (zpowers_le).mpr htX
  let := Walter.J1.conjAct A W hAW
  have hA2 : IsPGroup 2 A := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (t ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, ht, one_zpow]
  have hp : ¬ 2 ∣ Nat.card W := fun h2 =>
    (Nat.not_even_iff_odd.mpr hW) (even_iff_two_dvd.mpr h2)
  set H : Subgroup W := (centralizer ({t} : Set G)).subgroupOf W
  have hPmem : ∀ x : W, x ∈ (P : Subgroup W) ↔ (x : G) ∈ X := fun x => by
    rw [← hP]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => (Subtype.ext hyx : y = x) ▸ hy⟩
  have hPinv : ∀ a : A, ∀ x ∈ (P : Subgroup W), a • x ∈ (P : Subgroup W) := by
    intro a x hx
    rw [hPmem] at hx ⊢
    exact (mem_normalizer_iff.mp (hAX a.2) x).mp hx
  have hHinv : ∀ a : A, ∀ x ∈ H, a • x ∈ H := by
    intro a x hx
    obtain ⟨k, hk⟩ := a.2
    have hxt : (x : G) * t = t * x := mem_centralizer_singleton_iff.mp hx
    have hxa : (a : G) * x * (a : G)⁻¹ = x := by
      rw [← hk, (Commute.zpow_left hxt.symm k).eq, mul_inv_cancel_right]
    change ((a : G) * x * (a : G)⁻¹) ∈ centralizer ({t} : Set G)
    rw [hxa]; exact hx
  have hCH : fixedPointSubgroup A W ≤ normalizer (H : Set W) := by
    intro x hx
    refine Subgroup.le_normalizer ?_
    have h1 := congrArg Subtype.val (hx ⟨t, mem_zpowers t⟩)
    change t * (x : G) * t⁻¹ = x at h1
    change (x : G) ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h1]
      _ = t * x := by group
  obtain ⟨⟨R, hR⟩, -⟩ := CFSG.GroupTheory.coprime_normalized_sylow_intersection (p := 2) (q := 3)
    hA2 hp P hPinv H hHinv hCH
  have hYH : Y.subgroupOf W ≤ H := fun y hy => hYt hy
  set Y' : Subgroup H := (Y.subgroupOf W).subgroupOf H
  have hY'card : Nat.card Y' = Nat.card Y := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYW).toEquiv]
  have hY' : IsPGroup 3 Y' := (hY.comap_subtype (K := W)).comap_subtype
  obtain ⟨R', hR'⟩ := hY'.exists_le_sylow
  have hRcard : Nat.card R = Nat.card (X ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    have e1 : Nat.card R = Nat.card ((P : Subgroup W) ⊓ H : Subgroup W) := by
      rw [← hR, Subgroup.card_map_of_injective H.subtype_injective]
    have e2 : ((P : Subgroup W) ⊓ H).map W.subtype = X ⊓ centralizer ({t} : Set G) := by
      rw [Subgroup.map_inf_eq _ _ _ W.subtype_injective, hP, Subgroup.subgroupOf_map_subtype]
      have hXW : X ≤ W := le_of_isSylowOf ⟨P, hP⟩
      ext x
      simp only [mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hXW h.1⟩⟩
    rw [e1, ← e2, Subgroup.card_map_of_injective W.subtype_injective]
  calc Nat.card Y = Nat.card Y' := hY'card.symm
    _ ≤ Nat.card R' := Subgroup.card_le_of_le hR'
    _ = Nat.card R := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ = _ := hRcard

omit [Finite G] in
theorem centralizer_singleton_le (q : G) :
    centralizer ({q} : Set G) ≤ centralizer (zpowers q : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp hx).symm k).eq

omit [Finite G] in
theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x).symm

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen
