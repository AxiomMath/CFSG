module

public import CFSG.GroupTheory.InvolutionFixedCentralSylow
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem card_le_two_of_card_centralizer_le_two {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (t : P) (hC : Nat.card (centralizer ({t} : Set P)) ≤ 2) :
    Nat.card P ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hcen : t ∈ center P
  · have htop : centralizer ({t} : Set P) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [mem_centralizer_singleton_iff]
      exact mem_center_iff.mp hcen g
    rw [htop, Subgroup.card_top] at hC
    exact hC
  · by_cases hnt : Nontrivial P
    · have hZ := hP.center_nontrivial
      obtain ⟨⟨c, hcZ⟩, hc1⟩ := exists_ne (1 : center P)
      have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
      have ht1 : t ≠ 1 := by
        rintro rfl
        exact hcen (one_mem _)
      have hct : c ≠ t := by
        rintro rfl
        exact hcen hcZ
      have hsub : ({1, t, c} : Set P) ⊆ (centralizer ({t} : Set P) : Set P) := by
        intro x hx
        rcases hx with rfl | rfl | rfl
        · exact one_mem _
        · exact mem_centralizer_singleton_iff.mpr rfl
        · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hcZ t).symm
      have h3 : ({1, t, c} : Set P).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨1, t, c, ht1.symm, hc1'.symm, hct.symm, rfl⟩
      have hle : ({1, t, c} : Set P).ncard ≤ Nat.card (centralizer ({t} : Set P)) := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    · rw [not_nontrivial_iff_subsingleton] at hnt
      rw [Nat.card_unique]
      omega

theorem isPGroup_zpowers_of_sq_eq_one_two {X : Type*} [Group X] {t : X} (ht : t ^ 2 = 1) :
    IsPGroup 2 (zpowers t) := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ht) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem le_zpowers_of_isPGroup_of_centralizer {X : Type*} [Group X] [Finite X] {Q : Subgroup X}
    (hQ : IsPGroup 2 Q) {t : X} (ht : orderOf t = 2) (htQ : t ∈ normalizer (Q : Set X))
    (hC : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ Q ⊔ zpowers t →
      U ≤ centralizer ({t} : Set X) → Nat.card U ≤ 2) : Q ≤ zpowers t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hzN : zpowers t ≤ normalizer (Q : Set X) := by
    rw [zpowers_le]
    exact htQ
  set H : Subgroup X := Q ⊔ zpowers t with hH
  have hHp : IsPGroup 2 H := IsPGroup.to_sup_of_normal_left' hQ htz hzN
  have htH : t ∈ H := mem_sup_right (mem_zpowers t)
  have hCH : Nat.card (centralizer ({(⟨t, htH⟩ : H)} : Set H)) ≤ 2 := by
    have hU := hC ((centralizer ({(⟨t, htH⟩ : H)} : Set H)).map H.subtype)
      ((hHp.to_subgroup _).map H.subtype) (map_subtype_le _) (by
        rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hx)
    rwa [card_map_of_injective H.subtype_injective] at hU
  have hcardH : Nat.card H ≤ 2 := card_le_two_of_card_centralizer_le_two hHp _ hCH
  have hzH : zpowers t ≤ H := le_sup_right
  have hz2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have heq : zpowers t = H :=
    eq_of_le_of_card_ge hzH (by rw [hz2]; exact hcardH)
  rw [heq]
  exact le_sup_left

theorem subsingleton_of_perfect_of_two_small {E : Type} [Group E] [Finite E]
    (hE : Group.IsPerfect E) (h2 : ∀ U : Subgroup E, IsPGroup 2 U → Nat.card U ≤ 2) :
    Subsingleton E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 E))
  have hR2 : Nat.card (R : Subgroup E) ≤ 2 := h2 R R.isPGroup'
  have hR1 : (R : Subgroup E) = ⊥ := by
    by_contra hne
    have h4 := CFSG.GroupTheory.four_le_index_center_subgroupOf_sylow_two (B := E) R hne
    have hidx : ((center E).subgroupOf (R : Subgroup E)).index ≤ Nat.card (R : Subgroup E) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    omega
  have hodd : Odd (Nat.card E) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (even_iff_two_dvd.mp hev)
    have hxp : IsPGroup 2 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨R', hR'⟩ := hxp.exists_le_sylow
    have hcardR' : Nat.card (R' : Subgroup E) = Nat.card (R : Subgroup E) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have h1 : Nat.card (R : Subgroup E) = 1 := by rw [hR1, Subgroup.card_bot]
    have hle := Subgroup.card_le_of_le hR'
    rw [Nat.card_zpowers, hx, hcardR', h1] at hle
    omega
  have hsol : Group.IsSolvable E := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := E)
  rw [hE.commutator_eq_top] at hlt
  exact lt_irrefl _ hlt

theorem eq_bot_of_perfect_of_centralizer_two_small {X : Type} [Group X] [Finite X]
    {E : Subgroup X} (hE : Group.IsPerfect E) {t : X} (ht : t ^ 2 = 1)
    (hC : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ E ⊔ zpowers t →
      U ≤ centralizer ({t} : Set X) → Nat.card U ≤ 2) : E = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  suffices h2E : ∀ U : Subgroup E, IsPGroup 2 U → Nat.card U ≤ 2 by
    have hsub := subsingleton_of_perfect_of_two_small hE h2E
    rw [eq_bot_iff]
    intro x hx
    have := Subsingleton.elim (⟨x, hx⟩ : E) 1
    exact mem_bot.mpr (congrArg Subtype.val this)
  intro U hU
  set H : Subgroup X := E ⊔ zpowers t with hH
  have htH : t ∈ H := mem_sup_right (mem_zpowers t)
  set t' : H := ⟨t, htH⟩ with ht'
  have ht'2 : t' ^ 2 = 1 := Subtype.ext ht
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_of_sq_eq_one_two ht'2).exists_le_sylow
  have htP : t' ∈ (P : Subgroup H) := hP (mem_zpowers t')
  have hPcard : Nat.card (P : Subgroup H) ≤ 2 := by
    refine card_le_two_of_card_centralizer_le_two P.isPGroup' ⟨t', htP⟩ ?_
    set C : Subgroup (P : Subgroup H) := centralizer ({(⟨t', htP⟩ : (P : Subgroup H))} : Set _)
    have hinj : Function.Injective (H.subtype.comp (P : Subgroup H).subtype) :=
      H.subtype_injective.comp (P : Subgroup H).subtype_injective
    have hU' := hC (C.map (H.subtype.comp (P : Subgroup H).subtype))
      ((P.isPGroup'.to_subgroup C).map _) (by
        rintro _ ⟨x, -, rfl⟩
        exact ((x : (P : Subgroup H)) : H).2) (by
        rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
        rw [mem_centralizer_singleton_iff]
        have := congrArg (fun y : (P : Subgroup H) => ((y : H) : X)) hx
        simpa using this)
    rwa [card_map_of_injective hinj] at hU'
  have hUH : IsPGroup 2 ((U.map E.subtype).subgroupOf H) :=
    ((hU.map E.subtype).comap_of_injective H.subtype H.subtype_injective)
  obtain ⟨P', hP'⟩ := hUH.exists_le_sylow
  have hcardP' : Nat.card (P' : Subgroup H) = Nat.card (P : Subgroup H) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hle : Nat.card ((U.map E.subtype).subgroupOf H) ≤ Nat.card (P' : Subgroup H) :=
    Subgroup.card_le_of_le hP'
  have hUle : U.map E.subtype ≤ H := (map_subtype_le U).trans le_sup_left
  rw [Nat.card_congr (subgroupOfEquivOfLe hUle).toEquiv,
    card_map_of_injective E.subtype_injective] at hle
  omega

theorem conj_ne_of_card_le {G : Type*} [Group G] [Finite G] {a w : G} {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPa : P ≤ centralizer ({a} : Set G)) {N : ℕ} (hN : N ≤ Nat.card P)
    (hw : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer ({w} : Set G) → Nat.card Q < N)
    (g : G) : g * a * g⁻¹ ≠ w := by
  intro hga
  have hQ := hw (P.map (MulAut.conj g).toMonoidHom) (hP.map _) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hxa : x * a = a * x := mem_centralizer_singleton_iff.mp (hPa hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hga]
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group)
  rw [card_map_of_injective (MulAut.conj g).injective] at hQ
  omega

theorem card_lt_of_centralizer_eq_bot {K : Type*} [Group K] [Finite K] {J : Subgroup K}
    [J.Normal] (hJ : centralizer (J : Set K) = ⊥) {P : Subgroup K} (hP : IsPGroup 2 P) {N : ℕ}
    (hAut : ∀ Q : Subgroup (MulAut J), IsPGroup 2 Q → Nat.card Q < N) : Nat.card P < N := by
  have hinj : Function.Injective (MulAut.conjNormal : K →* MulAut J) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ centralizer (J : Set K) := by
      rw [mem_centralizer_iff]
      intro j hj
      have := congrArg (fun φ : MulAut J => ((φ ⟨j, hj⟩ : J) : K)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc j * g = g * j * g⁻¹ * g := by rw [this]
        _ = g * j := by group
    rw [hJ] at hgC
    exact mem_bot.mp hgC
  have h := hAut (P.map MulAut.conjNormal) (hP.map _)
  rwa [card_map_of_injective hinj] at h

end CFSG.SeitzReduction.RankOne
