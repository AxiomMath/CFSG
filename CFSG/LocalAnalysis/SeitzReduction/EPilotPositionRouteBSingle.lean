module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteBAut

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le)

section Centralizers

variable {G : Type*} [Group G]

theorem conj_inf_centralizer_eq {A B : Subgroup G} {q : G} (hq : q ∈ A) :
    (A ⊓ centralizer (B : Set G)).map (MulAut.conj q).toMonoidHom =
      A ⊓ centralizer ((B.map (MulAut.conj q).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyA, hyB⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨?_, mem_centralizer_iff.2 ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact A.mul_mem (A.mul_mem hq hyA) (A.inv_mem hq)
    · rintro _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h := mem_centralizer_iff.1 hyB b hb
      calc q * b * q⁻¹ * (q * y * q⁻¹) = q * (b * y) * q⁻¹ := by group
        _ = q * (y * b) * q⁻¹ := by rw [h]
        _ = q * y * q⁻¹ * (q * b * q⁻¹) := by group
  · intro hx
    obtain ⟨hxA, hxB⟩ := mem_inf.1 hx
    refine ⟨q⁻¹ * x * q, mem_inf.2 ⟨A.mul_mem (A.mul_mem (A.inv_mem hq) hxA) hq,
      mem_centralizer_iff.2 ?_⟩, ?_⟩
    · intro b hb
      have h := mem_centralizer_iff.1 hxB (q * b * q⁻¹)
        ⟨b, hb, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      calc b * (q⁻¹ * x * q) = q⁻¹ * ((q * b * q⁻¹) * x) * q := by group
        _ = q⁻¹ * (x * (q * b * q⁻¹)) * q := by rw [h]
        _ = q⁻¹ * x * q * b := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem map_inf_centralizer_eq_of_injective {C : Type*} [Group C] {φ : C →* G}
    (hφ : Function.Injective φ) (A B : Subgroup C) :
    (A ⊓ centralizer (B : Set C)).map φ =
      A.map φ ⊓ centralizer ((B.map φ : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyA, hyB⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨⟨y, hyA, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hyB b hb]
  · intro hx
    obtain ⟨⟨y, hyA, rfl⟩, hyB⟩ := mem_inf.1 hx
    refine ⟨y, mem_inf.2 ⟨hyA, mem_centralizer_iff.2 fun b hb => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hyB (φ b) ⟨b, hb, rfl⟩

theorem card_inf_centralizer_eq_of_le_conj [Finite G] {C : Type*} [Group C] {φ φ' : C →* G}
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') {Q J J' : Subgroup C}
    (hQ : Q.map φ = Q.map φ') {q₀ : G} (hq₀ : q₀ ∈ Q.map φ)
    (hX : J.map φ ≤ (J'.map φ').map (MulAut.conj q₀).toMonoidHom)
    (hcard : Nat.card J' = Nat.card J) :
    Nat.card (Q ⊓ centralizer (J' : Set C) : Subgroup C) =
      Nat.card (Q ⊓ centralizer (J : Set C) : Subgroup C) := by
  have hXeq : J.map φ = (J'.map φ').map (MulAut.conj q₀).toMonoidHom := by
    refine eq_of_le_of_card_ge hX ?_
    rw [card_map_of_injective (MulAut.conj q₀).injective, card_map_of_injective hφ',
      card_map_of_injective hφ, hcard]
  calc Nat.card (Q ⊓ centralizer (J' : Set C) : Subgroup C)
      = Nat.card ((Q ⊓ centralizer (J' : Set C)).map φ') := (card_map_of_injective hφ').symm
    _ = Nat.card (Q.map φ ⊓ centralizer ((J'.map φ' : Subgroup G) : Set G) : Subgroup G) := by
        rw [map_inf_centralizer_eq_of_injective hφ', hQ]
    _ = Nat.card ((Q.map φ ⊓ centralizer ((J'.map φ' : Subgroup G) : Set G)).map
          (MulAut.conj q₀).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj q₀).injective).symm
    _ = Nat.card (Q.map φ ⊓ centralizer ((J.map φ : Subgroup G) : Set G) : Subgroup G) := by
        rw [conj_inf_centralizer_eq hq₀, ← hXeq]
    _ = Nat.card ((Q ⊓ centralizer (J : Set C)).map φ) := by
        rw [map_inf_centralizer_eq_of_injective hφ]
    _ = Nat.card (Q ⊓ centralizer (J : Set C) : Subgroup C) := card_map_of_injective hφ

end Centralizers

section RouteB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_le_centralizer_mulEquiv_of_coords_single (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {z₀ : C} {g : G}
    (hg : g⁻¹ * t * g = (e.symm z₀ : G) ∨ g⁻¹ * t * g = t * (e.symm z₀ : G))
    {φ' : C →* G} (hφ' : Function.Injective φ') (hφ'r : φ'.range = CFSG.conjugate L g)
    (hact : ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = φ' z₀ * l * (φ' z₀)⁻¹)
    (Qz Mz : Subgroup C) (hF3 : perfectCore (centralizer ({z₀} : Set C)) = Qz ⊔ Mz)
    (hQ : IsPGroup 2 Qz) (hMN : Mz ≤ normalizer (Qz : Set C)) (hQM : Disjoint Qz Mz)
    (hM : ∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : J ≤ Mz) (hJo : Odd (Nat.card J)) {D : Type*} [Group D]
    (hF6 : ∀ ι : Mz ≃* Mz,
      Nat.card (Qz ⊓ centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map Mz.subtype :
          Subgroup C) : Set C) : Subgroup C) =
        Nat.card (Qz ⊓ centralizer (J : Set C) : Subgroup C) →
      Nonempty (perfectCore (centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map
        Mz.subtype : Subgroup C) : Set C)) ≃* D)) :
    ∃ P : Subgroup G, P ≤ CFSG.conjugate L g ⊓
        centralizer (((J.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) ∧
      Nonempty (P ≃* D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := range_subtype_comp_mulEquiv_symm e
  have hΛ := map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r hg hact
  rw [hF3] at hΛ
  have hX2 : ¬ 2 ∣ Nat.card (J.map φ) := by
    rw [card_map_of_injective hφ]
    exact fun h => (Nat.not_even_iff_odd.2 hJo) (even_iff_two_dvd.2 h)
  obtain ⟨hQeq, ι, -, q₀, hq₀, hXq⟩ := exists_conj_le_map_of_two_decompositions hφ hφ'
    hQ hQ hM hM hMN hMN hQM hQM hΛ hJ le_rfl hX2
  set J' : Subgroup C := ((J.subgroupOf Mz).map ι.toMonoidHom).map Mz.subtype with hJ'def
  have hcardJ' : Nat.card J' = Nat.card J := by
    rw [hJ'def, card_map_of_injective Mz.subtype_injective, card_map_of_injective ι.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hJ).toEquiv
  obtain ⟨eD⟩ := hF6 ι (card_inf_centralizer_eq_of_le_conj hφ hφ' hQeq hq₀ hXq hcardJ')
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨n, -, rfl⟩ := hq₀
    exact ⟨n, rfl⟩
  have hXJ : (J.map e.symm.toMonoidHom).map L.subtype = J.map φ := by
    rw [hφdef, Subgroup.map_map]
  refine ⟨((perfectCore (centralizer (J' : Set C))).map φ').map (MulAut.conj q₀).toMonoidHom,
    le_inf ?_ ?_, ⟨?_⟩⟩
  · rw [← hφ'r]
    rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    obtain ⟨n', rfl⟩ := hq₀'
    exact ⟨n' * c * n'⁻¹, by simp [MulAut.conj_apply]⟩
  · rw [hXJ]
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨_, ⟨j, hj, rfl⟩, hjx⟩ := hXq hx
    have hcj := mem_centralizer_iff.1 (perfectCore_le _ hc) j hj
    have hφc : φ' j * φ' c = φ' c * φ' j := by rw [← map_mul, ← map_mul, hcj]
    rw [← hjx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc q₀ * φ' j * q₀⁻¹ * (q₀ * φ' c * q₀⁻¹) = q₀ * (φ' j * φ' c) * q₀⁻¹ := by group
      _ = q₀ * (φ' c * φ' j) * q₀⁻¹ := by rw [hφc]
      _ = q₀ * φ' c * q₀⁻¹ * (q₀ * φ' j * q₀⁻¹) := by group
  · exact (((perfectCore (centralizer (J' : Set C))).map φ').equivMapOfInjective _
      (MulAut.conj q₀).injective).symm.trans
      (((perfectCore (centralizer (J' : Set C))).equivMapOfInjective _ hφ').symm.trans eD)

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_single (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {z₀ : C} {g : G} (hg : g⁻¹ * t * g = t * (e.symm z₀ : G))
    (hinner : ∃ c : C, ∀ l ∈ CFSG.conjugate L g,
      t * l * t⁻¹ = (g⁻¹ * (e.symm (c * z₀ * c⁻¹) : G) * g) * l *
        (g⁻¹ * (e.symm (c * z₀ * c⁻¹) : G) * g)⁻¹)
    (Qz Mz : Subgroup C) (hF3 : perfectCore (centralizer ({z₀} : Set C)) = Qz ⊔ Mz)
    (hQ : IsPGroup 2 Qz) (hMN : Mz ≤ normalizer (Qz : Set C)) (hQM : Disjoint Qz Mz)
    (hM : ∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : J ≤ Mz) (hJo : Odd (Nat.card J)) {D : Type*} [Group D]
    (hF6 : ∀ ι : Mz ≃* Mz,
      Nat.card (Qz ⊓ centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map Mz.subtype :
          Subgroup C) : Set C) : Subgroup C) =
        Nat.card (Qz ⊓ centralizer (J : Set C) : Subgroup C) →
      Nonempty (perfectCore (centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map
        Mz.subtype : Subgroup C) : Set C)) ≃* D)) :
    ∃ P : Subgroup G, P ≤ centralizer (((J.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
        Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧ Nonempty (P ≃* D) := by
  have htC := mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  obtain ⟨c, hc⟩ := hinner
  obtain ⟨φ', hφ', hφ'r, hφ'z⟩ := exists_coords_conjugate e g (x' := c * z₀ * c⁻¹) (y' := z₀)
    (c' := c⁻¹) (by group)
  obtain ⟨P, hP, hPD⟩ := exists_le_centralizer_mulEquiv_of_coords_single hset hOut e ht htC
    (Or.inr hg) hφ' hφ'r (by rw [hφ'z]; exact hc) Qz Mz hF3 hQ hMN hQM hM hJ hJo hF6
  exact ⟨P, le_inf (hP.trans inf_le_right)
    ((hP.trans inf_le_left).trans (conjugate_le_centralizer_conj htC g)), hPD⟩

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_single_of_isConj
    (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C]
    (e : L ≃* C) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {z₀ : C} {g : G} (hg : g⁻¹ * t * g = t * (e.symm z₀ : G))
    (hinner : ∃ w' : G, ∃ hw' : g * w' * g⁻¹ ∈ L,
      (∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹) ∧
        IsConj (e ⟨g * w' * g⁻¹, hw'⟩) z₀)
    (Qz Mz : Subgroup C) (hF3 : perfectCore (centralizer ({z₀} : Set C)) = Qz ⊔ Mz)
    (hQ : IsPGroup 2 Qz) (hMN : Mz ≤ normalizer (Qz : Set C)) (hQM : Disjoint Qz Mz)
    (hM : ∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : J ≤ Mz) (hJo : Odd (Nat.card J)) {D : Type*} [Group D]
    (hF6 : ∀ ι : Mz ≃* Mz,
      Nat.card (Qz ⊓ centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map Mz.subtype :
          Subgroup C) : Set C) : Subgroup C) =
        Nat.card (Qz ⊓ centralizer (J : Set C) : Subgroup C) →
      Nonempty (perfectCore (centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map
        Mz.subtype : Subgroup C) : Set C)) ≃* D)) :
    ∃ P : Subgroup G, P ≤ centralizer (((J.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
        Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧ Nonempty (P ≃* D) := by
  obtain ⟨w', hw', hact, hconj⟩ := hinner
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  refine exists_le_centralizer_mulEquiv_of_conj_eq_mul_single hset hOut e ht hKt hg
    ⟨c⁻¹, ?_⟩ Qz Mz hF3 hQ hMN hQM hM hJ hJo hF6
  have hw : (g⁻¹ * (e.symm (c⁻¹ * z₀ * c⁻¹⁻¹) : G) * g) = w' := by
    have h1 : c⁻¹ * z₀ * c⁻¹⁻¹ = e ⟨g * w' * g⁻¹, hw'⟩ := by
      rw [← hc]
      group
    rw [h1, MulEquiv.symm_apply_apply]
    group
  rw [hw]
  exact hact

end RouteB

end CFSG.SeitzReduction.EPilot
