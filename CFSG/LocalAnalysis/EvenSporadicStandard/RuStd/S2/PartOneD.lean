module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Interfaces
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.PartOneAux

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

@[expose] def A5Lemma : Prop :=
  ∀ {D : Type} [Group D], (D ≃* A5) → ∀ U : Subgroup D, Nat.card U = 4 →
    ∃ r ∈ normalizer (U : Set D), orderOf r = 3 ∧ ∃ x ∈ U, r * x * r⁻¹ ≠ x

variable {G : Type} [Group G]

theorem exists_two_ne_one {V : Subgroup G} (hV4 : Nat.card V = 4) :
    ∃ a ∈ V, a ≠ 1 ∧ ∃ b ∈ V, b ≠ 1 ∧ b ≠ a := by
  have key : ∀ (c : G), ∃ x ∈ V, x ≠ 1 ∧ x ≠ c := by
    intro c
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set G) ⊆ {1, c} := fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, c} : Set G).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp [Set.ncard_singleton])
    have h3 : Nat.card V = (V : Set G).ncard := (Nat.card_coe_set_eq _)
    omega
  obtain ⟨a, ha, ha1, -⟩ := key 1
  obtain ⟨b, hb, hb1, hba⟩ := key a
  exact ⟨a, ha, ha1, b, hb, hb1, hba⟩

theorem comm_of_sq_one {V : Subgroup G} (hV2 : ∀ x ∈ V, x * x = 1) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) : x * y = y * x := by
  have hxy := hV2 (x * y) (mul_mem hx hy)
  have e1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hV2 x hx)
  have e2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hV2 y hy)
  have e3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, e1, e2] at e3
  exact e3.symm

theorem map_centralizer_subtype (Y : Subgroup G) {f : G} (hf : f ∈ Y) :
    (centralizer ({(⟨f, hf⟩ : Y)} : Set Y)).map Y.subtype = Y ⊓ centralizer ({f} : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))⟩
  · rintro ⟨hyY, hyf⟩
    exact ⟨⟨y, hyY⟩, mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_singleton_iff.1 hyf)), rfl⟩

theorem typeA_data {Y : Subgroup G} (hY : RuFiveFacts Y) {f : G} (hfY : f ∈ Y)
    (hf5 : orderOf f = 5) {V : Subgroup G} (hVY : V ≤ Y) (hV4 : Nat.card V = 4)
    (hV2 : ∀ x ∈ V, x * x = 1) (hVf : ∀ x ∈ V, x * f = f * x) :
    ∃ D : Subgroup G, D ≤ Y ∧ Nonempty (↥D ≃* A5) ∧ D ≤ centralizer ({f} : Set G) ∧
      Y ⊓ centralizer ({f} : Set G) = zpowers f ⊔ D ∧ Disjoint (zpowers f) D ∧ V ≤ D ∧
      Nat.card (centralizer ({(⟨f, hfY⟩ : Y)} : Set Y)) = 300 := by
  set fY : Y := ⟨f, hfY⟩ with hfYdef
  have hfY5 : orderOf fY = 5 := by
    rw [← Subgroup.orderOf_coe]; exact hf5
  obtain ⟨a, ha, ha1, b, hb, hb1, hba⟩ := exists_two_ne_one hV4
  have hord : ∀ x ∈ V, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hV2 x hx) hx1
  have hkl : HasKlein ((centralizer ({fY} : Set Y) : Subgroup Y) : Set Y) := by
    unfold HasKlein
    refine ⟨⟨a, hVY ha⟩, ?_, ⟨b, hVY hb⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact mem_centralizer_singleton_iff.2 (Subtype.ext (hVf a ha))
    · exact mem_centralizer_singleton_iff.2 (Subtype.ext (hVf b hb))
    · rw [Subgroup.orderOf_mk]; exact hord a ha ha1
    · rw [Subgroup.orderOf_mk]; exact hord b hb hb1
    · intro h1; exact hba (congrArg Subtype.val h1).symm
    · exact Subtype.ext (comm_of_sq_one hV2 ha hb)
  have h300 : Nat.card (centralizer ({fY} : Set Y)) = 300 := by
    rcases hY.typeAB fY hfY5 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd hkl h2
  obtain ⟨DY, hDYiso, hDYle, hDYeq, hDYdisj⟩ := hY.typeA fY hfY5 h300
  refine ⟨DY.map Y.subtype, ?_, ?_, ?_, ?_, ?_, ?_, h300⟩
  · rintro _ ⟨d, -, rfl⟩; exact d.2
  · obtain ⟨e⟩ := hDYiso
    exact ⟨(DY.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hDYle hd)))
  · rw [← map_centralizer_subtype Y hfY, hDYeq, Subgroup.map_sup, MonoidHom.map_zpowers]; rfl
  · rw [Subgroup.disjoint_def]
    rintro x hx ⟨d, hd, rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
    have hdk : d = fY ^ k := Subtype.ext (by simpa using hk.symm)
    have : d ∈ zpowers fY ⊓ DY := ⟨mem_zpowers_iff.2 ⟨k, hdk.symm⟩, hd⟩
    rw [hDYdisj.eq_bot, mem_bot] at this
    rw [this]; rfl
  · intro x hx
    have hxY : x ∈ Y := hVY hx
    have hxc : (⟨x, hxY⟩ : Y) ∈ centralizer ({fY} : Set Y) :=
      mem_centralizer_singleton_iff.2 (Subtype.ext (hVf x hx))
    rw [hDYeq] at hxc
    have hx2 : (⟨x, hxY⟩ : Y) * ⟨x, hxY⟩ = 1 := Subtype.ext (hV2 x hx)
    exact ⟨_, involution_mem_of_sup hDYle hDYdisj (by rw [hfY5]; decide) hxc hx2, rfl⟩

theorem normalizing_data (hA5 : A5Lemma) {D V : Subgroup G} (hD : Nonempty (↥D ≃* A5))
    (hVD : V ≤ D) (hV4 : Nat.card V = 4) :
    ∃ r ∈ D, orderOf r = 3 ∧ r ∈ normalizer (V : Set G) ∧ ∃ x ∈ V, r * x * r⁻¹ ≠ x := by
  obtain ⟨e⟩ := hD
  have hcard : Nat.card (V.subgroupOf D) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVD).toEquiv, hV4]
  obtain ⟨rD, hrN, hr3, x, hxV, hx⟩ := hA5 e (V.subgroupOf D) hcard
  refine ⟨rD, rD.2, by rw [Subgroup.orderOf_coe]; exact hr3, ?_, ⟨x, hxV, ?_⟩⟩
  · rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have := (mem_normalizer_iff.1 hrN) ⟨y, hVD hy⟩
      exact this.1 hy
    · intro hy
      have hyD : y ∈ D := by
        have h1 : (rD : G)⁻¹ * ((rD : G) * y * (rD : G)⁻¹) * (rD : G) ∈ D :=
          mul_mem (mul_mem (D.inv_mem rD.2) (hVD hy)) rD.2
        simpa [mul_assoc] using h1
      exact ((mem_normalizer_iff.1 hrN) ⟨y, hyD⟩).2 hy
  · intro h1
    exact hx (Subtype.ext h1)

end CFSG.EvenSporadicStandard.RuStd.S2
