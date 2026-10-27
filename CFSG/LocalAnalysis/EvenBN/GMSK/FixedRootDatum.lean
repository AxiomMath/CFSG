module

public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
public import CFSG.LocalAnalysis.EvenBN.GMSK.Statement

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

structure FixedRootDatum (D : Type) [Group D] (n : ℕ) (K : Type) [Field K] [Fintype K]
    (α : MulAut D) (S : Subgroup D) : Prop where
  two_le : 2 ≤ n
  card_eq : Fintype.card K = 2 ^ n
  orderOf_eq : orderOf α = 2
  le_fixed : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D)
  normal : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal
  nonempty_mulEquiv : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)
  rankOne : FixedRootRankOne α S

theorem FixedRootSelector.survivors_of_datum {P : (D : Type) → [Group D] → Prop}
    (h : FixedRootSelector P) {D : Type} [Group D] [Finite D] (hD : IsSimpleGroup D) (hP : P D)
    {n : ℕ} {K : Type} [Field K] [Fintype K] {α : MulAut D} {S : Subgroup D}
    (d : FixedRootDatum D n K α S) : FixedRootSurvivors D n :=
  h D hD hP n d.two_le K d.card_eq α d.orderOf_eq S d.le_fixed d.normal d.nonempty_mulEquiv
    d.rankOne

section Normal

variable {G : Type} [Group G] {D : Subgroup G} [D.Normal] {t : G}

theorem mem_eqLocus_conjNormal_iff {x : D} :
    x ∈ (MulAut.conjNormal t : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D) ↔
      t * (x : G) * t⁻¹ = x := by
  change MulAut.conjNormal t x = x ↔ _
  rw [← Subtype.coe_inj, MulAut.conjNormal_apply]

theorem mem_centralizer_of_mem_eqLocus {x : D}
    (hx : x ∈ (MulAut.conjNormal t : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D)) :
    (x : G) ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  have h := mem_eqLocus_conjNormal_iff.1 hx
  calc (x : G) * t = t * x * t⁻¹ * t := by rw [h]
    _ = t * x := by group

theorem orderOf_conjNormal (ht : orderOf t = 2) (hnt : ∃ d ∈ D, t⁻¹ * d * t ≠ d) :
    orderOf (MulAut.conjNormal t : MulAut D) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ht2]
  refine orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) fun h1 => ?_
  obtain ⟨d, hd, hdt⟩ := hnt
  have h := congrArg (fun α : MulAut D => ((α ⟨d, hd⟩ : D) : G)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  apply hdt
  rw [htinv]
  calc t * d * t = t * d * t⁻¹ := by rw [htinv]
    _ = d := h

theorem conjNormal_mem_range_of_mem (htD : t ∈ D) :
    (MulAut.conjNormal t : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range := by
  refine ⟨⟨t, htD⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [MulAut.conjNormal_apply, MulAut.conj_apply]
  rfl

theorem fixedRootDatum_of_normal [Finite G] {A : Subgroup G} (hAD : A ≤ D) (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set G)) (hCt : centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hnt : ∃ d ∈ D, t⁻¹ * d * t ≠ d)
    (hrank : ∀ P : Subgroup G, P ≤ centralizer (A : Set G) → IsPGroup 2 P → Nat.card P ≤ 2)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    FixedRootDatum D n K (MulAut.conjNormal t) (A.subgroupOf D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α : MulAut D := MulAut.conjNormal t with hα
  set F := α.toMonoidHom.eqLocus (MonoidHom.id D) with hF
  have hle : A.subgroupOf D ≤ F := fun s hs => by
    rw [hF, mem_eqLocus_conjNormal_iff]
    have hc := mem_centralizer_iff.1 htA s (mem_subgroupOf.1 hs)
    calc t * (s : G) * t⁻¹ = s * t * t⁻¹ := by rw [hc]
      _ = s := by group
  refine ⟨hn, hK, orderOf_conjNormal ht hnt, hle, ⟨fun x hx g => ?_⟩,
    ⟨(subgroupOfEquivOfLe hAD).trans φ⟩, fun P hP hP2 => ?_⟩
  ·
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hgN := hCt (mem_centralizer_of_mem_eqLocus g.2)
    exact (mem_normalizer_iff.1 hgN _).1 hx
  ·
    set P' := P.map D.subtype with hP'
    have hP'A : P' ≤ centralizer (A : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [mem_centralizer_iff]
      intro a ha
      have h := mem_centralizer_iff.1 (hP hp).2 ⟨a, hAD ha⟩ (mem_subgroupOf.2 ha)
      exact congrArg Subtype.val h
    have hP't : P' ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      exact mem_centralizer_of_mem_eqLocus (hP hp).1
    have hz2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hzN : P' ≤ normalizer (zpowers t : Set G) := by
      refine le_trans ?_ (centralizer_le_normalizer _)
      rw [le_centralizer_iff, zpowers_le, mem_centralizer_iff]
      intro p hp
      exact mem_centralizer_singleton_iff.1 (hP't hp)
    have hQ := IsPGroup.to_sup_of_normal_right' (hP2.map D.subtype) hz2 hzN
    have hQA : P' ⊔ zpowers t ≤ centralizer (A : Set G) := sup_le hP'A (zpowers_le.2 htA)
    have hQt : zpowers t = P' ⊔ zpowers t :=
      eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, ht]; exact hrank _ hQA hQ)
    have hP'le : P' ≤ zpowers t := hQt ▸ le_sup_left
    have hcard : Nat.card P = Nat.card P' := (card_map_of_injective D.subtype_injective).symm
    refine ⟨?_, fun hout => ?_⟩
    · rw [hcard]
      calc Nat.card P' ≤ Nat.card (zpowers t) := card_le_of_le hP'le
        _ = 2 := by rw [Nat.card_zpowers, ht]
    · by_contra hne
      obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      have hpt := hP'le ⟨p, hp, rfl⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hpt
      change t ^ k = (p : G) at hk
      have hpz : (p : G) = 1 ∨ (p : G) = t := by
        rw [← hk, ← zpow_mod_orderOf, ht]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          rw [Nat.cast_ofNat, h, zpow_zero]
        · right
          rw [Nat.cast_ofNat, h, zpow_one]
      rcases hpz with h1 | htp
      · exact hp1 (Subtype.ext (Subtype.ext h1))
      · exact hout (conjNormal_mem_range_of_mem (htp ▸ p.2))

end Normal

theorem exists_fixedRootDatum_of_simple {G : Type} [Group G] [Finite G]
    (hG : CFSG.SectionRank.IsKGroupCat G)
    {n : ℕ} {A : Subgroup G} (hA : StdLinearData G A n)
    (hrank : ∀ P : Subgroup G, P ≤ centralizer (A : Set G) → IsPGroup 2 P → Nat.card P ≤ 2)
    {t : G} (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hCt : centralizer ({t} : Set G) ≤ normalizer (A : Set G)) {D : Subgroup G} [D.Normal]
    (hAD : A ≤ D) (hD : IsSimpleGroup D) (hnt : ∃ d ∈ D, t⁻¹ * d * t ≠ d) :
    Catalog D ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K) (α : MulAut D) (S : Subgroup D),
      FixedRootDatum D n K α S := by
  obtain ⟨hn, -, -, K, _, _, hK, ⟨φ⟩⟩ := hA
  exact ⟨CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hG D (MonoidHom.id D)
      Function.surjective_id,
    K, inferInstance, inferInstance, _, _,
    fixedRootDatum_of_normal hAD ht htA hCt hnt hrank hn hK φ⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
