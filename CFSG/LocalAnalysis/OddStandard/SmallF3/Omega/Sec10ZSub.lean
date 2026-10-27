module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma conj_mul_inv_eq (a b c : G) :
    a * b * c = (a * (b * c * b⁻¹)) * b := by
  simp only [mul_assoc, inv_mul_cancel, mul_one]

private lemma le_normalizer_sup_of_conj_mem {X Y : Subgroup G}
    (h : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X ⊔ Y) :
    Y ≤ Subgroup.normalizer (X ⊔ Y : Subgroup G) := by
  rw [Subgroup.le_normalizer_iff]
  intro y hy z hz
  have hmap : (X ⊔ Y).map (MulAut.conj y).toMonoidHom ≤ X ⊔ Y := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      simpa using h y hy x hx
    · rintro _ ⟨w, hw, rfl⟩
      exact Subgroup.mem_sup_right (Y.mul_mem (Y.mul_mem hy hw) (Y.inv_mem hy))
  exact hmap (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem comap_oddCore_eq {P P' : Type*} [Group P] [Group P'] [Finite P] [Finite P']
    (φ : P →* P') (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) :
    (oddCore P').comap φ = oddCore P := by
  apply le_antisymm
  · have hn : ((oddCore P').comap φ).Normal := (oddCore_normal (G := P')).comap φ
    let g := φ.domRestrict ((oddCore P').comap φ)
    have hcard := Subgroup.card_ker_mul_card_range g
    have hrange : Nat.card g.range ∣ Nat.card (oddCore P') := by
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨v, rfl⟩
      exact v.2
    have hkerdvd : Nat.card g.ker ∣ Nat.card φ.ker := by
      have hsub : g.ker.map ((oddCore P').comap φ).subtype ≤ φ.ker := by
        rintro _ ⟨v, hv, rfl⟩
        exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hv)
      rw [← Subgroup.card_map_of_injective (K := g.ker)
        ((oddCore P').comap φ).subtype_injective]
      exact Subgroup.card_dvd_of_le hsub
    have hodd : Odd (Nat.card ((oddCore P').comap φ)) := by
      rw [← hcard]
      exact (hker.of_dvd_nat hkerdvd).mul
        ((odd_card_oddCore' P').of_dvd_nat hrange)
    exact le_sSup ⟨hn, hodd⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have hn : ((oddCore P).map φ).Normal := (oddCore_normal (G := P)).map φ hφ
    have hodd : Odd (Nat.card ((oddCore P).map φ)) :=
      (odd_card_oddCore' P).of_dvd_nat (Subgroup.card_map_dvd _ φ)
    exact le_sSup ⟨hn, hodd⟩

private noncomputable def oddCoreQuotientEquiv {P P' : Type*} [Group P] [Group P']
    [Finite P] [Finite P']
    (φ : P →* P') (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) :
    P ⧸ oddCore P ≃* P' ⧸ oddCore P' :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact (comap_oddCore_eq φ hφ hker).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (oddCore P')).comp φ)
      ((QuotientGroup.mk'_surjective _).comp hφ))

theorem sec10_isSubnormal_sup_odd {H C K K1 N : Subgroup G} (hN : N ≤ H)
    (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hC : C ≤ H) (hdec : ∀ h ∈ H, ∃ o ∈ N, ∃ c ∈ C, h = o * c)
    (hK : K ≤ C) (hKn : ∀ c ∈ C, ∀ x ∈ K, c * x * c⁻¹ ∈ K)
    (hK1 : K1 ≤ K) (hK1n : ∀ k ∈ K, ∀ x ∈ K1, k * x * k⁻¹ ∈ K1) :
    ((K1 ⊔ N).subgroupOf H).IsSubnormal := by
  have hBleH : K ⊔ N ≤ H := sup_le (hK.trans hC) hN
  have hAleB : K1 ⊔ N ≤ K ⊔ N := sup_le (hK1.trans le_sup_left) le_sup_right
  have hHnN : H ≤ Subgroup.normalizer N := Subgroup.le_normalizer_iff.mpr hNn
  have hCnK : C ≤ Subgroup.normalizer K := Subgroup.le_normalizer_iff.mpr hKn
  have hCnN : C ≤ Subgroup.normalizer N := hC.trans hHnN
  have hCnB : C ≤ Subgroup.normalizer (K ⊔ N : Subgroup G) :=
    (le_inf hCnK hCnN).trans (Subgroup.inf_normalizer_le_normalizer_sup K N)
  have hNnB : N ≤ Subgroup.normalizer (K ⊔ N : Subgroup G) :=
    (le_sup_right : N ≤ K ⊔ N).trans (Subgroup.le_normalizer (H := K ⊔ N))
  have hHnB : H ≤ Subgroup.normalizer (K ⊔ N : Subgroup G) := by
    intro h hh
    obtain ⟨o, ho, c, hc, rfl⟩ := hdec h hh
    exact mul_mem (hNnB ho) (hCnB hc)
  have hBnormal : ((K ⊔ N).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBleH).mpr hHnB
  have hKnK1 : K ≤ Subgroup.normalizer K1 := Subgroup.le_normalizer_iff.mpr hK1n
  have hKnN : K ≤ Subgroup.normalizer N :=
    Subgroup.le_normalizer_iff.mpr (fun k hk n hn => hNn k (hC (hK hk)) n hn)
  have hKnA : K ≤ Subgroup.normalizer (K1 ⊔ N : Subgroup G) :=
    (le_inf hKnK1 hKnN).trans (Subgroup.inf_normalizer_le_normalizer_sup K1 N)
  have hNnA : N ≤ Subgroup.normalizer (K1 ⊔ N : Subgroup G) :=
    le_normalizer_sup_of_conj_mem (X := K1) (Y := N) (fun o ho x hx => by
      have hxN : x * o⁻¹ * x⁻¹ ∈ N := hNn x (hC (hK (hK1 hx))) o⁻¹ (N.inv_mem ho)
      have hprod : (o * (x * o⁻¹ * x⁻¹)) * x ∈ K1 ⊔ N :=
        mul_mem (Subgroup.mem_sup_right (N.mul_mem ho hxN)) (Subgroup.mem_sup_left hx)
      rw [conj_mul_inv_eq o x o⁻¹]
      exact hprod)
  have hBnA : K ⊔ N ≤ Subgroup.normalizer (K1 ⊔ N : Subgroup G) := sup_le hKnA hNnA
  have hAnormal : (((K1 ⊔ N).subgroupOf H).subgroupOf ((K ⊔ N).subgroupOf H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.subgroupOf_mono H hAleB)]
    rw [Subgroup.le_normalizer_iff]
    intro x hx a ha
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.le_normalizer_iff.mp hBnA (x : G) (Subgroup.mem_subgroupOf.mp hx)
        (a : G) (Subgroup.mem_subgroupOf.mp ha))
  exact Subgroup.IsSubnormal.step ((K1 ⊔ N).subgroupOf H) ((K ⊔ N).subgroupOf H)
    (Subgroup.subgroupOf_mono H hAleB) hBnormal.isSubnormal hAnormal

theorem isSL23Mod_sup_odd [Finite G] {K1 N : Subgroup G} (hK1 : IsSL23Mod ↥K1)
    (hN : ∀ k ∈ K1, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    IsSL23Mod ↥(K1 ⊔ N) := by
  have hKN : K1 ≤ Subgroup.normalizer N := Subgroup.le_normalizer_iff.mpr hN
  letI : (N.subgroupOf (K1 ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hKN
  have hN1odd : Odd (Nat.card (N.subgroupOf K1)) :=
    hodd.of_dvd_nat (Subgroup.card_comap_dvd_of_injective N K1.subtype K1.subtype_injective)
  have hNtodd : Odd (Nat.card (N.subgroupOf (K1 ⊔ N))) :=
    hodd.of_dvd_nat (Subgroup.card_comap_dvd_of_injective N (K1 ⊔ N).subtype
      (K1 ⊔ N).subtype_injective)
  let φ1 : ↥K1 →* (↥(K1 ⊔ N)) ⧸ (N.subgroupOf (K1 ⊔ N)) :=
    (QuotientGroup.mk' (N.subgroupOf (K1 ⊔ N))).comp
      (Subgroup.inclusion (le_sup_left : K1 ≤ K1 ⊔ N))
  have hφ1surj : Function.Surjective φ1 := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (K1 ⊔ N)) y
    have hxmem : (x : G) ∈ (↑(K1 ⊔ N) : Set G) := x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K1 N hKN] at hxmem
    rw [Set.mem_mul] at hxmem
    obtain ⟨k, hk, n, hn, hkn⟩ := hxmem
    refine ⟨⟨k, hk⟩, ?_⟩
    have hxeq : x = Subgroup.inclusion (le_sup_left : K1 ≤ K1 ⊔ N) ⟨k, hk⟩ *
        Subgroup.inclusion (le_sup_right : N ≤ K1 ⊔ N) ⟨n, hn⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      exact hkn.symm
    show φ1 ⟨k, hk⟩ = QuotientGroup.mk' (N.subgroupOf (K1 ⊔ N)) x
    rw [hxeq, map_mul]
    have hnker : QuotientGroup.mk' (N.subgroupOf (K1 ⊔ N))
        (Subgroup.inclusion (le_sup_right : N ≤ K1 ⊔ N) ⟨n, hn⟩) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact Subgroup.mem_subgroupOf.mpr hn
    rw [hnker, mul_one]
    rfl
  have hφ1ker : φ1.ker = N.subgroupOf K1 := by
    show ((QuotientGroup.mk' (N.subgroupOf (K1 ⊔ N))).comp
      (Subgroup.inclusion (le_sup_left : K1 ≤ K1 ⊔ N))).ker = N.subgroupOf K1
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    simp only [Subgroup.comap_inclusion_subgroupOf]
  have hφ1odd : Odd (Nat.card φ1.ker) := by
    rw [hφ1ker]
    exact hN1odd
  have hqodd : Odd (Nat.card (QuotientGroup.mk' (N.subgroupOf (K1 ⊔ N))).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hNtodd
  obtain ⟨e1⟩ := hK1
  exact ⟨(oddCoreQuotientEquiv (QuotientGroup.mk' (N.subgroupOf (K1 ⊔ N)))
      (QuotientGroup.mk'_surjective _) hqodd).trans
    ((oddCoreQuotientEquiv φ1 hφ1surj hφ1odd).symm.trans e1)⟩

end CFSG.OddStandard.SmallF3.Omega
