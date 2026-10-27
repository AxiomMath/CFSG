module

public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE Polynomial

theorem natCard_fixSubfield_eq {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (E : Subfield L) [Finite E]
    (hKE : Set.range (algebraMap K L) ⊆ E) (σE : E ≃+* E) (hσ : ∀ e : E, (σE e : L) = Fr e) :
    Nat.card (fixSubfield σE) = Nat.card K := by
  exact CFSG.RankThree.PartOne.KE.natCard_fixSubfield_eq_of_frobenius Fr hFr E hKE σE hσ

section Certs


theorem fixedFieldImage_index_dvd_card_units {τ : Tag} {M : Type} [Field M] [Finite M]
    (σ : M ≃+* M) :
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣
      (Nat.card (fixSubfield σ)ˣ) ^ τ.rank := by
  simpa only [Nat.card_units] using
    CFSG.LieType.Chevalley.fixedFieldImage_index_dvd_card_units (τ := τ) σ

theorem fixedFieldImage_index_dvd_gcd_E6 {M : Type} [Field M] [Finite M] (σ : M ≃+* M) :
    ((fixedFieldImage .E6 σ).subgroupOf (entrywiseFixedGroup .E6 σ)).index ∣
      (Nat.card (fixSubfield σ) - 1).gcd 3 := by
  have h3 : ((fixedFieldImage .E6 σ).subgroupOf (entrywiseFixedGroup .E6 σ)).index ∣ 3 := by
    have h := fixedFieldImage_index_dvd (τ := .E6) σ
    rwa [det_cartan_E6] at h
  have hn := fixedFieldImage_index_dvd_card_units (τ := .E6) σ
  rw [Nat.card_units] at hn
  have hrank : Tag.E6.rank = 6 := by decide
  rw [hrank] at hn
  generalize ((fixedFieldImage .E6 σ).subgroupOf (entrywiseFixedGroup .E6 σ)).index = d at h3 hn
  generalize Nat.card (fixSubfield σ) - 1 = n at hn ⊢
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with rfl | rfl
  · exact one_dvd _
  · have : 3 ∣ n := Nat.prime_three.dvd_of_dvd_pow hn
    rw [Nat.gcd_eq_right this]

theorem relIndex_dvd_E6_of_not_three_dvd (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K - 1) :
    ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card K) → ∀ (X : Subgroup (ModGL .E6 L)) [Finite X],
        X ≤ adjointGroup .E6 L → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ((adjointGroup .E6 K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ 1 := by
  intro L _ _ _ Fr hFr X _ hXC hXF
  classical
  have : Fintype X := Fintype.ofFinite X
  have hdesc : ∀ x : X, ∃ S : Finset L, ∀ E : Subfield L, (S : Set L) ⊆ E →
      ∃ y ∈ adjointGroup .E6 E, baseChangeGL E.subtype y = (x : ModGL .E6 L) :=
    fun x => CFSG.LieType.Chevalley.exists_finset_descent (hXC x.2)
  choose Sx hSx using hdesc
  obtain ⟨E, hEf, hSE, hKE⟩ :=
    exists_finite_subfield_of_finset (K := K) (L := L) (Finset.univ.biUnion Sx)
  have : Finite E := hEf
  have hSE' : ∀ x : X, (Sx x : Set L) ⊆ E := fun x a ha =>
    hSE (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Finset.mem_coe.1 ha⟩))
  obtain ⟨σE, hσE, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := .E6) Fr hFr E hKE
  have hJn : ((fixedFieldImage .E6 σE).subgroupOf (entrywiseFixedGroup .E6 σE)).Normal :=
    fixedFieldImage_normal
  have hidx : ((fixedFieldImage .E6 σE).subgroupOf (entrywiseFixedGroup .E6 σE)).index ∣ 1 := by
    have h := fixedFieldImage_index_dvd_gcd_E6 σE
    rw [natCard_fixSubfield_eq Fr hFr E hKE σE hσE] at h
    have hg : (Nat.card K - 1).gcd 3 = 1 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    rwa [hg] at h
  have hιE : Function.Injective (baseChangeGL (τ := .E6) E.subtype) :=
    baseChangeGL_injective E.subtype
  set A : Subgroup (ModGL .E6 E) :=
    X.comap (baseChangeGL E.subtype) ⊓ adjointGroup .E6 E with hA
  have hXA : X = A.map (baseChangeGL E.subtype) := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨y, hy, hyx⟩ := hSx ⟨x, hx⟩ E (hSE' ⟨x, hx⟩)
      refine ⟨y, ⟨?_, hy⟩, hyx⟩
      have h1 : baseChangeGL E.subtype y = x := hyx
      show baseChangeGL E.subtype y ∈ X
      rw [h1]
      exact hx
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
  have hAΓ : A ≤ entrywiseFixedGroup .E6 σE := fun y hy =>
    hfix y hy.2 (hXF _ hy.1)
  rw [← hJ, hXA, Subgroup.relIndex_map_map_of_injective _ _ hιE]
  have h1 : ((fixedFieldImage .E6 σE).subgroupOf (entrywiseFixedGroup .E6 σE)).relIndex
      (A.subgroupOf (entrywiseFixedGroup .E6 σE)) =
      (fixedFieldImage .E6 σE).relIndex A := Subgroup.relIndex_subgroupOf hAΓ
  rw [← h1]
  exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hidx

end Certs

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
