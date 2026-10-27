
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44
public import CFSG.LieType.Multipliers.L34Data

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

abbrev Jhat (J : Subgroup G) : Type := ↥J ⧸ pPrimeCore 2 ↥J

abbrev jq (J : Subgroup G) : ↥J →* Jhat J := QuotientGroup.mk' (pPrimeCore 2 ↥J)

instance (J : Subgroup G) : (pPrimeCore 2 ↥J).Normal := pPrimeCore_normal

theorem commutator_jhat {J : Subgroup G} (hJ : ⁅J, J⁆ = J) : commutator (Jhat J) = ⊤ := by
  have : Group.IsPerfect ↥J := (Subgroup.isPerfect_iff (H := J)).2 hJ
  exact Group.IsPerfect.commutator_eq_top

theorem mem_oddIn_iff {J : Subgroup G} {g : G} (hg : g ∈ J) :
    g ∈ oddIn J ↔ jq J ⟨g, hg⟩ = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨o, ho, hoe⟩
    have : o = ⟨g, hg⟩ := Subtype.ext hoe
    rwa [← this]
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem mem_zStarIn_iff {J : Subgroup G} {g : G} (hg : g ∈ J) :
    g ∈ zStarIn J ↔ jq J ⟨g, hg⟩ ∈ center (Jhat J) := by
  constructor
  · rintro ⟨z, hz, hze⟩
    have : z = ⟨g, hg⟩ := Subtype.ext hze
    rw [← this]
    rwa [GrS4.fusionZStar_eq_comap_pPrimeCore] at hz
  · intro h
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [GrS4.fusionZStar_eq_comap_pPrimeCore]
    exact h

theorem eq_one_of_jq_eq_one [Finite G] {J P : Subgroup G} (hPJ : P ≤ J) (hP : IsPGroup 2 P)
    {g : G} (hg : g ∈ P) (h : jq J ⟨g, hPJ hg⟩ = 1) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : (⟨g, hPJ hg⟩ : J) ∈ pPrimeCore 2 ↥J := by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have h1 : orderOf (⟨⟨g, hPJ hg⟩, ho⟩ : pPrimeCore 2 ↥J) ∣ Nat.card (pPrimeCore 2 ↥J) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨⟨g, hPJ hg⟩, ho⟩ : pPrimeCore 2 ↥J) ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥J)) :=
    Nat.Coprime.pow_left _ pPrimeCore_coprime_card
  have h3 : orderOf (⟨⟨g, hPJ hg⟩, ho⟩ : pPrimeCore 2 ↥J) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  have := congrArg (fun x : pPrimeCore 2 ↥J => ((x : J) : G)) (orderOf_eq_one_iff.mp h3)
  simpa using this

theorem eq_of_jq_eq [Finite G] {J P : Subgroup G} (hPJ : P ≤ J) (hP : IsPGroup 2 P) {g h : G}
    (hg : g ∈ P) (hh : h ∈ P) (e : jq J ⟨g, hPJ hg⟩ = jq J ⟨h, hPJ hh⟩) : g = h := by
  have hgh : g * h⁻¹ ∈ P := P.mul_mem hg (P.inv_mem hh)
  have h1 : jq J ⟨g * h⁻¹, hPJ hgh⟩ = 1 := by
    have : (⟨g * h⁻¹, hPJ hgh⟩ : J) = ⟨g, hPJ hg⟩ * (⟨h, hPJ hh⟩)⁻¹ := rfl
    rw [this, map_mul, map_inv, e, mul_inv_cancel]
  have := eq_one_of_jq_eq_one hPJ hP hgh h1
  rwa [mul_inv_eq_one] at this

theorem exists_jq [Finite G] {J : Subgroup G}
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) :
    ∃ q : Jhat J →* Equiv.Perm (Fin 42), (∀ e, q e ∈ S) ∧ (∀ s ∈ S, ∃ e, q e = s) ∧
      q.ker = center (Jhat J) ∧ ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1 := by
  obtain ⟨π, hπ, hker, h3⟩ := GrS5.exists_quotient_psl34 hL
  have hk : (S.subtype.comp π).ker = π.ker := by
    ext e
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  refine ⟨S.subtype.comp π, fun e => (π e).2, fun s hs => ?_, hk.trans hker, ?_⟩
  · obtain ⟨e, he⟩ := hπ ⟨s, hs⟩
    exact ⟨e, by simp [he]⟩
  · rw [hk]
    exact h3

theorem conj_jq {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {g : Equiv.Perm (Fin 42)} (hg : g ∈ R) :
    (∀ e, ((MulAut.conj g).toMonoidHom.comp q) e ∈ S) ∧
      (∀ s ∈ S, ∃ e, ((MulAut.conj g).toMonoidHom.comp q) e = s) ∧
      ((MulAut.conj g).toMonoidHom.comp q).ker = q.ker := by
  refine ⟨fun e => conj_mem_S hg (hqS e), fun s hs => ?_, ?_⟩
  · have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S := conj_mem_S (R.inv_mem hg) hs
    obtain ⟨e, he⟩ := hqsurj _ hs'
    refine ⟨e, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, he]
    group
  · ext e
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro h
      have : q e = g⁻¹ * (g * q e * g⁻¹) * g := by group
      rw [this, h]
      group
    · intro h
      rw [h]
      group

theorem exists_mem_of_mem_center [Finite G] {J P : Subgroup G} (hP : IsSylowTwoIn P J)
    {ζ : Jhat J} (hζ : ζ ∈ center (Jhat J)) : ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = ζ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPJ, T, hT⟩ := hP
  set T' : Sylow 2 (Jhat J) := T.mapSurjective (QuotientGroup.mk'_surjective _)
  have hle : center (Jhat J) ≤ (T' : Subgroup (Jhat J)) :=
    (GrS4.isPGroup_center_quotient ↥J).le_sylow_of_normal T'
  have hmem := hle hζ
  rw [Sylow.coe_mapSurjective] at hmem
  obtain ⟨x, hx, rfl⟩ := hmem
  rw [hT] at hx
  exact ⟨x, hx, x.2, rfl⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
