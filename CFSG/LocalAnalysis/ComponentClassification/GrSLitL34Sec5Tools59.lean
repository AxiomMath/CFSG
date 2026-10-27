module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Core
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReduction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoIn_of_le_of_le {S H K : Subgroup G} (hS : IsSylowTwoIn S K) (hSH : S ≤ H)
    (hHK : H ≤ K) : IsSylowTwoIn S H := by
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hS
  refine ⟨hSH, ⟨S.subgroupOf H, hS2.of_equiv (subgroupOfEquivOfLe hSH).symm, fun {Q} hQ hSQ => ?_⟩,
    rfl⟩
  have hQ2 : IsPGroup 2 ↥(Q.map H.subtype) := hQ.map H.subtype
  have hSQ' : S ≤ Q.map H.subtype := fun x hx => ⟨⟨x, hSH hx⟩, hSQ hx, rfl⟩
  have heq := IsSylowTwoIn.eq_of_le hS hSQ' ((map_subtype_le Q).trans hHK) hQ2
  apply map_injective H.subtype_injective
  rw [heq, subgroupOf_map_subtype, inf_eq_left.mpr hSH]

omit [Finite G] in
theorem mem_of_mem_center_of_le {L S T : Subgroup G} {t : G}
    (hSyl : IsSylowTwoIn S (normalizer (L : Set G))) (htS : t ∈ S) (hST : S ≤ T)
    (hT2 : IsPGroup 2 T) (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {z : G}
    (hzT : z ∈ T) (hz : ∀ y ∈ T, z * y = y * z) : z ∈ S := by
  have hzN : z ∈ normalizer (L : Set G) :=
    hCN (mem_centralizer_singleton_iff.mpr (hz t (hST htS)))
  have hle : S ⊔ zpowers z ≤ T := sup_le hST (zpowers_le.mpr hzT)
  have heq := IsSylowTwoIn.eq_of_le hSyl le_sup_left (sup_le hSyl.1 (zpowers_le.mpr hzN))
    (hT2.to_le hle)
  exact heq ▸ mem_sup_right (mem_zpowers z)

theorem card_eq_two_pow_twoExp {P H : Subgroup G} (hP : IsSylowTwoIn P H) :
    Nat.card P = 2 ^ twoExp H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPH, P₀, hP₀⟩ := hP
  have h := P₀.card_eq_multiplicity
  rw [hP₀, Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv] at h
  exact h

theorem two_pow_le_card_of_isSylowTwoIn {P K : Subgroup G} (hP : IsSylowTwoIn P K) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card K) : 2 ^ k ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK, P₀, hP₀⟩ := hP
  have h1 : 2 ^ k ∣ Nat.card (P₀ : Subgroup K) := P₀.pow_dvd_card_of_pow_dvd_card hk
  rw [hP₀, Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv] at h1
  exact Nat.le_of_dvd Nat.card_pos h1

theorem card_le_two_pow_twoExp {R H : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R) :
    Nat.card R ≤ 2 ^ twoExp H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' : IsPGroup 2 ↥(R.subgroupOf H) := hR.of_equiv (subgroupOfEquivOfLe hRH).symm
  obtain ⟨P₀, hP₀⟩ := hR'.exists_le_sylow
  have h1 := P₀.card_eq_multiplicity
  calc Nat.card R = Nat.card ↥(R.subgroupOf H) :=
        Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv.symm
    _ ≤ Nat.card (P₀ : Subgroup H) := card_le_of_le hP₀
    _ = 2 ^ twoExp H := h1

theorem le_twoExp_of_dvd {H : Subgroup G} {k : ℕ} (h : 2 ^ k ∣ Nat.card H) : k ≤ twoExp H :=
  (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h

theorem not_mem_zStarIn_of_lieModel_psl_two {K : Subgroup G} {p f : ℕ}
    (hL : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f)
    (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) {u : G} (hu : orderOf u = 2) : u ∉ zStarIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := isSimpleGroup_of_lieModel_psl_two hL
  have hZ : center (K ⧸ pPrimeCore 2 K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ pPrimeCore 2 K)) with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hq
      have : Subsingleton ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact hab (Subsingleton.elim _ _)
  rintro ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap, hZ, mem_bot,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
  have hu' : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hdvd : orderOf (⟨z, hz⟩ : pPrimeCore 2 ↥K) ∣ Nat.card (pPrimeCore 2 ↥K) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hu'] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem mem_zStarIn_of_sup_oddIn {K P : Subgroup G} (hKP : K ≤ P) (hsup : K ⊔ oddIn P = P)
    {u : G} (hu : u ∈ zStarIn K) : u ∈ zStarIn P := by
  obtain ⟨-, e, he⟩ := restriction_quotient_mulEquiv hKP hsup
  obtain ⟨z, hz, rfl⟩ := hu
  refine ⟨⟨z, hKP z.2⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap] at hz ⊢
  have h1 : e (QuotientGroup.mk' (pPrimeCore 2 ↥K) z) ∈ center (↥P ⧸ pPrimeCore 2 ↥P) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hz y')]
  rwa [QuotientGroup.mk'_apply, he z (hKP z.2)] at h1

end CFSG.ComponentClassification.GrSLit.GrS5
