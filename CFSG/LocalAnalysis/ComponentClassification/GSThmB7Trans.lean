module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Data
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Sp4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Prop
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB71Step2a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

section Lift

variable {G : Type} [Group G] [Finite G]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 G)

omit [Finite G] in
theorem isPGroup_closure_pair {u v : G} (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) :
    IsPGroup 2 (closure ({u, v} : Set G)) := by
  intro w
  refine ⟨1, Subtype.ext ?_⟩
  have key : (w : G) * w = 1 := by
    rcases Six.mem_closure_pair_cases hu hv huv.symm w.2 with h | h | h | h <;> rw [h]
    · exact one_mul 1
    · exact hu
    · exact hv
    · rw [show u * v * (u * v) = u * (v * u) * v by group, ← huv,
        show u * (u * v) * v = (u * u) * (v * v) by group, hu, hv, one_mul]
  simpa [pow_two] using key

omit [Finite G] in
theorem isPGroup_closure_pair_sup {u v r : G} (hu : u * u = 1) (hv : v * v = 1)
    (huv : u * v = v * u) (hr : r * r = 1) (hru : r⁻¹ * u * r = v) :
    IsPGroup 2 ↥(closure ({u, v} : Set G) ⊔ zpowers r) := by
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hrv : r⁻¹ * v * r = u := by
    rw [← hru, hrinv, show r * (r * u * r) * r = (r * r) * u * (r * r) by group, hr, one_mul,
      mul_one]
  have hN : zpowers r ≤ normalizer (closure ({u, v} : Set G) : Set G) := by
    rw [zpowers_le]
    have key : ∀ w ∈ closure ({u, v} : Set G), r * w * r⁻¹ ∈ closure ({u, v} : Set G) := by
      intro w hw
      induction hw using closure_induction with
      | mem w hw =>
        rcases hw with rfl | rfl
        · rw [← hrinv, inv_inv, hru]; exact subset_closure (by simp)
        · rw [← hrinv, inv_inv, hrv]; exact subset_closure (by simp)
      | one => simp
      | mul w₁ w₂ _ _ h₁ h₂ =>
        rw [show r * (w₁ * w₂) * r⁻¹ = (r * w₁ * r⁻¹) * (r * w₂ * r⁻¹) by group]
        exact mul_mem h₁ h₂
      | inv w _ h =>
        rw [show r * w⁻¹ * r⁻¹ = (r * w * r⁻¹)⁻¹ by group]
        exact inv_mem h
    rw [mem_normalizer_iff]
    intro w
    refine ⟨key w, fun hw => ?_⟩
    have := key _ hw
    rwa [show r * (r * w * r⁻¹) * r⁻¹ = (r * r) * w * (r * r)⁻¹ by group, hr, one_mul, inv_one,
      mul_one] at this
  have h2 : IsPGroup 2 (zpowers r) := by
    intro w
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp w.2
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hk]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hr, one_zpow]
  exact (isPGroup_closure_pair hu hv huv).to_sup_of_normal_left' h2 hN

theorem lift_swap {t z : G} (ht : t * t = 1) (hz : z * z = 1) (htz : t * z = z * t)
    {rb : G ⧸ pPrimeCore 2 G} (hr : rb * rb = 1) (hrt : rb⁻¹ * π t * rb = π z) :
    ∃ r : G, r * r = 1 ∧ r⁻¹ * t * r = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Eb : Subgroup (G ⧸ pPrimeCore 2 G) := closure ({π t, π z} : Set _) ⊔ zpowers rb with hEb
  have hEb2 : IsPGroup 2 Eb := isPGroup_closure_pair_sup (by rw [← map_mul, ht, map_one])
    (by rw [← map_mul, hz, map_one]) (by rw [← map_mul, ← map_mul, htz]) hr hrt
  set Et : Subgroup G := Eb.comap π with hEt
  have hE0 : closure ({t, z} : Set G) ≤ Et := by
    rw [closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_left (subset_closure (by simp))
  have hE02 : IsPGroup 2 ((closure ({t, z} : Set G)).subgroupOf Et) :=
    (isPGroup_closure_pair ht hz htz).comap_subtype
  obtain ⟨P, hP⟩ := hE02.exists_le_sylow
  let π' : ↥Et →* ↥(Et.map π) := (QuotientGroup.mk' (pPrimeCore 2 G)).subgroupMap Et
  have hπ' : Function.Surjective π' := MonoidHom.subgroupMap_surjective _ Et
  have hEm2 : IsPGroup 2 ↥(Et.map π) := hEb2.to_le (map_comap_le _ _)
  have htop : ((P.mapSurjective hπ' : Sylow 2 ↥(Et.map π)) : Subgroup ↥(Et.map π)) = ⊤ :=
    ((P.mapSurjective hπ').is_maximal' (hEm2.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  obtain ⟨r₀, hr₀⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 G) rb
  have hrbE : rb ∈ Eb := mem_sup_right (mem_zpowers rb)
  have hrbm : rb ∈ Et.map π := ⟨r₀, show π r₀ ∈ Eb by rw [hr₀]; exact hrbE, hr₀⟩
  obtain ⟨⟨r, hrE⟩, hrP, hrr⟩ := mem_map.mp (htop ▸ mem_top (⟨rb, hrbm⟩ : ↥(Et.map π)))
  have hrr' : π r = rb := congrArg Subtype.val hrr
  set E : Subgroup G := (P : Subgroup ↥Et).map Et.subtype with hE
  have hE2 : IsPGroup 2 E := P.isPGroup'.map _
  have hrE' : r ∈ E := ⟨⟨r, hrE⟩, hrP, rfl⟩
  have htE : t ∈ E := ⟨⟨t, hE0 (subset_closure (by simp))⟩,
    hP (mem_subgroupOf.mpr (subset_closure (by simp))), rfl⟩
  have hzE : z ∈ E := ⟨⟨z, hE0 (subset_closure (by simp))⟩,
    hP (mem_subgroupOf.mpr (subset_closure (by simp))), rfl⟩
  have hinj := OddQuot.injOn_of_isPGroup hE2
  refine ⟨r, hinj (mul_mem hrE' hrE') (one_mem _) ?_, hinj (mul_mem (mul_mem (inv_mem hrE')
    htE) hrE') hzE ?_⟩
  · rw [map_mul, hrr', hr, map_one]
  · rw [map_mul, map_mul, map_inv, hrr', hrt]

theorem isPComponent_centralizer_map {t : G} (ht : t * t = 1) {M : Subgroup G}
    (hMt : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G)))) :
    M.map π ≤ centralizer ({π t} : Set (G ⧸ pPrimeCore 2 G)) ∧
      IsPComponent 2 ((M.map π).subgroupOf (centralizer ({π t} : Set (G ⧸ pPrimeCore 2 G)))) := by
  rw [OddQuot.centralizer_singleton_map_eq ht]
  exact ⟨map_mono hMt, OddQuot.isPComponent_map π OddQuot.not_two_dvd_card_ker hMt hM⟩

end Lift

end Seven

end CFSG.ComponentClassification.GSThmB
