module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma45
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvSylow
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqElem
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5OTwoFam510

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mul_self_of_odd {D : Subgroup G} (hD : Odd (Nat.card D)) {y : G}
    (hy : y ∈ D) (hy2 : y * y = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
  have h2 : orderOf y ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hy
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd (Odd.of_dvd_nat hD h2) (by decide)

theorem le_of_twoExp_eq_two
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) (h3 : twoExp (zStarIn L) = 2) :
    S ⊓ coreActionKernel L ⊓ L ≠ ⊥ ∧ S ⊓ coreActionKernel L ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, -, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  obtain ⟨h0, -⟩ := twoExp_le_of_setting hS hU hheld hSol hGW h58 h59 hset
  have hZ : S ⊓ coreActionKernel L ⊓ L ≠ ⊥ := fun hZ => by
    have := h0 hZ
    omega
  refine ⟨hZ, ?_⟩
  obtain ⟨hQΩ, -⟩ := (h58 G L t S T hset).2 hZ
  obtain ⟨z, hzo, hzt, hΩ, -, -⟩ := h59 G L t S T hset
  have hz2 : z * z = 1 := by rw [← pow_two, ← hzo, pow_orderOf_eq_one]
  have hzQ : z ∈ S ⊓ coreActionKernel L := by
    rw [hQΩ, hΩ]
    exact mem_sup_right (mem_zpowers z)
  have hzt' : z ∉ zpowers t := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers' ht2 h with h1 | h1
    · rw [h1] at hzo
      simp at hzo
    · exact hzt h1
  obtain ⟨-, hcard⟩ := elemTwo_zpowers_sup hz2 (isElemTwo_zpowers ht2) (fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hZS z (mem_inf.mp hzQ).1) k).eq) hzt'
  have hQ4 : Nat.card ↥(S ⊓ coreActionKernel L) = 4 := by
    rw [hQΩ, hΩ, sup_comm, hcard, Nat.card_zpowers, hto]
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hZn : ((zStarIn L).subgroupOf L).Normal := by
    have h1 : (zStarIn L).subgroupOf L = Open.fusionZStar L :=
      comap_map_eq_self_of_injective L.subtype_injective _
    rw [h1, Sol78.fusionZStar_eq_comap]
    exact Subgroup.Normal.comap inferInstance _
  have hZsyl : IsSylowTwoIn (S ⊓ L ⊓ zStarIn L) (zStarIn L) :=
    isSylowTwoIn_inf_of_isSubnormal hS₀ (map_subtype_le _) hZn.isSubnormal
  have hZc := card_eq_two_pow_twoExp hZsyl
  rw [h3] at hZc
  have hZQ : S ⊓ L ⊓ zStarIn L ≤ S ⊓ coreActionKernel L := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).1, zStarIn_le_coreActionKernel L (mem_inf.mp hx).2⟩
  have heq := Subgroup.eq_of_le_of_card_ge hZQ (by rw [hQ4, hZc]; norm_num)
  rw [← heq]
  exact inf_le_left.trans inf_le_right

theorem commute_of_mem_zStarIn (hSol : SolomonCommutingCoreInput) {L : Subgroup G} {t u : G}
    (hto : orderOf t = 2) (hu2 : orderOf u = 2) (htu : t * u = u * t)
    (hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G))
    {K₁ S₁ : Subgroup G} (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x)
    (hS₁ : IsSylowTwoIn S₁ (normalizer (K₁ : Set G))) {b : G} (hb : b ∈ S₁ ⊓ zStarIn K₁)
    (hbo : orderOf b = 2) (h1 : twoExp (zStarIn K₁) = 1) :
    ∀ y ∈ oddIn L ⊓ centralizer ({u} : Set G), y * b = b * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K₁ hK₁u hK₁p
  obtain ⟨hbS₁, hbZ⟩ := mem_inf.mp hb
  have hb1 : b ≠ 1 := by rintro rfl; simp at hbo
  have hZK : zStarIn K₁ ≤ K₁ := map_subtype_le _
  have hab : ∀ x ∈ zStarIn K₁, ∀ x' ∈ zStarIn K₁, x * x' = x' * x := fun x hx x' hx' =>
    (mem_centralizer_singleton_iff.mp
      (le_centralizer_of_mem_zStarIn hK₁u hK₁p hO hx (hZK hx'))).symm
  have hP₀ : IsSylowTwoIn (S₁ ⊓ K₁) K₁ := isSylowTwoIn_inf_of_isSubnormal hS₁ le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hZn : ((zStarIn K₁).subgroupOf K₁).Normal := by
    have h1 : (zStarIn K₁).subgroupOf K₁ = Open.fusionZStar K₁ :=
      comap_map_eq_self_of_injective K₁.subtype_injective _
    rw [h1, Sol78.fusionZStar_eq_comap]
    exact Subgroup.Normal.comap inferInstance _
  have hPsyl : IsSylowTwoIn (S₁ ⊓ K₁ ⊓ zStarIn K₁) (zStarIn K₁) :=
    isSylowTwoIn_inf_of_isSubnormal hP₀ hZK hZn.isSubnormal
  have hPc := card_eq_two_pow_twoExp hPsyl
  rw [h1, pow_one] at hPc
  have hbP : b ∈ S₁ ⊓ K₁ ⊓ zStarIn K₁ := mem_inf.mpr ⟨mem_inf.mpr ⟨hbS₁, hZK hbZ⟩, hbZ⟩
  have hb2 : b * b = 1 := by rw [← pow_two, ← hbo, pow_orderOf_eq_one]
  intro y hy
  set c := y * b * y⁻¹ with hc
  have hcZ : c ∈ zStarIn K₁ := GrS4.conj_mem_zStarIn (hDN (hYD hy)) hbZ
  have hc2 : c * c = 1 := by
    rw [hc, show y * b * y⁻¹ * (y * b * y⁻¹) = y * (b * b) * y⁻¹ by group, hb2]
    group
  have hc1 : c ≠ 1 := fun h => hb1 (by
    calc b = y⁻¹ * c * y := by rw [hc]; group
      _ = 1 := by rw [h]; group)
  have hcP : c ∈ S₁ ⊓ K₁ ⊓ zStarIn K₁ := by
    refine HSFLit.L34Inv.le_of_isSylowTwoIn hPsyl (zpowers_le.mpr hcZ)
      (HSFLit.L34Inv.isPGroup_zpowers_of_mul_self hc2) (fun s hs => ?_) (mem_zpowers c)
    exact mem_normalizer_of_commute fun w hw => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact (Commute.zpow_right (show Commute s c from hab s (mem_inf.mp hs).2 c hcZ) k).eq
  have hcb := HSFLit.L34Uniq.eq_of_card_two hPc hcP hbP hc1 hb1
  calc y * b = c * y := by rw [hc]; group
    _ = b * y := by rw [hcb]

end CFSG.ComponentClassification.GrSLit.GrS5S
