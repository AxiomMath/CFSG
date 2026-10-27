module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZStrong
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BTClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3q510Syl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec5ZGoldData {X : Type} [Group X] (Sb Tb : Subgroup X) : Prop where
  le : Tb ≤ Sb
  comm : ∀ a ∈ Tb, ∀ b ∈ Tb, a * b = b * a
  sq : ∀ a ∈ Tb, a * a = 1
  card : Nat.card ↥Tb = 4
  closed : ∀ a ∈ Tb, ∀ g : X, g⁻¹ * a * g ∈ Sb → g⁻¹ * a * g ∈ Tb
  trans : ∀ a ∈ Tb, ∀ b ∈ Tb, a ≠ 1 → b ≠ 1 → ∃ g : X, g⁻¹ * a * g = b

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

local notation "𝓗" => centralizer (Singleton.singleton z : Set G)

theorem sec5z_exists_sylow_quotient (h : Sec510Ctx G t L S z r ρ B A φ)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = (S.subgroupOf (centralizer ({z} : Set G))).map π := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH : S ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.central s hs)
  have hP : IsPGroup 2 ↥(S.subgroupOf (centralizer ({z} : Set G))) :=
    h.syl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hnd : ¬ 2 ∣ (S.subgroupOf (centralizer ({z} : Set G))).index := fun hd =>
    h.syl.2.2 (by
      rw [← Subgroup.relIndex_mul_relIndex S (centralizer ({z} : Set G)) ⊤ hSH le_top]
      exact Dvd.dvd.mul_right hd _)
  refine ⟨(hP.toSylow hnd).mapSurjective hπ, ?_⟩
  rw [Sylow.coe_mapSurjective, IsPGroup.toSylow_coe]

theorem sec5z_gold_data (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTE : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = sec5p510_E t a b)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    Sec5ZGoldData ((S.subgroupOf (centralizer ({z} : Set G))).map π)
      (((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
        (centralizer ({z} : Set G))).map π) := by
  have hSH : S ≤ 𝓗 := fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (h.central s hs)
  have hTS : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) ≤ S :=
    (sec5p510_T_le_R t z _).trans inf_le_left
  have hTH : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) ≤ 𝓗 := hTS.trans hSH
  have hzT : z ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) := by
    rw [hTE]
    exact sec5p510_z_mem_E h hs.ab
  have hTA : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) ≤ A := by
    rw [hTE]
    exact sec5p510_E_le_A h hs.ab
  have htz : t * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 h.mem_S)).symm
  have htH : t ∈ 𝓗 := Subgroup.mem_centralizer_singleton_iff.mpr htz
  have hzH : z ∈ 𝓗 := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hπz : π ⟨z, hzH⟩ = 1 := by
    have : (⟨z, hzH⟩ : ↥𝓗) ∈ π.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z)
    exact this
  have hmemT : ∀ c₀ : ↥𝓗,
      c₀ ∈ (sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf 𝓗 →
        (c₀ : G) ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) :=
    fun c₀ hc₀ => Subgroup.mem_subgroupOf.mp hc₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro c ⟨c₀, hc₀, rfl⟩
    exact ⟨c₀, Subgroup.mem_subgroupOf.mpr (hTS (hmemT c₀ hc₀)), rfl⟩
  ·
    rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (sec5p510_A_comm h (hTA (hmemT a₀ ha₀)) (hTA (hmemT b₀ hb₀)))
  ·
    rintro _ ⟨a₀, ha₀, rfl⟩
    rw [← map_mul]
    have : a₀ * a₀ = 1 := Subtype.ext (by
      push_cast
      exact sec5p510_A_sq h (hTA (hmemT a₀ ha₀)))
    rw [this, map_one]
  ·
    have hcardT' : Nat.card ↥((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁)
        (twoCoreIn K₂))).subgroupOf 𝓗) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, hTE]
      exact sec5p510_card_E h hs.ab
    have hmain := Subgroup.card_ker_mul_card_range (π.domRestrict
      ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf 𝓗))
    rw [MonoidHom.domRestrict_range, hcardT'] at hmain
    have hker2 : Nat.card (π.domRestrict
        ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf 𝓗)).ker = 2 := by
      have hinj : Function.Injective ((𝓗).subtype.comp
          ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf 𝓗).subtype) :=
        (𝓗).subtype_injective.comp Subtype.val_injective
      have himg : (π.domRestrict
          ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf 𝓗)).ker.map
          ((𝓗).subtype.comp
            ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf 𝓗).subtype)
            = zpowers z := by
        ext w
        constructor
        · rintro ⟨c, hc, rfl⟩
          have h1 : π (c : ↥𝓗) = 1 := hc
          have h2 : (c : ↥𝓗) ∈ π.ker := h1
          rw [hker] at h2
          exact Subgroup.mem_subgroupOf.mp h2
        · intro hw
          have hwT : w ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) :=
            (Subgroup.zpowers_le.mpr hzT) hw
          have hwH : w ∈ 𝓗 := hTH hwT
          refine ⟨⟨⟨w, hwH⟩, Subgroup.mem_subgroupOf.mpr hwT⟩, ?_, rfl⟩
          show π ⟨w, hwH⟩ = 1
          have : (⟨w, hwH⟩ : ↥𝓗) ∈ π.ker := by
            rw [hker]
            exact Subgroup.mem_subgroupOf.mpr hw
          exact this
      rw [← Subgroup.card_map_of_injective hinj, himg, Nat.card_zpowers, h.pocket.1]
    rw [hker2] at hmain
    omega
  ·
    intro c hc g hg
    exact sec5z_strongly_closed_quotient hy h55 h58d hFB h4 h hs hTE π hπ hker c hc g hg
  ·
    have key : ∀ c₀ : ↥𝓗,
        (c₀ : G) ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) → π c₀ ≠ 1 →
          ∃ k : ↥𝓗, π c₀ = π k * π ⟨t, htH⟩ * (π k)⁻¹ := by
      intro c₀ hcT hc1
      have hnz : (c₀ : G) ∉ zpowers z := fun hz => hc1 (by
        have : c₀ ∈ π.ker := by
          rw [hker]
          exact Subgroup.mem_subgroupOf.mpr hz
        exact this)
      have hxE : (c₀ : G) ∈ sec5p510_E t a b := by
        rw [← hTE]
        exact hcT
      have hx2 : (c₀ : G) * c₀ = 1 := sec5p510_A_sq h (sec5p510_E_le_A h hs.ab hxE)
      obtain ⟨y, hyH, hxy⟩ := hs.T_invol c₀ hcT (by rw [hx2]; exact one_mem _) hnz
      obtain ⟨k, hk, hyk⟩ := hyH
      refine ⟨⟨k, hk⟩, ?_⟩
      rcases hxy with hxy | hxy
      · have e : c₀ = (⟨k, hk⟩ : ↥𝓗) * ⟨t, htH⟩ * (⟨k, hk⟩ : ↥𝓗)⁻¹ :=
          Subtype.ext (by push_cast; rw [hxy, hyk])
        rw [e, map_mul, map_mul, map_inv]
      · have e : c₀ = ((⟨k, hk⟩ : ↥𝓗) * ⟨t, htH⟩ * (⟨k, hk⟩ : ↥𝓗)⁻¹) * ⟨z, hzH⟩ :=
          Subtype.ext (by push_cast; rw [hxy, hyk])
        rw [e, map_mul, map_mul, map_mul, map_inv, hπz, mul_one]
    rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩ hna hnb
    obtain ⟨k, hk⟩ := key a₀ (hmemT a₀ ha₀) hna
    obtain ⟨l, hl⟩ := key b₀ (hmemT b₀ hb₀) hnb
    refine ⟨π k * (π l)⁻¹, ?_⟩
    rw [hk, hl]
    group

end CFSG.OddStandard.SmallF3.Omega
