module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVQStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVShear
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28WC
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28InvProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l28iv_conj_cases (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL28Normal M x J) {t₀ : G} (hT : (P : Subgroup G) ⊓ J = zpowers t₀)
    (ht₀ : orderOf t₀ = 9) {g : G}
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) ⊓ centralizer ({x} : Set G)) :
    g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers (t₀ ^ 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, hxLO, -, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  obtain ⟨hZQ, hxZ, hTZ, hcomm, hZc⟩ := l28iv_Z_facts hS hU0 hE1 hp hM hgen hJ
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hTdef
  set Z : Subgroup G := l28ivZ P x J with hZdef
  set y : G := g * x * g⁻¹ with hy
  have hyQ : y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := hg ⟨x, mem_zpowers x, rfl⟩
  have hyLO : IsLargeObstruction 3 M y :=
    isLargeObstruction_conj_of_map_le hS hU0 hp hM hxP hxLO (hg.trans inf_le_left)
  obtain ⟨-, hy1, hy3, -, -⟩ := id hyLO
  have ht₀T : t₀ ∈ T := by rw [hT]; exact mem_zpowers t₀
  have ht₀M : t₀ ∈ M := hPM ht₀T.1
  have h9 : t₀ ^ 9 = 1 := by rw [← ht₀]; exact pow_orderOf_eq_one t₀
  by_cases hyTZ : y ∈ T ⊔ Z
  swap
  ·
    exfalso
    obtain ⟨t, htT, hyt⟩ := l28iv_exists_moved hS hU0 hE1 hp hM hgen hJ hyQ.1 hyQ.2 hyTZ
    have hyt₀ : y * t₀ * y⁻¹ ≠ t₀ := by
      intro h
      apply hyt
      have htz : t ∈ zpowers t₀ := by rw [← hT]; exact htT
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp htz
      rw [← conj_zpow, h]
    have hyN : y * t₀ * y⁻¹ ∈ zpowers t₀ := by
      rw [← hT]
      refine ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hyQ.1 ht₀T.1)
        ((P : Subgroup G).inv_mem hyQ.1), ?_⟩
      exact (mem_normalizer_iff.mp (hJ.centralizer_le hyQ.2) t₀).mp ht₀T.2
    obtain ⟨hz1, hz3, hzy, hzT, hshear⟩ := l28iv_shear ht₀ hy3 hyN hyt₀
    set z : G := t₀ * (y * t₀ * y⁻¹)⁻¹ with hz
    have hzTT : z ∈ T := by rw [hT]; exact hzT
    have hyz : y ∉ zpowers z := fun h =>
      hyTZ (mem_sup_left ((zpowers_le.mpr hzTT) h))
    have hwz : t₀ * z * t₀⁻¹ = z := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hzT
      rw [← hk, mul_inv_eq_iff_eq_mul, ← zpow_one_add, ← zpow_add_one, add_comm]
    exact false_of_coset_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hyLO
      (hPM hzTT.1) hz1 hz3 hyz hzy ht₀M hshear hwz
  set u : G := t₀ ^ 3 with hu
  have hTZc : ∀ a ∈ T, ∀ c ∈ Z, a * c = c * a := hcomm
  obtain ⟨a, haT, c, hcZ, hac⟩ := u3l42_decomp hTZc hyTZ
  have hac3 : a ^ 3 = 1 ∧ c ^ 3 = 1 := by
    have h1 : a ^ 3 * c ^ 3 = 1 := by
      rw [← (Commute.mul_pow (show Commute a c from hTZc a haT c hcZ) 3), ← hac, hy3]
    have h2 : a ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a ^ 3 ∈ T ⊓ Z := Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ haT 3, by
      rw [h2]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcZ 3)⟩
    rw [hTZ, mem_bot] at h3
    refine ⟨h3, ?_⟩
    rw [h3] at h2
    exact inv_eq_one.mp h2.symm
  have hcx : c ∈ zpowers x := mem_zpowers_of_isCyclic_of_pow_three hZc hxZ hcZ hx1 hx3 hac3.2
  have huT : u ∈ T := by rw [hT]; exact pow_mem (mem_zpowers t₀) 3
  have hu3 : u ^ 3 = 1 := by rw [hu, ← pow_mul, show 3 * 3 = 9 from rfl, h9]
  have hu1 : u ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) h
    omega
  have hTcyc : IsCyclic ↥T := by rw [hT]; infer_instance
  have hau : a ∈ zpowers u := mem_zpowers_of_isCyclic_of_pow_three hTcyc huT haT hu1 hu3 hac3.1
  by_cases ha1 : a = 1
  · left
    rw [hac, ha1, one_mul]
    exact hcx
  by_cases hc1 : c = 1
  · right
    rw [hac, hc1, mul_one]
    exact hau
  exfalso
  obtain ⟨n, hnC, hnN, hninv⟩ := l28_exists_inverting l28SylowInversion_proved hgen hJ
  have hnx : n * x * n⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hnC)
  have hnu : n * u * n⁻¹ = u⁻¹ := hninv u huT hu3
  have hxu : x ∉ zpowers u := fun h => hxJ (zpowers_le.mpr huT.2 h)
  have hux : u * x = x * u := hTZc u huT x hxZ
  obtain ⟨hDel, hDc⟩ := plane_zpowers_sup (x := x) (k := u) hx3 hu1 hu3 hxu hux
  have hKz : ∀ t ∈ zpowers u, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_zpow (show Commute u x from hux) i j).eq
  have hmap : ∀ m : G, m * u * m⁻¹ ∈ zpowers u → m * x * m⁻¹ ∈ zpowers x →
      ∀ w ∈ zpowers u ⊔ zpowers x, m * w * m⁻¹ ∈ zpowers u ⊔ zpowers x := by
    intro m hmu hmx w hw
    obtain ⟨t, ht, c', hc', rfl⟩ := u3l42_decomp hKz hw
    have h1 : m * t * m⁻¹ ∈ zpowers u := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
      rw [← conj_zpow]
      exact zpow_mem hmu i
    have h2 : m * c' * m⁻¹ ∈ zpowers x := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc'
      rw [← conj_zpow]
      exact zpow_mem hmx j
    rw [show m * (t * c') * m⁻¹ = (m * t * m⁻¹) * (m * c' * m⁻¹) by group]
    exact Subgroup.mul_mem _ (mem_sup_left h1) (mem_sup_right h2)
  have hnU : n ∈ normalizer ((zpowers u ⊔ zpowers x : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro w
    refine ⟨hmap n (by rw [hnu]; exact inv_mem (mem_zpowers u))
      (by rw [hnx]; exact mem_zpowers x) w, fun hw => ?_⟩
    have hnu' : n⁻¹ * u * n⁻¹⁻¹ ∈ zpowers u := by
      have : n⁻¹ * u * n⁻¹⁻¹ = u⁻¹ := by
        rw [inv_inv]
        have h : n⁻¹ * (n * u * n⁻¹) * n = u := by group
        rw [hnu] at h
        calc n⁻¹ * u * n = (n⁻¹ * u⁻¹ * n)⁻¹ := by group
          _ = u⁻¹ := by rw [h]
      rw [this]
      exact inv_mem (mem_zpowers u)
    have hnx' : n⁻¹ * x * n⁻¹⁻¹ ∈ zpowers x := by
      have : n⁻¹ * x * n⁻¹⁻¹ = x := by
        rw [inv_inv]
        have h : n⁻¹ * (n * x * n⁻¹) * n = x := by group
        rwa [hnx] at h
      rw [this]
      exact mem_zpowers x
    have := hmap n⁻¹ hnu' hnx' _ hw
    rwa [show n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w by group] at this
  have hUM : zpowers u ⊔ zpowers x ≤ M :=
    sup_le (zpowers_le.mpr (hPM huT.1)) (zpowers_le.mpr (hPM hxP))
  have hnM : n ∈ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM
    (elementary_isPGroup 3 _ hDel) hUM (le_pRank_of_elemAbelian_card le_rfl hDel hDc) hnU
  have hxa : x ∉ zpowers a := fun h => hxJ (zpowers_le.mpr haT.2 h)
  have hax : a * x = x * a := hTZc a haT x hxZ
  have hyD : y ∈ zpowers a ⊔ zpowers x := by
    rw [hac]
    exact Subgroup.mul_mem _ (mem_sup_left (mem_zpowers a)) (mem_sup_right hcx)
  have hya : y ∉ zpowers a := fun h => by
    have hc' : c ∈ zpowers a := by
      rw [hac] at h
      simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers a)) h
    have : c ∈ T ⊓ Z := ⟨(zpowers_le.mpr haT) hc', hcZ⟩
    rw [hTZ, mem_bot] at this
    exact hc1 this
  have hyx : y ∉ zpowers x := fun h => by
    have ha' : a ∈ zpowers x := by
      rw [hac] at h
      simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hcx)
    have : a ∈ T ⊓ Z := ⟨haT, (zpowers_le.mpr hxZ) ha'⟩
    rw [hTZ, mem_bot] at this
    exact ha1 this
  exact false_of_mixed_pair hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hxLO
    (hPM haT.1) ha1 hac3.1 hxa hax hnM hnx (hninv a haT hac3.1) hyD hya hyx hyLO

end CFSG.LocalAnalysis.RankThreeTheoremC
