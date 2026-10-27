module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KNormalRankComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

namespace HypCGen

variable {M E H : Subgroup G}

theorem le_normalizer_kSub_of_fiveTypes (h : HypCGen G M 3 E H) (hfive : FiveTypes M H)
    (hU : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3)
    (hL : ¬ pLayerIn 3 H ≤ M) : H ≤ normalizer (kSub 3 M H : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨J₀, hJ₀, h2⟩ := hfive.exists_pComponentIn_two_le_pRank
  have hσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet
  have h3N : ∀ T : Subgroup G, T ≤ H → IsPGroup 3 T →
      T ≤ H ⊓ normalizer (kSub 3 M H : Set G) := by
    intro T hTH hT z hz
    refine ⟨hTH hz, ?_⟩
    have hodd : Odd (orderOf z) := by
      obtain ⟨n, hn⟩ := hT ⟨z, hz⟩
      have hd : orderOf z ∣ 3 ^ n := by
        rw [← Subgroup.orderOf_mk z hz]
        exact orderOf_dvd_of_pow_eq_one hn
      exact (Odd.pow (by decide : Odd 3)).of_dvd_nat hd
    exact NineSettingGen.mem_normalizer_kSub_of_odd h.toNineSettingGen h.mem_H2Fam hσ hJ₀ h2 hL
      (hTH hz) hodd
  have hHM : ∀ {m : G}, m ∈ H → m ∈ M → m ∈ normalizer (kSub 3 M H : Set G) := by
    intro m hmH hmM
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact conj_mem_kSub (p := 3) (M := M) (H := H) hmH hmM hn
    · intro hn
      have h := conj_mem_kSub (p := 3) (M := M) (H := H) (H.inv_mem hmH) (M.inv_mem hmM) hn
      have h' : m⁻¹ * (m * n * m⁻¹) * (m⁻¹)⁻¹ = n := by group
      rwa [h'] at h
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (H ⊓ M)
  obtain ⟨hPH, hPn⟩ := isSylowOf_of_NineNineOne h.maxLocal h.mem_QSet h.E_le_H hσ hU hP
  intro y hy
  have hPle : P ≤ H := hP.le.trans inf_le_left
  have hP'le : P.map (MulAut.conj y).toMonoidHom ≤ H := by
    rintro _ ⟨p, hp, rfl⟩
    simpa [MulAut.conj_apply] using H.mul_mem (H.mul_mem hy (hPle hp)) (H.inv_mem hy)
  have hPcard : Nat.card (P.map (MulAut.conj y).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 3
      (P.map (MulAut.conj y).toMonoidHom) H :=
    CFSG.ABGLocalTools.isSylowOf_of_card hP'le (by rw [hPcard, hPH.card_eq])
  have hPN : P ≤ H ⊓ normalizer (kSub 3 M H : Set G) := h3N P hPle hP.isPGroup
  have hP'N : P.map (MulAut.conj y).toMonoidHom ≤
      H ⊓ normalizer (kSub 3 M H : Set G) := h3N _ hP'le hP'syl.isPGroup
  have hPN' : CFSG.ABGLocalTools.IsSylowOf 3 P
      (H ⊓ normalizer (kSub 3 M H : Set G)) := hPH.of_le hPN inf_le_left
  have hP'N' : CFSG.ABGLocalTools.IsSylowOf 3 (P.map (MulAut.conj y).toMonoidHom)
      (H ⊓ normalizer (kSub 3 M H : Set G)) := hP'syl.of_le hP'N inf_le_left
  obtain ⟨k, hk, hkconj⟩ := hPN'.exists_mem_conj hP'N'
  have hkyP : k⁻¹ * y ∈ normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hyz : y * z * y⁻¹ ∈ P.map (MulAut.conj y).toMonoidHom := by
        simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hz
      have h1 := (hkconj (y * z * y⁻¹)).mp hyz
      have hEq : (k⁻¹ * y) * z * (k⁻¹ * y)⁻¹ = k⁻¹ * (y * z * y⁻¹) * k := by group
      rwa [hEq]
    · intro hz
      have hz' : k⁻¹ * (y * z * y⁻¹) * k ∈ P := by
        have hEq : k⁻¹ * (y * z * y⁻¹) * k = (k⁻¹ * y) * z * (k⁻¹ * y)⁻¹ := by group
        rwa [hEq]
      have hyz : y * z * y⁻¹ ∈ P.map (MulAut.conj y).toMonoidHom :=
        (hkconj (y * z * y⁻¹)).mpr hz'
      have h1 := (CFSG.Quasithin.A38.mem_map_conj).mp hyz
      simpa [mul_assoc] using h1
  have hkyM : k⁻¹ * y ∈ M := hPn hkyP
  have hkyH : k⁻¹ * y ∈ H := H.mul_mem (H.inv_mem hk.1) hy
  have hyEq : y = k * (k⁻¹ * y) := by group
  rw [hyEq]
  exact Subgroup.mul_mem _ hk.2 (hHM hkyH hkyM)

end HypCGen

theorem kNormalAt_of_preamble {M : Subgroup G} (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) : KNormalAt M := by
  intro q E H h
  have hq3 : q = 3 := eq_three_of_mem hpre h.mem_QSet h.mem
  subst q
  exact h.le_normalizer_kSub_of_fiveTypes (hpre 3 E h.mem_QSet H h.mem).2 (hU 3 E H h)
    (hL 3 E H h)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
