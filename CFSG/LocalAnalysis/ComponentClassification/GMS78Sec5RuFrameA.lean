module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Main
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCenter
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCoset
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNotSylow
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuStarD
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTrans
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTwoBasic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

structure Sec3.SzR.FrameData {G : Type} [Group G] (L T R : Subgroup G) (μ : G → ℕ)
    (ν : G → Fin 8) (S : Subgroup G) (f : G) (X J : Subgroup G) : Prop where
  coords : Sec3.SzR.MaskCoords L T R μ ν
  inf_centralizer : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R
  relIndex : R.relIndex (normalizer (R : Set G)) = 168
  normalizer_gmsA : normalizer (gmsA L T : Set G) = normalizer (R : Set G)
  pCoreOf_eq : pCoreOf 2 (normalizer (gmsA L T : Set G)) = R
  card_R : Nat.card R = 2 ^ 11
  isPGroup : IsPGroup 2 R
  sylow : IsSylowOf 2 S (normalizer (R : Set G))
  sylow_top : IsSylowOf 2 S ⊤
  le_S : R ≤ S
  mem_gmsA : f ∈ gmsA L T
  ne_one : f ≠ 1
  center_eq : S ⊓ centralizer (S : Set G) = zpowers f
  conj_eq : ∀ s ∈ S, s * f * s⁻¹ = f
  coset : ∀ g ∈ S, g ∉ R → g ^ 2 ∈ R → ∃ y ∈ S, y ^ 2 = 1 ∧ g⁻¹ * y ∈ R
  plane : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)
  J_mem : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f
  not_le : ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G)

namespace SzMinCounter

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem card_centralizer_eq_of_mem_T₀
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) {e : G}
    (he : e ∈ T ⊓ centralizer (L : Set G)) (he1 : e ≠ 1) :
    Nat.card (centralizer ({e} : Set G)) = 116480 := by
  rw [hM.centralizer_eq_sup h3 hF hZ h4 hO he he1]
  have hZL := hM.center_eq_bot h3 hF hZ h4 hO
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hL : Nat.card L = 29120 := by
    have h1 : Nat.card (rankTwoQuot L) = 29120 := by
      rw [Nat.card_congr eS.toEquiv, card_Sz_one]
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [show Nat.card (center L) = 1 by rw [hZL, card_bot], mul_one] at h2
    rw [h2]
    exact h1
  have hN : T ⊓ centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    inf_le_right.trans (centralizer_le_normalizer _)
  have hdisj : L ⊓ (T ⊓ centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxK⟩ := mem_inf.mp hx
    have hz : (⟨x, hxL⟩ : L) ∈ center L := mem_center_iff.mpr fun l =>
      Subtype.ext (mem_centralizer_iff.mp (mem_inf.mp hxK).2 l l.2)
    rw [hZL, mem_bot] at hz
    exact (mem_bot).mpr (congrArg Subtype.val hz)
  rw [sup_comm, AS76b.card_sup_eq_mul hN hdisj, hL, h4]

theorem exists_mem_normalizer_card_centralizer
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) :
    ∃ e ∈ normalizer (gmsA L T : Set G), orderOf e = 2 ∧
      Nat.card (centralizer ({e} : Set G)) = 116480 := by
  obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h3.T₀_ne_bot
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have hT₀el := h3.isElemAbelian_T₀ hF
  have hAL : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  refine ⟨e, centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha =>
    mem_centralizer_iff.mp (mem_inf.mp he).2 a (hAL ha)), orderOf_eq_prime (hT₀el.2 e he) he1',
    hM.card_centralizer_eq_of_mem_T₀ h3 hF hZ h4 hO he he1'⟩

theorem exists_frameData
    (hF : Foundation) (hS3 : B1Stage3)
    (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d) (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :
    ∃ (μ : G → ℕ) (ν : G → Fin 8) (S : Subgroup G) (f : G) (X J : Subgroup G),
      Sec3.SzR.FrameData L T R μ ν S f X J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := hS.sec3
  have hZ : Odd (Nat.card (center L)) := hS.oddCenter
  have hO := dempwolffOddCore_of hF hS3 G L hM _ h3.isSylowOf_T₀ h4
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  have hCV := hM.centralizer_gmsV_eq h3 hS.foundation hZ h4 hO
  have hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L := fun e he he1 =>
    hM.centralizer_eq_sup h3 hS.foundation hZ h4 hO he he1
  have hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G) := fun a haL ha1 ha2 =>
    hM.isPGroup_inf_centralizer h3 hS.foundation hZ h4 hO haL ha1 ha2
  have hNS := hS.not_isSylowOf_normalizer hM hR₂
  obtain ⟨μ, ν, hMC⟩ := Sec3.SzR.exists_maskCoords hS h34 hR₂ h4 hNS
  obtain ⟨S, hSN⟩ := exists_isSylowOf 2 (normalizer (R : Set G))
  have hRp : IsPGroup 2 R := hS.isR.isPGroup
  have hRS : R ≤ S := le_of_isSylowOf_normalizer hRp hSN
  obtain ⟨f, hfA, hf1, hZf⟩ := Sec3.SzR.exists_center_eq hS h34 hR₂ h4 hCV hCe hCL hNS hSN
  have hNC := Sec3.SzR.normalizer_inf_centralizer_eq hS h34 hR₂ h4 hCV
  have hidx := Sec3.SzR.relIndex_normalizer_eq hS h34 hR₂ h4 hCV hNS
  have hfZ : f ∈ S ⊓ centralizer (S : Set G) := by
    rw [hZf]
    exact mem_zpowers f
  have hfS : ∀ s ∈ S, s * f * s⁻¹ = f := by
    intro s hs
    rw [mem_centralizer_iff.mp (mem_inf.mp hfZ).2 s hs]
    group
  have hf2 : f * f = 1 := by
    have := (hMC.sq_eq_one_iff (hMC.le hfA)).mpr (by rw [(hMC.ker _ (hMC.le hfA)).mpr hfA]; rfl)
    rwa [pow_two] at this
  obtain ⟨X, hX⟩ := hMC.exists_plane f
  have hSX : S ≤ normalizer (X : Set G) := fun s hs =>
    hMC.mem_normalizer_plane hX (hSN.le hs) (hfS s hs) hfA
  obtain ⟨J, hJ⟩ := Sec3.SzR.MaskCoords.exists_J hf2 hfS hSX
  exact ⟨μ, ν, S, f, X, J, hMC, hNC, hidx,
    Sec3.SzR.normalizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL hNS,
    Sec3.SzR.pCoreOf_normalizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL hNS, hMC.card_R, hRp, hSN,
    Sec3.SzR.isSylowOf_top_of_isSylowOf_normalizer hS h34 hR₂ h4 hCV hCe hCL hNS hSN, hRS, hfA,
    hf1, hZf, hfS, hMC.exists_sq_eq_one_inv_mul_mem_of_le hNC hidx hSN.le hRS, hX, hJ,
    Sec3.SzR.not_centralizer_le_normalizer_of_not_isSylowOf hS h34 hR₂ h4
      (Sec3.SzR.centralizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL) hNS hfA hf1⟩

end SzMinCounter

end CFSG.ComponentClassification.GMS78
