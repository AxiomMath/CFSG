module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTwoB
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCenter
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCoset
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuIndec
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuStarD
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTrans
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTwoBasic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}
  {μ : G → ℕ} {ν : G → Fin 8} (hM : MaskCoords L T R μ ν)
include hM

theorem jFacts
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G)))
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {S : Subgroup G} (hSN : IsSylowOf 2 S (normalizer (R : Set G))) {f : G}
    (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) (hZ : S ⊓ centralizer (S : Set G) = zpowers f)
    {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    (h217 : centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G) ∨
      centralizer ({f} : Set G) ≤ normalizer (X : Set G)) :
    ∃ J : Subgroup G,
      (∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f) ∧
      pCoreOf 2 (centralizer ({f} : Set G)) = J ∧
      J ≤ centralizer ({f} : Set G) ∧ centralizer ({f} : Set G) ≤ normalizer (J : Set G) ∧
      (∃ σ : centralizer ({f} : Set G) →* Equiv.Perm (Fin 5), Function.Surjective σ ∧
        σ.ker = J.subgroupOf (centralizer ({f} : Set G))) ∧
      Nat.card J = 2 ^ 11 ∧ Nat.card (J ⊓ R : Subgroup G) = 2 ^ 9 ∧ X ≤ J ∧
      (∀ u ∈ J, ∀ v ∈ J, u * v * u⁻¹ * v⁻¹ ∈ X) ∧
      (∀ u ∈ J, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ zpowers f) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup 2 R := hS.isR.isPGroup
  have hNC := normalizer_inf_centralizer_eq hS h34 hR₂ h4 hCV
  have hidx := relIndex_normalizer_eq hS h34 hR₂ h4 hCV hNS
  have hNA := normalizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL hNS
  have hRS : R ≤ S := le_of_isSylowOf_normalizer hRp hSN
  have h210 := hM.exists_sq_eq_one_inv_mul_mem_of_le hNC hidx hSN.le hRS
  have hnot := not_centralizer_le_normalizer_of_not_isSylowOf hS h34 hR₂ h4
    (centralizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL) hNS hfA hf1
  have hXH := h217.resolve_left hnot
  have hAX : gmsA L T ≤ X := hM.gmsA_le_plane hX
  have hf2 : f * f = 1 := by
    have := (hM.sq_eq_one_iff (hM.le hfA)).mpr (by rw [(hM.ker _ (hM.le hfA)).mpr hfA]; rfl)
    rwa [pow_two] at this
  have hfZ : f ∈ S ⊓ centralizer (S : Set G) := by
    rw [hZ]
    exact mem_zpowers f
  have hfS : ∀ s ∈ S, s * f * s⁻¹ = f := by
    intro s hs
    rw [mem_centralizer_iff.mp (mem_inf.mp hfZ).2 s hs]
    group
  have hSX : S ≤ normalizer (X : Set G) := fun s hs =>
    hM.mem_normalizer_plane hX (hSN.le hs) (hfS s hs) hfA
  obtain ⟨J, hJ⟩ := exists_J hf2 hfS hSX
  obtain ⟨hcardJ, hXJ, hJS, hsqJ⟩ := hM.J_props hRp hNC hidx hSN hRS hfA hf1 hfS h210 hX hJ
  have hcardX := hM.card_plane hX hfA hf1
  have hXel := hM.isElemAbelian_plane hX
  have hJH : J ≤ centralizer ({f} : Set G) := fun v hv => mem_centralizer_singleton_iff.mpr (by
    calc v * f = v * f * v⁻¹ * v := by group
      _ = f * v := by rw [hfS v (hJS hv)])
  have hidx120 := hM.relIndex_J_eq hRp hNC hidx h216 hSN hRS hfA hf1 hfS h210 hX hJ hXH hnot
  have hJ' : ∀ h, h ∈ J ↔ h ∈ centralizer ({f} : Set G) ∧
      ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ zpowers f := by
    intro h
    rw [hM.mem_J_iff_of_mem_centralizer hNC hidx hNA hRp hSN hRS hfA hf1 hfS hX hJ h]
    simp only [mem_zpowers_of_mul_self hf2]
  have hZX : zpowers f ≤ X := zpowers_le.mpr (hAX hfA)
  have hcardZ : Nat.card (zpowers f) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hf2) hf1
  have hHZ : ∀ h ∈ centralizer ({f} : Set G), ∀ z ∈ zpowers f, h * z * h⁻¹ = z := by
    intro h hh z hz
    rcases (mem_zpowers_of_mul_self hf2).mp hz with h1 | h1
    · rw [h1]
      group
    · rw [h1, mem_centralizer_singleton_iff.mp hh]
      group
  have hHX : ∀ h ∈ centralizer ({f} : Set G), ∀ x ∈ X, h * x * h⁻¹ ∈ X :=
    fun h hh x hx => (mem_normalizer_iff.mp (hXH hh) x).mp hx
  have hne : ∀ x, x ∉ zpowers f → x ≠ 1 ∧ x ≠ f := fun x hx =>
    ⟨fun h => hx ((mem_zpowers_of_mul_self hf2).mpr (Or.inl h)),
      fun h => hx ((mem_zpowers_of_mul_self hf2).mpr (Or.inr h))⟩
  have htr : ∀ x ∈ X, x ∉ zpowers f → ∀ x' ∈ X, x' ∉ zpowers f →
      ∃ h ∈ centralizer ({f} : Set G), h * x * h⁻¹ * x'⁻¹ ∈ zpowers f := by
    intro x hx hxZ x' hx' hx'Z
    obtain ⟨hx1, hxf⟩ := hne x hxZ
    obtain ⟨hx'1, hx'f⟩ := hne x' hx'Z
    obtain ⟨h, hh, hhx⟩ :=
      hM.exists_conj_eq_of_mem_plane hNC hidx hfA hf1 hX hXH hnot hx hx1 hxf hx' hx'1 hx'f
    refine ⟨h, hh, ?_⟩
    rw [hhx, mul_inv_cancel]
    exact one_mem _
  obtain ⟨⟨σ, hσs, hσk⟩, -⟩ :=
    dempwolff218Hyp G hXel hcardX hZX hcardZ hHZ hHX hJ' hidx120 htr
  have hQ : pCoreOf 2 (centralizer ({f} : Set G)) = J :=
    pCoreOf_eq_of_perm_five σ hσs hσk hJH (IsPGroup.of_card hcardJ)
  have hJn : centralizer ({f} : Set G) ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hJH).mp (hσk ▸ σ.normal_ker)
  exact ⟨J, hJ, hQ, hJH, hJn, ⟨σ, hσs, hσk⟩, hcardJ, hM.card_J_inf_R hfA hf1 hRS hX hJ, hXJ,
    fun u hu v hv => comm_mem_X_of_mem_J (hJH.trans hXH) hsqJ hu hv,
    fun u hu x hx => ((hJ' u).mp hu).2 x hx⟩

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
