module

public import CFSG.GH74.QTGen4.Recog.Ku.Parabolics

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem normalizer_inf_of_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hA x) (hB x)

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

omit [Finite G] in
theorem le_normalizer_pCore (h : KuHyp G T M H P z) {x : G} (hx : x ∈ M) :
    x ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
  rw [← h.mNorm]
  exact hx

theorem oTwoUpper_inf_kuN_eq [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    oTwoUpper M ⊓ kuN P H = oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxM : x ∈ M := oTwoUpper_le M hxL
    refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
    have hV : x ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := h.le_normalizer_pCore hxM
    have hA : x ∈ Subgroup.normalizer (kuA P H : Set G) := hxN
    have hAV := normalizer_inf_of_normalizer hA hV
    rw [h.kuA_inf_pCore_M] at hAV
    exact hAV
  · intro x hx
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxM : x ∈ M := oTwoUpper_le M hxL
    exact Subgroup.mem_inf.mpr
      ⟨hxL, h.M_inf_normalizer_V2_le_normalizer_kuA (Subgroup.mem_inf.mpr ⟨hxM, hxN⟩)⟩

theorem card_oTwoUpper_inf_kuN [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    Nat.card ↥(oTwoUpper M ⊓ kuN P H) = 192 := by
  rw [h.oTwoUpper_inf_kuN_eq]
  exact h.card_L_inf_normalizer_kuV2

omit [Finite G] in
theorem pi_mem_stabS_of_normalizer (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    {t : G} (htN : t ∈ kuN P H) (ht : t ∈ Subgroup.normalizer (kuV2 T M : Set G)) :
    Ψ.π ⟨t, htN⟩ ∈ stabS := by
  intro v hv
  have hconj := (Subgroup.mem_normalizer_iff.mp ht (Ψ.Φ v)).mp ((Ψ.v2 v).mpr hv)
  have hact : t * Ψ.Φ v * t⁻¹ = Ψ.Φ (actS6 (Ψ.π ⟨t, htN⟩) v) := Ψ.act ⟨t, htN⟩ v
  rw [hact] at hconj
  exact (Ψ.v2 _).mp hconj

theorem exists_y2_mem_L2 [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    ∃ y : G, y ∈ oTwoUpper M ⊓ Ψ.L2 ∧ orderOf y = 3 := by
  obtain ⟨y, hyX, hy3⟩ := h.exists_order_three_X
  obtain ⟨hyL, hyV⟩ := Subgroup.mem_inf.mp hyX
  have hyM : y ∈ M := oTwoUpper_le M hyL
  have hyN : y ∈ kuN P H :=
    h.M_inf_normalizer_V2_le_normalizer_kuA (Subgroup.mem_inf.mpr ⟨hyM, hyV⟩)
  have hstab := pi_mem_stabS_of_normalizer Ψ hyN hyV
  have hy3' : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hpow : (⟨y, hyN⟩ : ↥(kuN P H)) ^ 3 = 1 := Subtype.ext (by simpa using hy3')
  have hcube : Ψ.π ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow, hpow, map_one]
  have hyL2 : y ∈ Ψ.L2 := (Ψ.mem_pre_iff lamS).mpr ⟨hyN, mem_lamS_of_pow_three _ hstab hcube⟩
  exact ⟨y, Subgroup.mem_inf.mpr ⟨hyL, hyL2⟩, hy3⟩

omit [Finite G] in
theorem oTwoUpper_inf_L2_eq_of_le (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    (hsub : oTwoUpper M ⊓ kuN P H ≤ Ψ.L2) :
    oTwoUpper M ⊓ Ψ.L2 = oTwoUpper M ⊓ kuN P H := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL, hxL2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxL, Ψ.pre_le_N lamS hxL2⟩
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hsub hx⟩

theorem card_oTwoUpper_inf_L2_of_le [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    (hsub : oTwoUpper M ⊓ kuN P H ≤ Ψ.L2) :
    Nat.card ↥(oTwoUpper M ⊓ Ψ.L2) = 192 := by
  rw [oTwoUpper_inf_L2_eq_of_le Ψ hsub]
  exact h.card_oTwoUpper_inf_kuN

end KuHyp

end CFSG.GH74.QTGen4.Ku
