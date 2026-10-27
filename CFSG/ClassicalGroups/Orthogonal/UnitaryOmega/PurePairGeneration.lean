module

import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
import CFSG.ClassicalInvolution.Phan.PhanDn.NormFormType
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapGen

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.LieType.SeitzGeneration
open Module QuadraticMap

section Generation

variable {k V : Type} [Field k] [Finite k] [CharP k 2] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V}

omit [Finite k] [FiniteDimensional k V] in
private theorem polar_self_charTwo (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_smul, CharTwo.add_self_eq_zero]

omit [Finite k] [CharP k 2] [FiniteDimensional k V] in
private theorem exists_polar_eq_one_of_polarNondegOn {W : Submodule k V}
    (hW : PolarNondegOn Q W) {x : V} (hx : x ∈ W) (hx0 : x ≠ 0) :
    ∃ y ∈ W, polar Q x y = 1 := by
  obtain ⟨y, hyW, hy⟩ := hW.exists_polar_ne_zero hx hx0
  refine ⟨(polar Q x y)⁻¹ • y, W.smul_mem _ hyW, ?_⟩
  rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]

omit [Finite k] [CharP k 2] [FiniteDimensional k V] in
private theorem polar_sup_left_eq_zero {S T U : Submodule k V}
    (hSU : ∀ x ∈ S, ∀ y ∈ U, polar Q x y = 0) (hTU : ∀ x ∈ T, ∀ y ∈ U, polar Q x y = 0) :
    ∀ x ∈ S ⊔ T, ∀ y ∈ U, polar Q x y = 0 := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [polar_add_left, hSU a ha y hy, hTU b hb y hy, add_zero]

omit [Finite k] [CharP k 2] in
private theorem finrank_sup_of_polar_eq_zero {S T : Submodule k V} (hS : PolarNondegOn Q S)
    (hST : ∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0) :
    finrank k ↥(S ⊔ T) = finrank k S + finrank k T := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S T
  rwa [(CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint hS hST).eq_bot, finrank_bot,
    add_zero] at h

omit [Finite k] [CharP k 2] in
private theorem supportedDerived_le_orthogonalGroup {W : Submodule k V}
    (hW : PolarNondegOn Q W) :
    supportedDerived Q W ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (supportedDerived_le_orthDerived_of_regular
    (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hW)).trans
    (orthDerived_le_orthogonalGroup_of_commutator Q)

omit [Finite k] [CharP k 2] [FiniteDimensional k V] in
private theorem eichler_mem_supportedDerived_of_two_lt (hk : 2 < Nat.card k)
    {W : Submodule k V} (hW : PolarNondegOn Q W) {e w : V} (he : e ∈ W) (hw : w ∈ W)
    (hQe : Q e = 0) (hew : polar Q e w = 0) : eichler Q e w ∈ supportedDerived Q W := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne hk 1
  exact eichler_mem_supportedDerived he hw hQe hew
    (CFSG.SeitzReduction.OmegaPilot.eichler_mem_orthDerived_of_ne_zero_ne_one
      (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hW) hc0 hc1 _ _)

omit [Finite k] [FiniteDimensional k V] in
private theorem exists_mem_sup_polar_eq {U₁ U₂ : Submodule k V} (h₁ : PolarNondegOn Q U₁)
    (h₂ : PolarNondegOn Q U₂) (h₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) {s₁ s₂ : V}
    (hs₁ : s₁ ∈ U₁) (hs₂ : s₂ ∈ U₂) (hs₁0 : s₁ ≠ 0) (hs₂0 : s₂ ≠ 0) (p : k) :
    ∃ a ∈ U₁ ⊔ U₂, polar Q (s₁ + s₂) a = 0 ∧ polar Q a s₂ = p := by
  obtain ⟨y₁, hy₁, hsy₁⟩ := exists_polar_eq_one_of_polarNondegOn h₁ hs₁ hs₁0
  obtain ⟨y₂, hy₂, hsy₂⟩ := exists_polar_eq_one_of_polarNondegOn h₂ hs₂ hs₂0
  refine ⟨p • (y₁ + y₂), Submodule.smul_mem _ p
    (add_mem (Submodule.mem_sup_left hy₁) (Submodule.mem_sup_right hy₂)), ?_, ?_⟩
  · rw [polar_smul_right, polar_add_left, polar_add_right, polar_add_right, hsy₁, hsy₂,
      h₁₂ s₁ hs₁ y₂ hy₂, polar_comm Q s₂ y₁, h₁₂ y₁ hy₁ s₂ hs₂, add_zero, zero_add,
      CharTwo.add_self_eq_zero, smul_zero]
  · rw [polar_smul_left, polar_add_left, h₁₂ y₁ hy₁ s₂ hs₂, polar_comm Q y₂ s₂, hsy₂, zero_add,
      smul_eq_mul, mul_one]

omit [Finite k] [CharP k 2] [FiniteDimensional k V] in
private theorem eichler_add_smul_apply {s₂ β a : V} {c : k} (hQt : Q (s₂ + β) = 0)
    (htz : polar Q (s₂ + β) (c • s₂) = 0) (haβ : polar Q a β = 0) :
    eichler Q (s₂ + β) (c • s₂) a =
      a + (polar Q a s₂ * c - polar Q a s₂ * (c * (1 + c * Q s₂))) • s₂ -
        (polar Q a s₂ * (c * (1 + c * Q s₂))) • β := by
  rw [eichler_apply hQt htz, polar_add_right, haβ, add_zero, polar_smul_right,
    QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
  module

omit [Finite k] in
private theorem smul_mem_rootSet_sup (hk : 2 < Nat.card k) {U₁ U₂ U₃ : Submodule k V}
    (h₁ : PolarNondegOn Q U₁) (h₂ : PolarNondegOn Q U₂) (h₃ : PolarNondegOn Q U₃)
    (h₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) (h₁₃ : ∀ x ∈ U₁, ∀ y ∈ U₃, polar Q x y = 0)
    (h₂₃ : ∀ x ∈ U₂, ∀ y ∈ U₃, polar Q x y = 0) {s₁ s₂ β : V} (hs₁ : s₁ ∈ U₁)
    (hs₂ : s₂ ∈ U₂) (hs₁0 : s₁ ≠ 0) (hq : Q s₂ ≠ 0) (hQs : Q (s₁ + s₂) = 0) (hβ : β ∈ U₃)
    (hQβ : Q β = Q s₂) (r : k) :
    r • β ∈ rootSet Q (supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃))
      (s₁ + s₂) := by
  have hA := CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup h₁ h₂ h₁₂
  have hB := CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup h₂ h₃ h₂₃
  have hs : s₁ + s₂ ∈ U₁ ⊔ U₂ :=
    add_mem (Submodule.mem_sup_left hs₁) (Submodule.mem_sup_right hs₂)
  have hroot : ∀ a ∈ U₁ ⊔ U₂, polar Q (s₁ + s₂) a = 0 → a ∈ rootSet Q
      (supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃)) (s₁ + s₂) :=
    fun a ha hsa => ⟨hsa, Subgroup.mem_sup_left
      (eichler_mem_supportedDerived_of_two_lt hk hA hs ha hQs hsa)⟩
  have hs₂β := h₂₃ s₂ hs₂ β hβ
  have hss : polar Q (s₁ + s₂) s₂ = 0 := by
    rw [polar_add_left, h₁₂ s₁ hs₁ s₂ hs₂, polar_self_charTwo, add_zero]
  obtain ⟨c, hc0, hcq⟩ := exists_ne_zero_ne hk (Q s₂)⁻¹
  have hκ : c * (1 + c * Q s₂) ≠ 0 := mul_ne_zero hc0 fun h => hcq
    (eq_inv_of_mul_eq_one_left (by linear_combination h - CharTwo.two_eq_zero (R := k)))
  obtain ⟨a, ha, hsa, hpa⟩ := exists_mem_sup_polar_eq h₁ h₂ h₁₂ hs₁ hs₂ hs₁0
    (fun h => hq (by rw [h, map_zero])) (r * (c * (1 + c * Q s₂))⁻¹)
  have hQt : Q (s₂ + β) = 0 := by
    rw [QuadraticMap.map_add Q, hQβ, hs₂β, add_zero, CharTwo.add_self_eq_zero]
  have htz : polar Q (s₂ + β) (c • s₂) = 0 := by
    rw [polar_smul_right, polar_add_left, polar_self_charTwo, polar_comm Q β s₂, hs₂β,
      add_zero, smul_zero]
  have hg : eichler Q (s₂ + β) (c • s₂) ∈
      supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃) :=
    Subgroup.mem_sup_right (eichler_mem_supportedDerived_of_two_lt hk hB
      (add_mem (Submodule.mem_sup_left hs₂) (Submodule.mem_sup_right hβ))
      (Submodule.smul_mem _ c (Submodule.mem_sup_left hs₂)) hQt htz)
  have hgs : eichler Q (s₂ + β) (c • s₂) (s₁ + s₂) = s₁ + s₂ := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_add_right, hss, polar_add_left, h₁₃ s₁ hs₁ β hβ, hs₂β, add_zero, add_zero]
    · rw [polar_smul_right, hss, smul_zero]
  have hga := rootSet_map (sup_le (supportedDerived_le_orthogonalGroup hA)
    (supportedDerived_le_orthogonalGroup hB)) hg (hroot a ha hsa)
  rw [hgs, eichler_add_smul_apply hQt htz (polar_sup_left_eq_zero h₁₃ h₂₃ a ha β hβ), hpa,
    inv_mul_cancel_right₀ hκ] at hga
  have hmem := hroot (a + (r * (c * (1 + c * Q s₂))⁻¹ * c - r) • s₂)
    (add_mem ha (Submodule.smul_mem _ _ (Submodule.mem_sup_right hs₂)))
    (by rw [polar_add_right, hsa, polar_smul_right, hss, smul_zero, add_zero])
  have hsub := sub_mem hmem hga
  rwa [sub_sub_cancel] at hsub

omit [Finite k] in
private theorem mem_rootSet_of_mem_third (hk : 2 < Nat.card k) {U₁ U₂ U₃ : Submodule k V}
    (h₁ : PolarNondegOn Q U₁) (h₂ : PolarNondegOn Q U₂) (h₃ : PolarNondegOn Q U₃)
    (ha₁ : ∀ u ∈ U₁, Q u = 0 → u = 0) (ha₂ : ∀ u ∈ U₂, Q u = 0 → u = 0)
    (ha₃ : ∀ u ∈ U₃, Q u = 0 → u = 0)
    (h₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) (h₁₃ : ∀ x ∈ U₁, ∀ y ∈ U₃, polar Q x y = 0)
    (h₂₃ : ∀ x ∈ U₂, ∀ y ∈ U₃, polar Q x y = 0) {s : V} (hs : s ∈ U₁ ⊔ U₂) (hs0 : s ≠ 0)
    (hQs : Q s = 0) {u : V} (hu : u ∈ U₃) :
    u ∈ rootSet Q (supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃)) s := by
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs
  have hs₁0 : s₁ ≠ 0 := by
    rintro rfl
    rw [zero_add] at hQs hs0
    exact hs0 (ha₂ s₂ hs₂ hQs)
  have hq : Q s₂ ≠ 0 := by
    intro h
    rw [ha₂ s₂ hs₂ h, add_zero] at hQs hs0
    exact hs0 (ha₁ s₁ hs₁ hQs)
  by_cases hu0 : u = 0
  · rw [hu0]
    exact zero_mem _
  have hQu : Q u ≠ 0 := fun h => hu0 (ha₃ u hu h)
  obtain ⟨l, hl⟩ := isSquare_of_charTwo' (Q s₂ / Q u)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hl
    exact hl.elim hq hQu
  have hQβ : Q (l • u) = Q s₂ := by
    rw [QuadraticMap.map_smul, smul_eq_mul, ← hl, div_mul_cancel₀ _ hQu]
  have h := smul_mem_rootSet_sup hk h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hs₁ hs₂ hs₁0 hq hQs
    (U₃.smul_mem l hu) hQβ l⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hl0, one_smul] at h

omit [Finite k] in
private theorem eichler_mem_sup_of_mem_pair (hk : 2 < Nat.card k) {U₁ U₂ U₃ : Submodule k V}
    (h₁ : PolarNondegOn Q U₁) (h₂ : PolarNondegOn Q U₂) (h₃ : PolarNondegOn Q U₃)
    (ha₁ : ∀ u ∈ U₁, Q u = 0 → u = 0) (ha₂ : ∀ u ∈ U₂, Q u = 0 → u = 0)
    (ha₃ : ∀ u ∈ U₃, Q u = 0 → u = 0)
    (h₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) (h₁₃ : ∀ x ∈ U₁, ∀ y ∈ U₃, polar Q x y = 0)
    (h₂₃ : ∀ x ∈ U₂, ∀ y ∈ U₃, polar Q x y = 0) {s : V} (hs : s ∈ U₁ ⊔ U₂) (hs0 : s ≠ 0)
    (hQs : Q s = 0) {w : V} (hw : w ∈ U₁ ⊔ U₂ ⊔ U₃) (hsw : polar Q s w = 0) :
    eichler Q s w ∈ supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃) := by
  obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.mp hw
  have hsu : polar Q s u = 0 := polar_sup_left_eq_zero h₁₃ h₂₃ s hs u hu
  have hsa : polar Q s a = 0 := by rwa [polar_add_right, hsu, add_zero] at hsw
  have hA : a ∈ rootSet Q (supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃)) s :=
    ⟨hsa, Subgroup.mem_sup_left (eichler_mem_supportedDerived_of_two_lt hk
      (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup h₁ h₂ h₁₂) hs ha hQs hsa)⟩
  exact (mem_rootSet.mp (add_mem hA (mem_rootSet_of_mem_third hk h₁ h₂ h₃ ha₁ ha₂ ha₃ h₁₂ h₁₃
    h₂₃ hs hs0 hQs hu))).2

private theorem orthDerived_le_comap_extU (hk : 2 < Nat.card k) {U₁ U₂ U₃ : Submodule k V}
    (h₁ : PolarNondegOn Q U₁) (h₂ : PolarNondegOn Q U₂) (h₃ : PolarNondegOn Q U₃)
    (hd₁ : finrank k U₁ = 2) (hd₂ : finrank k U₂ = 2) (hd₃ : finrank k U₃ = 2)
    (ha₁ : ∀ u ∈ U₁, Q u = 0 → u = 0) (ha₂ : ∀ u ∈ U₂, Q u = 0 → u = 0)
    (ha₃ : ∀ u ∈ U₃, Q u = 0 → u = 0)
    (h₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) (h₁₃ : ∀ x ∈ U₁, ∀ y ∈ U₃, polar Q x y = 0)
    (h₂₃ : ∀ x ∈ U₂, ∀ y ∈ U₃, polar Q x y = 0) (hV : PolarNondegOn Q (U₁ ⊔ U₂ ⊔ U₃)) :
    orthDerived (Q.comp (U₁ ⊔ U₂ ⊔ U₃).subtype) ≤
      (supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃)).comap (OrthNS.extU hV) := by
  have hA := CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup h₁ h₂ h₁₂
  have hdA := finrank_sup_of_polar_eq_zero h₁ h₁₂
  have hdV := finrank_sup_of_polar_eq_zero hA (polar_sup_left_eq_zero h₁₃ h₂₃)
  have hR := CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hV
  rw [CFSG.LocalAnalysis.GLTheoremA.T173U.orthDerived_eq_elementaryGroup_of_three_le hR le_rfl
    (by omega)]
  have hroot : ∀ x : ↥(U₁ ⊔ U₂ ⊔ U₃), (x : V) ∈ U₁ ⊔ U₂ → Q x = 0 → (x : V) ≠ 0 →
      IsRootCenter (Q.comp (U₁ ⊔ U₂ ⊔ U₃).subtype) ((supportedDerived Q (U₁ ⊔ U₂) ⊔
        supportedDerived Q (U₂ ⊔ U₃)).comap (OrthNS.extU hV) ⊓
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U₁ ⊔ U₂ ⊔ U₃).subtype)) x := by
    intro x hx hQx hx0
    refine ⟨fun h => hx0 (by simp [h]), hQx, fun w hw =>
      Subgroup.mem_inf.mpr ⟨?_, eichler_mem_orthogonalGroup _ x w⟩⟩
    rw [Subgroup.mem_comap, OrthNS.extU_eichler]
    exact eichler_mem_sup_of_mem_pair hk h₁ h₂ h₃ ha₁ ha₂ ha₃ h₁₂ h₁₃ h₂₃ hx hx0 hQx w.2
      (by rwa [polar_comp_subtype_eq] at hw)
  obtain ⟨e, he, he0, hQe⟩ :=
    CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_any (Q := Q)
      (S := U₁ ⊔ U₂) (by omega)
  obtain ⟨f, hf, hQf, hef⟩ := exists_partner_of_polarNondegOn hA he he0 hQe
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hef
    exact zero_ne_one hef
  refine (elementaryGroup_le_of_hypPair hR inf_le_right
    ⟨⟨e, Submodule.mem_sup_left he⟩, ⟨f, Submodule.mem_sup_left hf⟩, hQe, hQf, ?_⟩
      ?_ ?_).trans inf_le_left
  · rw [polar_comp_subtype_eq]
    exact hef
  · exact hroot _ he hQe he0
  · exact hroot _ hf hQf hf0

theorem supportedDerived_sup_sup_sup_of_anisotropic (hk : 2 < Nat.card k)
    {U₁ U₂ U₃ : Submodule k V} (h₁ : PolarNondegOn Q U₁) (h₂ : PolarNondegOn Q U₂)
    (h₃ : PolarNondegOn Q U₃) (hd₁ : finrank k U₁ = 2) (hd₂ : finrank k U₂ = 2)
    (hd₃ : finrank k U₃ = 2) (ha₁ : ∀ u ∈ U₁, Q u = 0 → u = 0)
    (ha₂ : ∀ u ∈ U₂, Q u = 0 → u = 0) (ha₃ : ∀ u ∈ U₃, Q u = 0 → u = 0)
    (h₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0) (h₁₃ : ∀ x ∈ U₁, ∀ y ∈ U₃, polar Q x y = 0)
    (h₂₃ : ∀ x ∈ U₂, ∀ y ∈ U₃, polar Q x y = 0) :
    supportedDerived Q (U₁ ⊔ U₂) ⊔ supportedDerived Q (U₂ ⊔ U₃) =
      supportedDerived Q (U₁ ⊔ U₂ ⊔ U₃) := by
  have hA := CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup h₁ h₂ h₁₂
  have hB := CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup h₂ h₃ h₂₃
  have hV := CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hA h₃
    (polar_sup_left_eq_zero h₁₃ h₂₃)
  refine le_antisymm (sup_le ?_ ?_) fun g hg => ?_
  · exact supportedDerived_le_supportedDerived_of_le le_sup_left
      (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hA)
      (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hV)
  · exact supportedDerived_le_supportedDerived_of_le
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hB)
      (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hV)
  obtain ⟨hfix, h, hh, hagree⟩ := mem_supportedDerived.mp hg
  rw [← OrthNS.extU_eq_of_agree hV (a := h) (fun u => (hagree u).symm) fun r hr => hfix r hr]
  exact orthDerived_le_comap_extU hk h₁ h₂ h₃ hd₁ hd₂ hd₃ ha₁ ha₂ ha₃ h₁₂ h₁₃ h₂₃ hV hh

end Generation

section Model

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem finrank_coordPlane_refl (E : QuadExt F K (unitaryInvolution K 2 f))
    (n : ℕ) (i : Fin n) :
    Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) = 2 := by
  have hdim : Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) =
      Module.finrank F K := by
    let L : K →ₗ[F] (Fin n → K) := LinearMap.single F (fun _ => K) i
    have hL : Function.Injective L := by
      intro x y hxy
      have h := congrFun hxy i
      simpa [L] using h
    have hinj : Function.Injective
        ((LinearMap.inr F (F × F) (Fin n → K)).comp L) :=
      LinearMap.inr_injective.comp hL
    dsimp only [coordPlane]
    exact LinearMap.finrank_range_of_inj hinj
  rw [hdim, E.finrank_eq]

private theorem normHypForm_coordPlane_anisotropic (n : ℕ) (i : Fin n) :
    ∀ u ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i,
      normHypForm E n u = 0 → u = 0 := by
  intro u hu hQu
  obtain ⟨x, rfl⟩ := mem_coordPlane.mp hu
  change normHypForm E n (((0, 0), Pi.single i x) : (F × F) × (Fin n → K)) = 0 at hQu
  have hsum : (∑ j : Fin n, normQuad E ((Pi.single i x : Fin n → K) j)) = normQuad E x := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hQx : normQuad E x = 0 := by
    rw [normHypForm_apply_coord] at hQu
    simpa [hypPlane_apply, hsum] using hQu
  have hx : x = 0 := (normQuad_eq_zero_iff E).1 hQx
  subst hx
  simp

theorem normPureBlock_pair_sup_pair (hq : 2 < Nat.card F) {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    normPureBlock E n {i, j} ⊔ normPureBlock E n {j, k} = normPureBlock E n {i, j, k} := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  simp only [normPureBlock, Finset.sup_insert, Finset.sup_singleton]
  set ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)) with hψdef
  have hψ := normHypForm_apply_coord E n
  have hU : ∀ l, PolarNondegOn (normHypForm E n) (coordPlane ψ l) :=
    fun l => coordPlane_polarNondegOn ψ hψ (normQuad_polarBilin_nondegenerate E) l
  have horth : ∀ l m, l ≠ m → ∀ x ∈ coordPlane ψ l, ∀ y ∈ coordPlane ψ m,
      polar (normHypForm E n) x y = 0 :=
    fun l m hlm x hx y hy => polar_coordPlane_plane ψ hψ hlm hx hy
  have hle : ∀ {W : Submodule F ((F × F) × (Fin n → K))}, PolarNondegOn (normHypForm E n) W →
      supportedDerived (normHypForm E n) W ≤ normOmega E n := fun hW =>
    supportedDerived_le_orthDerived_of_regular
      (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hW)
  have hmain := supportedDerived_sup_sup_sup_of_anisotropic hq (hU i) (hU j) (hU k)
    (finrank_coordPlane_refl E n i) (finrank_coordPlane_refl E n j)
    (finrank_coordPlane_refl E n k) (normHypForm_coordPlane_anisotropic E n i)
    (normHypForm_coordPlane_anisotropic E n j) (normHypForm_coordPlane_anisotropic E n k)
    (horth i j hij) (horth i k hik) (horth j k hjk)
  rw [sup_assoc] at hmain
  rw [← Subgroup.subgroupOf_sup
    (hle (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup (hU i) (hU j) (horth i j hij)))
    (hle (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup (hU j) (hU k) (horth j k hjk))),
    hmain]

end Model

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
