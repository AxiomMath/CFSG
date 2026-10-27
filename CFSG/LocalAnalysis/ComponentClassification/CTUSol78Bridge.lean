module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Cited
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS
open scoped IsMulCommutative

private theorem pPrimeCore_map_le_of_isPComponent {G : Type*} [Group G] [Finite G]
    {L C : Subgroup G} (hLC : L ≤ C) (hL : IsPComponent 2 (L.subgroupOf C)) :
    (pPrimeCore 2 ↥L).map L.subtype ≤ (pPrimeCore 2 ↥C).map C.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, -, hsub, -, -⟩ := hL
  have h := pPrimeCoreOf_le_of_subnormal 2 hsub
  have hid : (pPrimeCore 2 ↥L).map L.subtype =
      (pPrimeCoreOf 2 (L.subgroupOf C)).map C.subtype := by
    let e : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
    unfold pPrimeCoreOf
    rw [Subgroup.map_map, ← pPrimeCore_map_iso 2 e, Subgroup.map_map]
    rfl
  rw [hid]
  exact Subgroup.map_mono h

private theorem not_le_pPrimeCore_map_of_isPComponent {G : Type*} [Group G] [Finite G]
    {M C : Subgroup G} (hM : IsPComponent 2 (M.subgroupOf C)) :
    ¬ M ≤ (pPrimeCore 2 ↥C).map C.subtype := by
  intro hle
  obtain ⟨K, hK, -, hmap, -⟩ := hM
  have hle' : M.subgroupOf C ≤ pPrimeCore 2 ↥C := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hle (mem_subgroupOf.mp hx)
    rwa [Subtype.ext hyx] at hy
  have hbot : (M.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hle' hx)
  rw [hmap] at hbot
  have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this hbot

private theorem le_normalizer_map_subtype_of_normal' {G : Type*} [Group G] (K : Subgroup G)
    (N : Subgroup K) [N.Normal] : K ≤ normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := N) K.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

theorem balanceTwoComponentInput_of_solomonCommutingCore (h : GrSLit.SolomonCommutingCoreInput) :
    BalanceTwoComponentInput := by
  intro G _ _ S T hS hT hSe hTe hST
  have hcomm : ∀ A : Subgroup G, IsElementaryAbelian 2 A → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro A hA x hx y hy
    have := hA
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hsq : ∀ A : Subgroup G, IsElementaryAbelian 2 A → ∀ x ∈ A, x * x = 1 := by
    intro A hA x hx
    have := hA
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hST' : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    ((mem_centralizer_iff.mp (hST hx)) y hy).symm
  have hh := h G S T hS hT (hcomm S hSe) (hsq S hSe) (hcomm T hTe) (hsq T hTe) hST'
  dsimp only at hh
  dsimp only [pPrimeCoreOf, pPrimePCore, IsPCompIn]
  obtain ⟨⟨h1, -⟩, h2, h4⟩ := hh
  refine ⟨h1, fun L hL => ?_, fun hnot => ?_⟩
  · obtain ⟨hLC, hLp⟩ := hL
    obtain ⟨hDN, hc⟩ := h2 L hLC hLp
    have hOL := pPrimeCore_map_le_of_isPComponent hLC hLp
    refine ⟨le_trans (le_inf (inf_le_right.trans (le_normalizer_map_subtype_of_normal' _ _)) hDN)
      (inf_normalizer_le_normalizer_sup _ _), fun hn => ?_⟩
    obtain ⟨hSL, hL1, hL2⟩ := hc fun h' => hn (h'.trans hOL)
    refine ⟨hSL, ?_, ?_⟩
    · conv_lhs => rw [← hL1]
      rw [← sup_assoc, sup_eq_left.mpr hOL]
    · conv_lhs => rw [← hL2]
      rw [← sup_assoc, sup_eq_left.mpr hOL]
  · obtain ⟨M, hMC, hMp, hMn⟩ := h4 hnot
    refine ⟨M, ⟨hMC, hMp⟩, fun hle => ?_⟩
    obtain ⟨-, hc⟩ := h2 M hMC hMp
    obtain ⟨-, hM1, -⟩ := hc hMn
    have hMO : M ≤ (pPrimeCore 2 ↥(centralizer (T : Set G))).map
        (centralizer (T : Set G)).subtype := by
      rw [← hM1]
      exact sup_le (pPrimeCore_map_le_of_isPComponent hMC hMp) hle
    exact not_le_pPrimeCore_map_of_isPComponent hMp hMO

theorem balanceTwoComponentInput_holds : BalanceTwoComponentInput :=
  balanceTwoComponentInput_of_solomonCommutingCore GrSLit.solomonCommutingCoreInput

end CFSG.ComponentClassification.Sol78
