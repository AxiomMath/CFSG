module

public import CFSG.ClassicalInvolution.Q3.Q3AMPspC01
public import CFSG.ClassicalInvolution.Q3.Q3AMBadFrame
public import CFSG.ClassicalInvolution.Q3.Q3T6DSComp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Q3.Q3T6D CFSG.ClassicalInvolution.Asc77

section Plain

variable {G : Type} [Group G]

theorem closure_triple_perm (z₁ z₂ s : G) :
    Subgroup.closure ({z₁, z₂, s} : Set G) = Subgroup.closure ({z₂, s, z₁} : Set G) := by
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem closure_triple_swap (a b c : G) :
    Subgroup.closure ({a, b, c} : Set G) = Subgroup.closure ({a, c, b} : Set G) := by
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem closure_triple_mul {z : G} (t s : G) (hz : z * z = 1) :
    Subgroup.closure ({z, s, z * t} : Set G) = Subgroup.closure ({z, t, s} : Set G) := by
  have hz1 : z ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have ht1 : t ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hs1 : s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hz2 : z ∈ Subgroup.closure ({z, s, z * t} : Set G) := Subgroup.subset_closure (by simp)
  have hs2 : s ∈ Subgroup.closure ({z, s, z * t} : Set G) := Subgroup.subset_closure (by simp)
  have hzt2 : z * t ∈ Subgroup.closure ({z, s, z * t} : Set G) :=
    Subgroup.subset_closure (by simp)
  have ht2 : t ∈ Subgroup.closure ({z, s, z * t} : Set G) := by
    have e : z * (z * t) = t := by rw [← mul_assoc, hz, one_mul]
    have := Subgroup.mul_mem _ hz2 hzt2
    rwa [e] at this
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hz1
    · exact hs1
    · exact Subgroup.mul_mem _ hz1 ht1
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hz2
    · exact ht2
    · exact hs2

theorem closure_triple_eq_insert (z₁ z₂ s : G) :
    Subgroup.closure ({z₁, z₂, s} : Set G) = Subgroup.closure (insert s ({z₁, z₂} : Set G)) := by
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

variable [Finite G]

theorem isSolvablePsp_of_isClassicalMember3 {K : Subgroup G} {z : G}
    (h : IsClassicalMember3 K z) : Group.IsSolvable ↥K := by
  have hq := Q3T6.isSolvable_oddCoreQuotient_of_isClassicalMember3 h
  have ho : Group.IsSolvable ↥(classicalInvolutionOddCore ↥K) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card ↥K)
  exact Group.isSolvable_of_ker_le_range (classicalInvolutionOddCore ↥K).subtype
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem commutator_component_modOddPsp {K : Subgroup G} {z : G} (hK : IsClassicalMember3 K z)
    {L : Subgroup (OddQuot z)} (hL : CFSG.IsComponent L) : ⁅L, modOdd z K⁆ = ⊥ := by
  have hsubC : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := hK.subnormal
  have hMC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hsubC
  have hsolv : Group.IsSolvable ↥(modOdd z K) :=
    isSolvable_modOdd3 hMC (isSolvablePsp_of_isClassicalMember3 hK)
  rcases CFSG.LocalCores.component_subnormal_subgroup hL (isSubnormal_modOdd3 hsubC) with h | h
  · exfalso
    have : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect ↥L := hL.1.1
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance
  · exact h

theorem oddQuotMk_commute_of_memPsp {K : Subgroup G} {z k : G} (hK : IsClassicalMember3 K z)
    (hkK : k ∈ K) (hkC : k ∈ Subgroup.centralizer ({z} : Set G)) {L : Subgroup (OddQuot z)}
    (hL : CFSG.IsComponent L) :
    ∀ x ∈ L, oddQuotMk z ⟨k, hkC⟩ * x = x * oddQuotMk z ⟨k, hkC⟩ := fun _ hx =>
  Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_component_modOddPsp hK hL) hx)
    _ (oddQuotMk_mem_modOdd hkK hkC)

end Plain

section Main


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G}

theorem hyp51At_vertex_of_edges (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : CIT3Below (Nat.card G)) {V M M' B : Subgroup G} {c a a' tV tM tM' s : G}
    (eM : EdgeSetup K z V M c a) (eM' : EdgeSetup K z V M' c a') (hc2 : c * c = 1)
    (hca : c * a = a * c) (hca' : c * a' = a' * c) (haa' : a * a' = c) (hac : a ≠ c)
    (htV : tV ∈ V) (htM : tM ∈ M) (htM' : tM' ∈ M') (hctM : c * tM = tM * c)
    (hctM' : c * tM' = tM' * c) (hs : s = tV * (tM * tM')) (hB : IsElemAbelian 2 B)
    (hBgen : B = Subgroup.closure ({a, s, c} : Set G)) : Hyp51At B c := by
  have hcV : c ∈ V := eM.uniqueM.mem
  have hc1 : c ≠ 1 := eM.uniqueM.ne_one
  have hcC₁ : c ∈ V ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hcV, Subgroup.mem_centralizer_singleton_iff.mpr hca⟩
  have hcC₂ : c ∈ V ⊓ Subgroup.centralizer ({a'} : Set G) :=
    ⟨hcV, Subgroup.mem_centralizer_singleton_iff.mpr hca'⟩
  have htq₁ : c ∈ trivialOnQuot M := mem_trivialOnQuot_iff.mpr
    ⟨mem_normalizer_iff_conjSub_eq.mpr (eM.conjSub_eq_of_mem_centM hnab hBelow c hcC₁),
      fun l hl => eM.commutator_centM_le_oddCore hnab hBelow c hcC₁ l hl⟩
  have htq₂ : c ∈ trivialOnQuot M' := mem_trivialOnQuot_iff.mpr
    ⟨mem_normalizer_iff_conjSub_eq.mpr (eM'.conjSub_eq_of_mem_centM hnab hBelow c hcC₂),
      fun l hl => eM'.commutator_centM_le_oddCore hnab hBelow c hcC₂ l hl⟩
  have hcp : IsPGroup 2 (Subgroup.zpowers c) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have h₁ := isSectionMember3_exactCore3 eM.invN hcp htq₁
  have h₂ := isSectionMember3_exactCore3 eM'.invN hcp htq₂
  have hΦ := secData3_sFamily3 h₁ h₂ h₂
  have hnc := Balance.not_subset_center_of_ne_one hnab hc1
  have htM₀ : tM ∈ exactCore3 c M :=
    ⟨htM, Subgroup.mem_centralizer_singleton_iff.mpr hctM.symm⟩
  have htM₀' : tM' ∈ exactCore3 c M' :=
    ⟨htM', Subgroup.mem_centralizer_singleton_iff.mpr hctM'.symm⟩
  have htVC : tV ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (isUniqueInvolution_comm eM.uniqueM htV)
  exact hyp51At_of_pair_layers (c := c) (b := a) (b' := a') (d := s) (k := tV) (y := tM * tM')
    (M := exactCore3 c M) (M' := exactCore3 c M') (B := B) hBelow hΦ hnc
    (mem_sFamily3_one c _ _ _) (mem_sFamily3_two c _ _ _) h₁ h₂ haa' hB
    (hBgen ▸ Subgroup.subset_closure (by simp)) (hBgen ▸ Subgroup.subset_closure (by simp))
    (hBgen ▸ Subgroup.subset_closure (by simp)) hBgen hc1 hac hs
    (Subgroup.mul_mem_sup htM₀ htM₀') htVC
    (fun L hL x hx => oddQuotMk_commute_of_memPsp eM.invM htV htVC hL x hx)

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
