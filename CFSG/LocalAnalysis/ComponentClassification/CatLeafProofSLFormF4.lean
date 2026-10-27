module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8AllInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4SignOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralThree

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)
open scoped MatrixGroups

theorem f4_toral_C3_slForm
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    SLComponentForm K (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .F4 K f4LeviC3 with hH_def
  set Q := rootSubgroup .F4 K hiF4 ⊔ rootSubgroup .F4 K (-hiF4) with hQ_def
  have hS : rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3)) = H ⊔ Q := by
    rw [rootCharKernel_f4BitsC3 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : H ⊔ Q ≤ (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := hS ▸ hSX
  have hHX : H ≤ (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := le_sup_left.trans hSX'
  have hQX : Q ≤ (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := le_sup_right.trans hSX'
  have hD : (rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)) =
      H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)) ⊔
        Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hHX hQX
  obtain ⟨-, -, -, hqH, -⟩ := f4_levi_C3_recognition_frame hp hp2 hK h2
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .F4 K hK2 isRoot_hiF4
  have hQmap : (rankOneHiF4 K).map (adjointGroup .F4 K).subtype = Q := by
    rw [rankOneHiF4, Subgroup.map_sup]
    simp only
    rw [map_subtype_rootGroup _ isRoot_hiF4, map_subtype_rootGroup _ (IsRoot.neg isRoot_hiF4)]
  have hcomm' : Commutes (⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)) (rankOneHiF4 K) :=
    commutes_iSup_left.2 fun k => (commutes_rankOneHiF4 (c3Node_val_ne_zero k)).symm
  have hcomm : Commutes H Q := by
    rw [hH_def, ← map_subtype_iSup_c3, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hq₁ : IsQuasisimple (H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHX).symm hqH
  have hn₁ : ((H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))).subgroupOf
      ((rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subtype.ext (hcomm x.1 hx y.1 hy))
  refine slComponentForm_of_eq_or_SL
    (B := H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) ?_ fun M hM => ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv]
    exact card_SL_dvd_subsystemGroup hK2 (i := c3Node 0) ⟨0, rfl⟩
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  by_cases h5 : 5 ≤ Nat.card K
  · have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm (hfin.2 h5).1
    have hn₂ : ((Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))).subgroupOf
        ((rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
          (toralCentralizer .F4 K (bitsTuple f4BitsC3)))).Normal := by
      rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
      refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subtype.ext (hcomm y.1 hy x.1 hx).symm)
    rcases eq_or_eq_of_isComponent_le_sup hD hq₁ hq₂ hn₁ hn₂ hM hMS with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(MulEquiv.subgroupCongr h).trans
        ((Subgroup.subgroupOfEquivOfLe hQX).trans eQ.symm)⟩
  · have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      have := (one_le_and_three_le_of_card hp hp2 hK).2
      omega
    have hs₂ : Group.IsSolvable (Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) :=
      haveI := (hfin.1 h3').1
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hQX).injective
    exact Or.inl (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM hMS)

theorem f4_toral_B4_slForm
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    SLComponentForm K (toralCentralizer .F4 K (bitsTuple f4BitsB4)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _
      (bitsTuple_mem (K := K) f4BitsB4)
  have hker : rootCharKernel (bitsTuple (K := K) f4BitsB4) =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  obtain ⟨-, -, -, hqs, -⟩ := exists_psi_B4_F4_frame hp hp2 hK h2
  have hSim : (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    rw [map_subtype_iSup_b4Chain, hker]
  let e₁ : ↥(⨆ k, b4Chain K k) ≃* rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) :=
    ((⨆ k, b4Chain K k).equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hSim)
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  refine slComponentForm_of_eq_or_SL (B := (rootSpan .F4 K (rootCharKernel
    (bitsTuple (K := K) f4BitsB4))).subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsB4)))
    ?_ fun L hL => Or.inl (eq_of_isComponent_of_normal_quasisimple hq hsolv hL)
  rw [Nat.card_congr e₂.toEquiv]
  have hmem : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ (f4Node 3) = 0 →
      rootSubgroup .F4 K γ ≤ rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    intro γ hγ h3
    have hγS : γ ∈ rootCharKernel (bitsTuple (K := K) f4BitsB4) := by
      rw [hker, mem_kernelRoots_maskChar, maskPairing_f4BitsB4, h3]
      exact ⟨hγ, ⟨0, rfl⟩⟩
    exact le_biSup (f := fun γ => rootSubgroup .F4 K γ) hγS
  exact card_SL_dvd_of_rootPair_le hK2 (isRoot_single _ (f4Node 0))
    (sup_le (hmem _ (isRoot_single _ _) (by decide))
      (hmem _ (IsRoot.neg (isRoot_single _ _)) (by decide)))

theorem oddExcInnerDiagSLForm_F4
    : OddExcInnerDiagSLForm .F4 := by
  refine oddExcInnerDiagSLForm_of_toral (Or.inr (Or.inl rfl))
    (fun K _ _ hK α hα L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components
        .F4 (Or.inr (Or.inl rfl)) K hK α hα 2 Nat.prime_two L hL)
    (fun K _ _ p f hp hp2 hKp b hb hb1 => ?_)
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_slForm_of_orbitCheck hK2 f4SignOrbitB4_check (fun ρ hρ hne => ?_) hb
    hb1
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact f4_toral_C3_slForm hp hp2 hKp
  · exact f4_toral_B4_slForm hp hp2 hKp

end CFSG.ComponentClassification.CatLeafProof
