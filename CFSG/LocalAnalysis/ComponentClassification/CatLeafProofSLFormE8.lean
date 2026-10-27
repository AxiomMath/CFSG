module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Inner
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8AllInvolutionComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

theorem e8_toral_D8_slForm
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    SLComponentForm K (toralCentralizer .E8 K (bitsTuple e8BitsD8)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _
      (bitsTuple_mem (K := K) e8BitsD8)
  obtain ⟨-, -, -, hqs, -⟩ := exists_psi_D8_E8 hp hp2 hK
  let e₁ : ↥(⨆ k, e8D8Chain K k) ≃*
      rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) :=
    ((⨆ k, e8D8Chain K k).equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_e8D8Chain hK2))
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  refine slComponentForm_of_eq_or_SL (B := (rootSpan .E8 K (rootCharKernel
    (bitsTuple (K := K) e8BitsD8))).subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsD8)))
    ?_ fun L hL => Or.inl (eq_of_isComponent_of_normal_quasisimple hq hsolv hL)
  rw [Nat.card_congr e₂.toEquiv]
  have hker : rootCharKernel (bitsTuple (K := K) e8BitsD8) =
      kernelRoots (maskChar (τ := .E8) e8BitsD8) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  have hmem : ∀ γ : Fin (Tag.rank .E8) → ℤ, IsRoot .E8 γ → γ (e8Node 0) = 0 →
      rootSubgroup .E8 K γ ≤ rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) := by
    intro γ hγ h0
    have hγS : γ ∈ rootCharKernel (bitsTuple (K := K) e8BitsD8) := by
      rw [hker, mem_kernelRoots_maskChar, maskPairing_e8BitsD8, h0]
      exact ⟨hγ, ⟨0, rfl⟩⟩
    exact le_biSup (f := fun γ => rootSubgroup .E8 K γ) hγS
  exact card_SL_dvd_of_rootPair_le hK2 (isRoot_single _ (e8Node 1))
    (sup_le (hmem _ (isRoot_single _ _) (by decide))
      (hmem _ (IsRoot.neg (isRoot_single _ _)) (by decide)))

theorem e8_toral_E7_slForm
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    SLComponentForm K (toralCentralizer .E8 K (bitsTuple e8BitsE7)) := by
  classical
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : Finite (ModGL .E8 K) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .E8 K e8LeviE7 with hH_def
  set Q := rootSubgroup .E8 K hiE8 ⊔ rootSubgroup .E8 K (-hiE8) with hQ_def
  have hS : rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7)) = H ⊔ Q := by
    rw [rootCharKernel_e8BitsE7 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : H ⊔ Q ≤ toralCentralizer .E8 K (bitsTuple e8BitsE7) := hS ▸ hSX
  have hHX : H ≤ toralCentralizer .E8 K (bitsTuple e8BitsE7) := le_sup_left.trans hSX'
  have hQX : Q ≤ toralCentralizer .E8 K (bitsTuple e8BitsE7) := le_sup_right.trans hSX'
  have hD : (rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7))).subgroupOf
        (toralCentralizer .E8 K (bitsTuple e8BitsE7)) =
      H.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7)) ⊔
        Q.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7)) := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hHX hQX
  obtain ⟨hqH, -⟩ := e8_levi_E7_recognition hp hp2 hK
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E8 K hK2 isRoot_hiE8
  have hQmap : (rootGroup (rootOperatorFamily .E8) K hiE8 ⊔
      rootGroup (rootOperatorFamily .E8) K (-hiE8)).map (adjointGroup .E8 K).subtype = Q := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_hiE8,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_hiE8)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup
      (e8E7Node k)) (rootGroup (rootOperatorFamily .E8) K hiE8 ⊔
        rootGroup (rootOperatorFamily .E8) K (-hiE8)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E8 (isRoot_single _ _) isRoot_hiE8
        (e8E7Node_ne_hiE8 k).1 (e8E7Node_ne_hiE8 k).2 (iform_e8E7Node_hiE8 k)
        (not_isRoot_e8E7Node_hiE8 k).1 (not_isRoot_e8E7Node_hiE8 k).2
  have hcomm : Commutes H Q := by
    rw [hH_def, show e8LeviE7 = Set.range e8E7Node from rfl,
      ← map_subtype_iSup_rankOne e8E7Node, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hq₁ : IsQuasisimple (H.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHX).symm hqH
  have hαβ : ∀ x ∈ H.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7)),
      ∀ y ∈ Q.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7)), x * y = y * x :=
    fun x hx y hy => Subtype.ext (hcomm x hx y hy)
  have hn₁ : ((H.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))).subgroupOf
      ((rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7))).subgroupOf
        (toralCentralizer .E8 K (bitsTuple e8BitsE7)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  refine slComponentForm_of_eq_or_SL
    (B := H.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))) ?_ fun M hM => ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv]
    exact card_SL_dvd_subsystemGroup hK2 (i := e8E7Node 0) ⟨0, rfl⟩
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  by_cases h5 : 5 ≤ Nat.card K
  · have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm (hfin.2 h5).1
    have hn₂ : ((Q.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))).subgroupOf
        ((rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7))).subgroupOf
          (toralCentralizer .E8 K (bitsTuple e8BitsE7)))).Normal := by
      rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
      refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (hαβ y hy x hx).symm)
    rcases eq_or_eq_of_isComponent_le_sup hD hq₁ hq₂ hn₁ hn₂ hM hMS with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(MulEquiv.subgroupCongr h).trans
        ((Subgroup.subgroupOfEquivOfLe hQX).trans eQ.symm)⟩
  · have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      omega
    have hs₂ : Group.IsSolvable (Q.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))) :=
      haveI := (hfin.1 h3').1
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hQX).injective
    exact Or.inl (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM hMS)

theorem oddExcInnerDiagSLForm_E8
    : OddExcInnerDiagSLForm .E8 := by
  refine oddExcInnerDiagSLForm_of_toral (Or.inr (Or.inr (Or.inr rfl)))
    (fun K _ _ hK α hα L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components
        .E8 (Or.inr (Or.inr rfl)) K hK α hα 2 Nat.prime_two L hL)
    (fun K _ _ p f hp hp2 hKp b hb hb1 => ?_)
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_slForm_of_orbitCheck hK2 e8SignOrbit_check (fun ρ hρ hne => ?_) hb hb1
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e8_toral_D8_slForm hp hp2 hKp
  ·
    have hmap := map_conj_toralCentralizer_of_maskAct (K := K) hK2 e8MaskWord e8BitsE7
    rw [maskAct_e8MaskWord] at hmap
    let e : toralCentralizer .E8 K (bitsTuple e8BitsE7) ≃*
        toralCentralizer .E8 K (bitsTuple (listMask (e8SignReps.getD 2 []))) :=
      ((toralCentralizer .E8 K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact slComponentForm_of_mulEquiv e.symm (e8_toral_E7_slForm hp hp2 hKp)

end CFSG.ComponentClassification.CatLeafProof
