module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Levi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralThree

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

@[expose] def e8BitsE7 : Fin (Tag.rank .E8) → Bool :=
  listMask [false, false, false, false, false, false, false, true]

theorem e8BitsE7_eq_false : ∀ j : Fin (Tag.rank .E8), j ≠ e8Node 7 → e8BitsE7 j = false := by
  decide

theorem maskPairing_e8BitsE7 (α : Fin (Tag.rank .E8) → ℤ) :
    maskPairing e8BitsE7 α = α (e8Node 7) := by
  rw [maskPairing, Finset.sum_eq_single (e8Node 7)]
  · simp [show e8BitsE7 (e8Node 7) = true from by decide]
  · intro j _ hj
    simp [e8BitsE7_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def hiE8 : Fin (Tag.rank .E8) → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem isRoot_hiE8 : IsRoot .E8 hiE8 := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  decide +kernel

theorem e8_even_seven_cases : ∀ α ∈ rootFinset .E8, Even (α (e8Node 7)) →
    α (e8Node 7) = 0 ∨ α = hiE8 ∨ α = -hiE8 := by
  decide +kernel

theorem e8E7Node_ne_seven : ∀ k : Fin 7, e8E7Node k ≠ e8Node 7 := by decide

theorem eq_seven_of_forall_e8E7Node_ne :
    ∀ i : Fin (Tag.rank .E8), (∀ k, e8E7Node k ≠ i) → i = e8Node 7 := by
  decide

theorem mem_parabolicRoots_e8LeviE7 {α : Fin (Tag.rank .E8) → ℤ} :
    α ∈ parabolicRoots .E8 e8LeviE7 ↔ IsRoot .E8 α ∧ α (e8Node 7) = 0 := by
  refine and_congr_right fun _ => ⟨fun h => h _ ?_, fun h i hi => ?_⟩
  · rintro ⟨k, hk⟩
    exact e8E7Node_ne_seven k hk
  · rw [eq_seven_of_forall_e8E7Node_ne i fun k hk => hi ⟨k, hk⟩]
    exact h

theorem rootCharKernel_e8BitsE7
    {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootCharKernel (bitsTuple (K := K) e8BitsE7) =
      parabolicRoots .E8 e8LeviE7 ∪ {hiE8, -hiE8} := by
  rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  ext α
  rw [mem_kernelRoots_maskChar, maskPairing_e8BitsE7, Set.mem_union, mem_parabolicRoots_e8LeviE7,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hev⟩
    rcases e8_even_seven_cases α (mem_rootFinset.2 hα) hev with h | h | h
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨hα, h⟩ | rfl | rfl)
    · exact ⟨hα, by rw [h]; decide⟩
    · exact ⟨isRoot_hiE8, by decide⟩
    · exact ⟨IsRoot.neg isRoot_hiE8, by decide⟩

theorem e8E7Node_ne_hiE8 : ∀ k : Fin 7, (Pi.single (e8E7Node k) 1 : Fin (Tag.rank .E8) → ℤ) ≠
    hiE8 ∧ (Pi.single (e8E7Node k) 1 : Fin (Tag.rank .E8) → ℤ) ≠ -hiE8 := by
  decide

theorem iform_e8E7Node_hiE8 : ∀ k : Fin 7,
    iform (Pi.single (e8E7Node k) 1 : Fin (Tag.rank .E8) → ℤ) hiE8 = 0 := by
  decide +kernel

theorem not_isRoot_e8E7Node_hiE8 : ∀ k : Fin 7,
    ¬ IsRoot .E8 (Pi.single (e8E7Node k) 1 + hiE8) ∧
      ¬ IsRoot .E8 (Pi.single (e8E7Node k) 1 + -hiE8) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  decide +kernel

theorem e8_toral_E7_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .E8 K (bitsTuple e8BitsE7))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
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
  obtain ⟨hqH, hlieH⟩ := e8_levi_E7_recognition hp hp2 hK
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
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  have hH : M = H.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7)) →
      OddLieCentralQuotient p M := fun h => by
    let e : M ≃* H := (MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hHX)
    exact ⟨.E7, 0, f, hadm, lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlieH⟩
  by_cases h5 : 5 ≤ Nat.card K
  · have hc2 : Nat.card K ≠ 2 := by omega
    have hc3 : Nat.card K ≠ 3 := by omega
    have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm (hfin.2 h5).1
    have hn₂ : ((Q.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))).subgroupOf
        ((rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7))).subgroupOf
          (toralCentralizer .E8 K (bitsTuple e8BitsE7)))).Normal := by
      rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
      refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (hαβ y hy x hx).symm)
    rcases eq_or_eq_of_isComponent_le_sup hD hq₁ hq₂ hn₁ hn₂ hM hMS with h | h
    · exact hH h
    · let e : M ≃* SL2 K :=
        ((MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hQX)).trans eQ.symm
      exact oddLieCentralQuotient_of_equiv_psl_two hp hf hK hc2 hc3
        (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
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
    exact hH (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM hMS)

end CFSG.ComponentClassification.CatLeafProof
