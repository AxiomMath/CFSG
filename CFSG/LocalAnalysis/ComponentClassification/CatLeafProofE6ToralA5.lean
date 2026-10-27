module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Levi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralThree

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

@[expose] def e6BitsA5 : Fin (Tag.rank .E6) → Bool :=
  listMask [false, true, false, false, false, false]

theorem e6BitsA5_eq_false : ∀ j : Fin (Tag.rank .E6), j ≠ e6Node 1 → e6BitsA5 j = false := by
  decide

theorem maskPairing_e6BitsA5 (α : Fin (Tag.rank .E6) → ℤ) :
    maskPairing e6BitsA5 α = α (e6Node 1) := by
  rw [maskPairing, Finset.sum_eq_single (e6Node 1)]
  · simp [show e6BitsA5 (e6Node 1) = true from by decide]
  · intro j _ hj
    simp [e6BitsA5_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def hiE6 : Fin (Tag.rank .E6) → ℤ := ![1, 2, 2, 3, 2, 1]

theorem isRoot_hiE6 : IsRoot .E6 hiE6 := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
  decide +kernel

theorem e6_even_one_cases : ∀ α ∈ rootFinset .E6, Even (α (e6Node 1)) →
    α (e6Node 1) = 0 ∨ α = hiE6 ∨ α = -hiE6 := by
  decide +kernel

theorem e6A5Node_ne_one : ∀ k : Fin 5, e6A5Node k ≠ e6Node 1 := by decide

theorem eq_one_of_forall_e6A5Node_ne :
    ∀ i : Fin (Tag.rank .E6), (∀ k, e6A5Node k ≠ i) → i = e6Node 1 := by
  decide

theorem mem_parabolicRoots_e6LeviA5 {α : Fin (Tag.rank .E6) → ℤ} :
    α ∈ parabolicRoots .E6 e6LeviA5 ↔ IsRoot .E6 α ∧ α (e6Node 1) = 0 := by
  refine and_congr_right fun _ => ⟨fun h => h _ ?_, fun h i hi => ?_⟩
  · rintro ⟨k, hk⟩
    exact e6A5Node_ne_one k hk
  · rw [eq_one_of_forall_e6A5Node_ne i fun k hk => hi ⟨k, hk⟩]
    exact h

theorem rootCharKernel_e6BitsA5
    {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootCharKernel (bitsTuple (K := K) e6BitsA5) =
      parabolicRoots .E6 e6LeviA5 ∪ {hiE6, -hiE6} := by
  rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  ext α
  rw [mem_kernelRoots_maskChar, maskPairing_e6BitsA5, Set.mem_union, mem_parabolicRoots_e6LeviA5,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hev⟩
    rcases e6_even_one_cases α (mem_rootFinset.2 hα) hev with h | h | h
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨hα, h⟩ | rfl | rfl)
    · exact ⟨hα, by rw [h]; decide⟩
    · exact ⟨isRoot_hiE6, by decide⟩
    · exact ⟨IsRoot.neg isRoot_hiE6, by decide⟩

theorem e6A5Node_ne_hiE6 : ∀ k : Fin 5, (Pi.single (e6A5Node k) 1 : Fin (Tag.rank .E6) → ℤ) ≠
    hiE6 ∧ (Pi.single (e6A5Node k) 1 : Fin (Tag.rank .E6) → ℤ) ≠ -hiE6 := by
  decide

theorem iform_e6A5Node_hiE6 : ∀ k : Fin 5,
    iform (Pi.single (e6A5Node k) 1 : Fin (Tag.rank .E6) → ℤ) hiE6 = 0 := by
  decide +kernel

theorem not_isRoot_e6A5Node_hiE6 : ∀ k : Fin 5,
    ¬ IsRoot .E6 (Pi.single (e6A5Node k) 1 + hiE6) ∧
      ¬ IsRoot .E6 (Pi.single (e6A5Node k) 1 + -hiE6) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
  decide +kernel

theorem e6_toral_A5_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .E6 K (bitsTuple e6BitsA5))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .PSL 6 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  have : Finite (ModGL .E6 K) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .E6 K e6LeviA5 with hH_def
  set Q := rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6) with hQ_def
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5)) = H ⊔ Q := by
    rw [rootCharKernel_e6BitsA5 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : H ⊔ Q ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := hS ▸ hSX
  have hHX : H ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := le_sup_left.trans hSX'
  have hQX : Q ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := le_sup_right.trans hSX'
  have hD : (rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
        (toralCentralizer .E6 K (bitsTuple e6BitsA5)) =
      H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)) ⊔
        Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)) := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hHX hQX
  obtain ⟨hqH, hlieH⟩ := e6_levi_A5_recognition hp hp2 hK
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E6 K hK2 isRoot_hiE6
  have hQmap : (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
      rootGroup (rootOperatorFamily .E6) K (-hiE6)).map (adjointGroup .E6 K).subtype = Q := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_hiE6,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_hiE6)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup
      (e6A5Node k)) (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
        rootGroup (rootOperatorFamily .E6) K (-hiE6)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E6 (isRoot_single _ _) isRoot_hiE6
        (e6A5Node_ne_hiE6 k).1 (e6A5Node_ne_hiE6 k).2 (iform_e6A5Node_hiE6 k)
        (not_isRoot_e6A5Node_hiE6 k).1 (not_isRoot_e6A5Node_hiE6 k).2
  have hcomm : Commutes H Q := by
    rw [hH_def, show e6LeviA5 = Set.range e6A5Node from rfl,
      ← map_subtype_iSup_rankOne e6A5Node, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hq₁ : IsQuasisimple (H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHX).symm hqH
  have hαβ : ∀ x ∈ H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)),
      ∀ y ∈ Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)), x * y = y * x :=
    fun x hx y hy => Subtype.ext (hcomm x hx y hy)
  have hn₁ : ((H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))).subgroupOf
      ((rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
        (toralCentralizer .E6 K (bitsTuple e6BitsA5)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  have hH : M = H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)) →
      OddLieCentralQuotient p M := fun h => by
    let e : M ≃* H := (MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hHX)
    exact ⟨.PSL, 6, f, hadm, lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlieH⟩
  by_cases h5 : 5 ≤ Nat.card K
  · have hc2 : Nat.card K ≠ 2 := by omega
    have hc3 : Nat.card K ≠ 3 := by omega
    have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm (hfin.2 h5).1
    have hn₂ : ((Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))).subgroupOf
        ((rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
          (toralCentralizer .E6 K (bitsTuple e6BitsA5)))).Normal := by
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
    have hs₂ : Group.IsSolvable (Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
      haveI := (hfin.1 h3').1
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hQX).injective
    exact hH (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM hMS)

end CFSG.ComponentClassification.CatLeafProof
