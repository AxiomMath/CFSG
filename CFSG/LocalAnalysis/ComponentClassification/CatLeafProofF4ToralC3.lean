module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4C3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)
open scoped MatrixGroups

@[expose] def f4BitsC3 : Fin (Tag.rank .F4) → Bool := listMask [true, false, false, false]

theorem f4_even_first_cases : ∀ α ∈ rootFinset .F4, Even (α (f4Node 0)) →
    α (f4Node 0) = 0 ∨ α = hiF4 ∨ α = -hiF4 := by
  decide +kernel

theorem f4BitsC3_eq_false : ∀ j : Fin (Tag.rank .F4), j ≠ f4Node 0 → f4BitsC3 j = false := by
  decide

theorem maskPairing_f4BitsC3 (α : Fin (Tag.rank .F4) → ℤ) :
    maskPairing f4BitsC3 α = α (f4Node 0) := by
  rw [maskPairing, Finset.sum_eq_single (f4Node 0)]
  · simp [show f4BitsC3 (f4Node 0) = true from by decide]
  · intro j _ hj
    simp [f4BitsC3_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem c3Node_ne_zero : ∀ k : Fin 3, c3Node k ≠ f4Node 0 := by decide

theorem c3Node_val_ne_zero : ∀ k : Fin 3, (c3Node k).val ≠ 0 := by decide

theorem eq_zero_of_forall_c3Node_ne :
    ∀ i : Fin (Tag.rank .F4), (∀ k, c3Node k ≠ i) → i = f4Node 0 := by
  decide

theorem mem_parabolicRoots_f4LeviC3 {α : Fin (Tag.rank .F4) → ℤ} :
    α ∈ parabolicRoots .F4 f4LeviC3 ↔ IsRoot .F4 α ∧ α (f4Node 0) = 0 := by
  refine and_congr_right fun _ => ⟨fun h => h _ ?_, fun h i hi => ?_⟩
  · rintro ⟨k, hk⟩
    exact c3Node_ne_zero k hk
  · rw [eq_zero_of_forall_c3Node_ne i fun k hk => hi ⟨k, hk⟩]
    exact h

theorem rootCharKernel_f4BitsC3
    {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootCharKernel (bitsTuple (K := K) f4BitsC3) =
      parabolicRoots .F4 f4LeviC3 ∪ {hiF4, -hiF4} := by
  rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  ext α
  rw [mem_kernelRoots_maskChar, maskPairing_f4BitsC3, Set.mem_union, mem_parabolicRoots_f4LeviC3,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hev⟩
    rcases f4_even_first_cases α (mem_rootFinset.2 hα) hev with h | h | h
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨hα, h⟩ | rfl | rfl)
    · exact ⟨hα, by rw [h]; decide⟩
    · exact ⟨isRoot_hiF4, by decide⟩
    · exact ⟨IsRoot.neg isRoot_hiF4, by decide⟩

theorem rootSpan_union_pair
    {τ : Tag} {K : Type} [Field K] (S : Set (Fin τ.rank → ℤ)) (γ : Fin τ.rank → ℤ) :
    rootSpan τ K (S ∪ {γ, -γ}) =
      rootSpan τ K S ⊔ (rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)) := by
  rw [rootSpan, rootSpan, iSup_union, iSup_insert, iSup_singleton]

theorem f4_toral_C3_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsC3))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hq4 : 4 ≤ Nat.card K := by omega
  have hc2 : Nat.card K ≠ 2 := by omega
  have hc3 : Nat.card K ≠ 3 := by omega
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  have : Finite (ModGL .F4 K) := finite_modGL
  have ha : ∀ i, bitsTuple (K := K) f4BitsC3 i = 1 ∨ bitsTuple (K := K) f4BitsC3 i = -1 :=
    bitsTuple_mem _
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _ ha
  set H := subsystemGroup .F4 K f4LeviC3 with hH_def
  set Q := rootSubgroup .F4 K hiF4 ⊔ rootSubgroup .F4 K (-hiF4) with hQ_def
  have hS : rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3)) = H ⊔ Q := by
    rw [rootCharKernel_f4BitsC3 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : H ⊔ Q ≤ toralCentralizer .F4 K (bitsTuple f4BitsC3) := hS ▸ hSX
  have hHX : H ≤ toralCentralizer .F4 K (bitsTuple f4BitsC3) := le_sup_left.trans hSX'
  have hQX : Q ≤ toralCentralizer .F4 K (bitsTuple f4BitsC3) := le_sup_right.trans hSX'
  have hD : (rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)) =
      H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)) ⊔
        Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hHX hQX
  obtain ⟨-, -, -, hqH, hlieH⟩ := f4_levi_C3_recognition hp hp2 hK hq4 h2
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .F4 K hK2 isRoot_hiF4
  have hqQ : IsQuasisimple Q := (hfin.2 h5).1
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
  have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm hqQ
  have hαβ : ∀ x ∈ H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)),
      ∀ y ∈ Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)), x * y = y * x :=
    fun x hx y hy => Subtype.ext (hcomm x hx y hy)
  have hn₁ : ((H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))).subgroupOf
      ((rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hn₂ : ((Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))).subgroupOf
      ((rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hαβ y hy x hx).symm)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  rcases eq_or_eq_of_isComponent_le_sup hD hq₁ hq₂ hn₁ hn₂ hM hMS with h | h
  · let e : M ≃* H := (MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hHX)
    exact ⟨.PSp, 3, f, hadm, lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlieH⟩
  · let e : M ≃* SL2 K :=
      ((MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hQX)).trans eQ.symm
    exact oddLieCentralQuotient_of_equiv_psl_two hp hf hK hc2 hc3
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

end CFSG.ComponentClassification.CatLeafProof
