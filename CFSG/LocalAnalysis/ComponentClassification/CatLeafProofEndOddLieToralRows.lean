module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieToral
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

theorem eq_or_SL_of_two_factors {K : Type} [Field K] {A : Type} [Group A]
    {X H Q S : Subgroup A} [Finite X] (hS : S = H ⊔ Q) (hSX : S ≤ X) [(S.subgroupOf X).Normal]
    (hsolv : Group.IsSolvable (X ⧸ S.subgroupOf X)) (hcomm : ∀ x ∈ H, ∀ y ∈ Q, x * y = y * x)
    (hqH : IsQuasisimple H) (eQ : SL(2, K) ≃* Q) (hQ : IsQuasisimple Q ∨ Group.IsSolvable Q)
    {M : Subgroup X} (hM : IsComponent M) : M = H.subgroupOf X ∨ Nonempty (M ≃* SL(2, K)) := by
  have hHX : H ≤ X := (le_sup_left.trans hS.symm.le).trans hSX
  have hQX : Q ≤ X := (le_sup_right.trans hS.symm.le).trans hSX
  have hD : S.subgroupOf X = H.subgroupOf X ⊔ Q.subgroupOf X := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hHX hQX
  have hq₁ : IsQuasisimple (H.subgroupOf X) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHX).symm hqH
  have hαβ : ∀ x ∈ H.subgroupOf X, ∀ y ∈ Q.subgroupOf X, x * y = y * x :=
    fun x hx y hy => Subtype.ext (hcomm x hx y hy)
  have hn₁ : ((H.subgroupOf X).subgroupOf (S.subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  rcases hQ with hq₂ | hs₂
  · have hq₂' : IsQuasisimple (Q.subgroupOf X) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm hq₂
    have hn₂ : ((Q.subgroupOf X).subgroupOf (S.subgroupOf X)).Normal := by
      rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
      refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (hαβ y hy x hx).symm)
    rcases eq_or_eq_of_isComponent_le_sup hD hq₁ hq₂' hn₁ hn₂ hM hMS with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(MulEquiv.subgroupCongr h).trans
        ((Subgroup.subgroupOfEquivOfLe hQX).trans eQ.symm)⟩
  · have hs₂' : Group.IsSolvable (Q.subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hQX).injective
    exact Or.inl (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂' hn₁ hM hMS)

theorem rootPair_quasisimple_or_solvable
    {τ : Tag} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hK2 : ringChar K ≠ 2) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    IsQuasisimple (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) : Subgroup (ModGL τ K)) ∨
      Group.IsSolvable (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) : Subgroup (ModGL τ K)) := by
  obtain ⟨-, -, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK2 hβ
  by_cases h5 : 5 ≤ Nat.card K
  · exact Or.inl (hfin.2 h5).1
  · have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      have := (one_le_and_three_le_of_card hp hp2 hK).2
      omega
    exact Or.inr (hfin.1 h3').1

theorem f4_toral_C3_quat
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    QuatComponentForm (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := by
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
  obtain ⟨-, -, -, hqH, -⟩ := f4_levi_C3_recognition_frame hp hp2 hK h2
  obtain ⟨-, ⟨eQ⟩, -, -⟩ := odd_arbitrary_root_pair_SL2_p_components .F4 K hK2 isRoot_hiF4
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
  have hHX : H ≤ toralCentralizer .F4 K (bitsTuple f4BitsC3) :=
    (le_sup_left.trans hS.symm.le).trans hSX
  intro M hM
  rcases eq_or_SL_of_two_factors hS hSX hsolv hcomm hqH eQ
      (rootPair_quasisimple_or_solvable hp hp2 hK hK2 isRoot_hiF4) hM with h | he
  · subst h
    exact exists_quaternion_of_rootPair_le hK2 (isRoot_single _ _) hHX
      (rootPair_le_subsystemGroup (i := c3Node 0) ⟨0, rfl⟩)
  · obtain ⟨e⟩ := he
    exact exists_quaternion_of_mulEquiv_SL hK2 e

theorem f4_toral_B4_quat
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    QuatComponentForm (toralCentralizer .F4 K (bitsTuple f4BitsB4)) := by
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
  have hmem : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ (f4Node 3) = 0 →
      rootSubgroup .F4 K γ ≤ rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    intro γ hγ h3
    have hγS : γ ∈ rootCharKernel (bitsTuple (K := K) f4BitsB4) := by
      rw [hker, mem_kernelRoots_maskChar, maskPairing_f4BitsB4, h3]
      exact ⟨hγ, ⟨0, rfl⟩⟩
    exact le_biSup (f := fun γ => rootSubgroup .F4 K γ) hγS
  intro M hM
  obtain rfl := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  exact exists_quaternion_of_rootPair_le hK2 (isRoot_single _ (f4Node 0)) hSX
    (sup_le (hmem _ (isRoot_single _ _) (by decide))
      (hmem _ (IsRoot.neg (isRoot_single _ _)) (by decide)))

theorem oddExcInnerDiagQuatForm_G2
    : OddExcInnerDiagQuatForm .G2 := by
  refine oddExcInnerDiagQuatForm_of_toral (Or.inl rfl) fun K _ _ p f hp hp2 hKp b hb hb1 => ?_
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact g2_toral_quat hKodd hK2 b hb hb1

theorem oddExcInnerDiagQuatForm_F4
    : OddExcInnerDiagQuatForm .F4 := by
  refine oddExcInnerDiagQuatForm_of_toral (Or.inr (Or.inl rfl))
    fun K _ _ p f hp hp2 hKp b hb hb1 => ?_
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_quat_of_orbitCheck hK2 f4SignOrbitB4_check (fun ρ hρ hne => ?_) hb hb1
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact f4_toral_C3_quat hp hp2 hKp
  · exact f4_toral_B4_quat hp hp2 hKp

end CFSG.ComponentClassification.CatLeafProof
