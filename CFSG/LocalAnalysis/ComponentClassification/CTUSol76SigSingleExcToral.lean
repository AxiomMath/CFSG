module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleExcTools

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Sol76.Sig (NonSLComponentUnique OddExcInnerDiagNonSLUnique
  nonSLComponentUnique_of_eq_or_SL nonSLComponentUnique_of_forall_SL
  nonSLComponentUnique_of_mulEquiv slComponentForm_of_forall_SL)
open scoped MatrixGroups

theorem toralCentralizer_nonSLUnique_of_orbitCheck
    {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2) {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      NonSLComponentUnique K (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))))
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    NonSLComponentUnique K (toralCentralizer τ K b) := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 hcert hb
  by_cases h0 : listMask (τ := τ) (reps.getD ρ []) = fun _ => false
  · refine absurd (eq_one_of_rootChar_smul_eq_one (w := w) fun v => ?_) hb1
    rw [hw v]
    congr 1
    funext i
    change (if listMask (τ := τ) (reps.getD ρ []) i then (-1 : Kˣ) else 1) = 1
    rw [h0]
    rfl
  · let e : toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
        toralCentralizer τ K b :=
      ((toralCentralizer τ K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact nonSLComponentUnique_of_mulEquiv e.symm (hreps ρ hρ h0)

theorem oddExcInnerDiagNonSLUnique_of_toral
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hrow : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
      Nat.card K = p ^ f → ∀ b : Fin τ.rank → Kˣ, (∀ i, b i = 1 ∨ b i = -1) → b ≠ 1 →
        NonSLComponentUnique K (toralCentralizer τ K b)) :
    OddExcInnerDiagNonSLUnique τ := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag hτ hKodd hαg hα
  exact nonSLComponentUnique_of_mulEquiv Θ (hrow K p f hp hp2 hKp b hb (hb1 hα1))

theorem e8_toral_D8_nonSLUnique
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NonSLComponentUnique K (toralCentralizer .E8 K (bitsTuple e8BitsD8)) := by
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
  exact nonSLComponentUnique_of_eq_or_SL fun L hL =>
    Or.inl (eq_of_isComponent_of_normal_quasisimple hq hsolv hL)

theorem e8_toral_E7_nonSLUnique
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NonSLComponentUnique K (toralCentralizer .E8 K (bitsTuple e8BitsE7)) := by
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
  refine nonSLComponentUnique_of_eq_or_SL
    (B := H.subgroupOf (toralCentralizer .E8 K (bitsTuple e8BitsE7))) fun M hM => ?_
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

theorem oddExcInnerDiagNonSLUnique_E8
    : OddExcInnerDiagNonSLUnique .E8 := by
  refine oddExcInnerDiagNonSLUnique_of_toral (Or.inr (Or.inr (Or.inr rfl)))
    (fun K _ _ p f hp hp2 hKp b hb hb1 => ?_)
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_nonSLUnique_of_orbitCheck hK2 e8SignOrbit_check (fun ρ hρ hne => ?_)
    hb hb1
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e8_toral_D8_nonSLUnique hp hp2 hKp
  ·
    have hmap := map_conj_toralCentralizer_of_maskAct (K := K) hK2 e8MaskWord e8BitsE7
    rw [maskAct_e8MaskWord] at hmap
    let e : toralCentralizer .E8 K (bitsTuple e8BitsE7) ≃*
        toralCentralizer .E8 K (bitsTuple (listMask (e8SignReps.getD 2 []))) :=
      ((toralCentralizer .E8 K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact nonSLComponentUnique_of_mulEquiv e.symm (e8_toral_E7_nonSLUnique hp hp2 hKp)

theorem f4_toral_C3_nonSLUnique
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NonSLComponentUnique K (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := by
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
  refine nonSLComponentUnique_of_eq_or_SL
    (B := H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) fun M hM => ?_
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

theorem f4_toral_B4_nonSLUnique
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NonSLComponentUnique K (toralCentralizer .F4 K (bitsTuple f4BitsB4)) := by
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
  exact nonSLComponentUnique_of_eq_or_SL fun L hL =>
    Or.inl (eq_of_isComponent_of_normal_quasisimple hq hsolv hL)

theorem oddExcInnerDiagNonSLUnique_F4
    : OddExcInnerDiagNonSLUnique .F4 := by
  refine oddExcInnerDiagNonSLUnique_of_toral (Or.inr (Or.inl rfl))
    (fun K _ _ p f hp hp2 hKp b hb hb1 => ?_)
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_nonSLUnique_of_orbitCheck hK2 f4SignOrbitB4_check
    (fun ρ hρ hne => ?_) hb hb1
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact f4_toral_C3_nonSLUnique hp hp2 hKp
  · exact f4_toral_B4_nonSLUnique hp hp2 hKp

theorem e6_toral_D5_nonSLUnique
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NonSLComponentUnique K (toralCentralizer .E6 K (bitsTuple e6BitsD5)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _
      (bitsTuple_mem (K := K) e6BitsD5)
  obtain ⟨hqs, -⟩ := e6_levi_D5_recognition hp hp2 hK
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsD5)) =
      subsystemGroup .E6 K e6LeviD5 := by
    rw [rootCharKernel_e6BitsD5 hK2, ← subsystemGroup_eq_rootSpan]
  let e₁ := MulEquiv.subgroupCongr hS
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁).symm hqs
  exact nonSLComponentUnique_of_eq_or_SL fun L hL =>
    Or.inl (eq_of_isComponent_of_normal_quasisimple hq hsolv hL)

theorem e6_toral_A5_nonSLUnique
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NonSLComponentUnique K (toralCentralizer .E6 K (bitsTuple e6BitsA5)) := by
  classical
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
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
  obtain ⟨hqH, -⟩ := e6_levi_A5_recognition hp hp2 hK
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
  refine nonSLComponentUnique_of_eq_or_SL
    (B := H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) fun M hM => ?_
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  by_cases h5 : 5 ≤ Nat.card K
  · have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm (hfin.2 h5).1
    have hn₂ : ((Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))).subgroupOf
        ((rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
          (toralCentralizer .E6 K (bitsTuple e6BitsA5)))).Normal := by
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
    have hs₂ : Group.IsSolvable (Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
      haveI := (hfin.1 h3').1
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hQX).injective
    exact Or.inl (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM hMS)

theorem oddExcInnerDiagNonSLUnique_E6
    : OddExcInnerDiagNonSLUnique .E6 := by
  refine oddExcInnerDiagNonSLUnique_of_toral (Or.inr (Or.inr (Or.inl rfl)))
    (fun K _ _ p f hp hp2 hKp b hb hb1 => ?_)
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_nonSLUnique_of_orbitCheck hK2 e6SignOrbit_check (fun ρ hρ hne => ?_)
    hb hb1
  have hlen : e6SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e6_toral_D5_nonSLUnique hp hp2 hKp
  · exact e6_toral_A5_nonSLUnique hp hp2 hKp

theorem toralCentralizer_G2_SL
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (b : Fin Tag.G2.rank → Kˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) {M : Subgroup (toralCentralizer .G2 K b)}
    (hM : IsComponent M) : Nonempty (M ≃* SL(2, K)) := by
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hKodd) (by decide)
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, hcases, hstruct, hq3⟩ :=
    odd_G2_toral_involution_fixed_p_components K hKodd b hb
  by_cases hK3 : Nat.card K = 3
  · have := (hq3 hK3 hb1).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨α₀, β₀, hc⟩ : ∃ α₀ β₀ : Fin Tag.G2.rank → ℤ,
      (b = ![-1, 1] ∧ α₀ = ![0, 1] ∧ β₀ = ![2, 3]) ∨
        (b = ![1, -1] ∧ α₀ = ![1, 0] ∧ β₀ = ![1, 2]) ∨
          (b = ![-1, -1] ∧ α₀ = ![1, 1] ∧ β₀ = ![1, 3]) := by
    rcases hcases with h | h | h | h
    · exact absurd h hb1
    · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩)⟩
    · exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
  obtain ⟨-, -, hS, hcomm, -, ⟨eα⟩, ⟨eβ⟩, hSX, hSn, hsolv, -⟩ := hstruct α₀ β₀ hc
  set X := toralCentralizer .G2 K b
  set Qα := rootSubgroup .G2 K α₀ ⊔ rootSubgroup .G2 K (-α₀)
  set Qβ := rootSubgroup .G2 K β₀ ⊔ rootSubgroup .G2 K (-β₀)
  have hQαX : Qα ≤ X := (hS ▸ (le_sup_left : Qα ≤ Qα ⊔ Qβ)).trans hSX
  have hQβX : Qβ ≤ X := (hS ▸ (le_sup_right : Qβ ≤ Qα ⊔ Qβ)).trans hSX
  have hD : (rootSpan .G2 K (rootCharKernel b)).subgroupOf X =
      Qα.subgroupOf X ⊔ Qβ.subgroupOf X := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hQαX hQβX
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  let eα' : Qα.subgroupOf X ≃* SL2 K := (Subgroup.subgroupOfEquivOfLe hQαX).trans eα.symm
  let eβ' : Qβ.subgroupOf X ≃* SL2 K := (Subgroup.subgroupOfEquivOfLe hQβX).trans eβ.symm
  have hqα : IsQuasisimple (Qα.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eα'.symm hSL
  have hqβ : IsQuasisimple (Qβ.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eβ'.symm hSL
  have hαβ : ∀ x ∈ Qα.subgroupOf X, ∀ y ∈ Qβ.subgroupOf X, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h1 _ hy).symm)
  have hnα : ((Qα.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hnβ : ((Qβ.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hαβ y hy x hx).symm)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  rcases eq_or_eq_of_isComponent_le_sup hD hqα hqβ hnα hnβ hM hMS with h | h
  · exact ⟨(MulEquiv.subgroupCongr h).trans eα'⟩
  · exact ⟨(MulEquiv.subgroupCongr h).trans eβ'⟩

theorem oddExcInnerDiagNonSLUnique_G2
    : OddExcInnerDiagNonSLUnique .G2 :=
  oddExcInnerDiagNonSLUnique_of_toral (Or.inl rfl) fun _ _ _ _ _ hp hp2 hKp b hb hb1 =>
    nonSLComponentUnique_of_forall_SL fun _ hM => toralCentralizer_G2_SL hp hp2 hKp b hb hb1 hM

theorem oddExcInnerDiagSLForm_G2
    : OddExcInnerDiagSLForm .G2 :=
  oddExcInnerDiagSLForm_of_toral (Or.inl rfl)
    (fun K _ _ hK α hα L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components
        .G2 (Or.inl rfl) K hK α hα 2 Nat.prime_two L hL)
    fun _ _ _ _ _ hp hp2 hKp b hb hb1 =>
      slComponentForm_of_forall_SL fun _ hM => toralCentralizer_G2_SL hp hp2 hKp b hb hb1 hM

end CFSG.ComponentClassification.CatLeafProof
