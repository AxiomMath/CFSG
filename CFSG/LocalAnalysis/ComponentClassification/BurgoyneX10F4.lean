module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Explicit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4SignOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.ClassicalInvolution.RouteD.Exotic (ChainOK)
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem excCompModel_f4_toral_B4_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsB4))} (hM : IsComponent M) :
    ExcCompModel p M := by
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
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _
      (bitsTuple_mem (K := K) f4BitsB4)
  have hker : rootCharKernel (bitsTuple (K := K) f4BitsB4) =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_B4_F4 hp hp2 hK hq4 h2
  have hSim : (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    rw [map_subtype_iSup_b4Chain, hker]
  let e₁ : ↥(⨆ k, b4Chain K k) ≃* rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) :=
    ((⨆ k, b4Chain K k).equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hSim)
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* ↥(⨆ k, b4Chain K k) := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁.symm)
  exact ⟨.POmegaOdd, 4, f, (by unfold ExcCompTag; decide), hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

theorem excCompModel_f4_toral_C3_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsC3))} (hM : IsComponent M) :
    ExcCompModel p M := by
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
    exact ⟨.PSp, 3, f, (by unfold ExcCompTag; decide), hadm, lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlieH⟩
  · let e : M ≃* SL2 K :=
      ((MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hQX)).trans eQ.symm
    exact excCompModel_of_equiv_psl_two hp hf hK hc2 hc3
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

theorem excCompModel_f4_toral_C3_component_three
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h3 : Nat.card K = 3)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsC3))} (hM : IsComponent M) :
    ExcCompModel p M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
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
  obtain ⟨-, -, -, hqH, hlieH⟩ := f4_levi_C3_recognition_frame hp hp2 hK h2
  obtain ⟨-, -, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .F4 K hK2 isRoot_hiF4
  have hsQ : Group.IsSolvable Q := (hfin.1 h3).1
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
  have hs₂ : Group.IsSolvable (Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQX).injective
  have hn₁ : ((H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))).subgroupOf
      ((rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subtype.ext (hcomm x.1 hx y.1 hy))
  have h := eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM
    (le_of_isComponent_of_solvable_quotient hsolv hM)
  let e : M ≃* H := (MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hHX)
  exact ⟨.PSp, 3, f, (by unfold ExcCompTag; decide), hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlieH⟩

theorem excCompModel_f4_toral_B4_component_frame
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsB4))} (hM : IsComponent M) :
    ExcCompModel p M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _
      (bitsTuple_mem (K := K) f4BitsB4)
  have hker : rootCharKernel (bitsTuple (K := K) f4BitsB4) =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_B4_F4_frame hp hp2 hK h2
  have hSim : (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    rw [map_subtype_iSup_b4Chain, hker]
  let e₁ : ↥(⨆ k, b4Chain K k) ≃* rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) :=
    ((⨆ k, b4Chain K k).equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hSim)
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* ↥(⨆ k, b4Chain K k) := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁.symm)
  exact ⟨.POmegaOdd, 4, f, (by unfold ExcCompTag; decide), hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

theorem excCompModel_f4_toralCentralizer_component
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    {b : Fin Tag.F4.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1)
    {M : Subgroup (toralCentralizer .F4 K b)} (hM : IsComponent M) :
    ExcCompModel p M := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨ρ, hρ, w, hw, hmap⟩ :=
    exists_conj_toralCentralizer_of_orbitCheck hK2 f4SignOrbitB4_check hb
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  have key : ∀ (c : Fin (Tag.rank .F4) → Kˣ),
      (toralCentralizer .F4 K c).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
          toralCentralizer .F4 K b →
      (∀ N : Subgroup (toralCentralizer .F4 K c), IsComponent N → ExcCompModel p N) →
        ExcCompModel p M := by
    intro c hc hcomp
    let e : toralCentralizer .F4 K c ≃* toralCentralizer .F4 K b :=
      ((toralCentralizer .F4 K c).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hc)
    exact ExcCompModel.of_mulEquiv (M.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (hcomp _ (LocalCores.isComponent_map_mulEquiv e.symm hM))
  interval_cases ρ
  · exact absurd (eq_one_of_rootChar_smul_eq_one (w := w) (by
      intro v
      rw [hw v]
      congr 1
      funext i
      have h0 : listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i = false := by
        revert i
        decide
      change (if listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i then (-1 : Kˣ) else 1) = 1
      rw [h0]
      rfl)) hb1
  · exact key _ hmap fun N hN => excCompModel_f4_toral_C3_component hp hp2 hK h5 hN
  · exact key _ hmap fun N hN => excCompModel_f4_toral_B4_component hp hp2 hK h5 hN

theorem excCompModel_oddExcInnerDiag_F4_of_five_le
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKp : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K) {α : MulAut (adjointGroup .F4 K)}
    {g : adjointGroup .F4 K} {a : Fin Tag.F4.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .F4 K, (α h : ModGL .F4 K) = (g : ModGL .F4 K) *
      rootDiagUnit .F4 a * (h : ModGL .F4 K) * (rootDiagUnit .F4 a)⁻¹ * (g : ModGL .F4 K)⁻¹)
    (hαo : orderOf α = 2) {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L) :
    ExcCompModel p L := by
  have hKodd : Odd (Nat.card K) := by rw [hKp]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inl rfl)) hKodd hαg hα
  exact ExcCompModel.of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (excCompModel_f4_toralCentralizer_component hp hp2 hKp h5 hb (hb1 hα1)
      (LocalCores.isComponent_map_mulEquiv Θ hL))

theorem excCompModel_f4_toralCentralizer_component_of_reps
    {K : Type} [Field K] {p : ℕ} (hK2 : ringChar K ≠ 2)
    (hC3 : ∀ N : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsC3)), IsComponent N →
      ExcCompModel p N)
    (hB4 : ∀ N : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsB4)), IsComponent N →
      ExcCompModel p N)
    {b : Fin Tag.F4.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1)
    {M : Subgroup (toralCentralizer .F4 K b)} (hM : IsComponent M) :
    ExcCompModel p M := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ :=
    exists_conj_toralCentralizer_of_orbitCheck hK2 f4SignOrbitB4_check hb
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  have key : ∀ (c : Fin (Tag.rank .F4) → Kˣ),
      (toralCentralizer .F4 K c).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
          toralCentralizer .F4 K b →
      (∀ N : Subgroup (toralCentralizer .F4 K c), IsComponent N → ExcCompModel p N) →
        ExcCompModel p M := by
    intro c hc hcomp
    let e : toralCentralizer .F4 K c ≃* toralCentralizer .F4 K b :=
      ((toralCentralizer .F4 K c).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hc)
    exact ExcCompModel.of_mulEquiv (M.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (hcomp _ (LocalCores.isComponent_map_mulEquiv e.symm hM))
  interval_cases ρ
  · exact absurd (eq_one_of_rootChar_smul_eq_one (w := w) (by
      intro v
      rw [hw v]
      congr 1
      funext i
      have h0 : listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i = false := by
        revert i
        decide
      change (if listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i then (-1 : Kˣ) else 1) = 1
      rw [h0]
      rfl)) hb1
  · exact key _ hmap hC3
  · exact key _ hmap hB4

theorem excInnerModel_F4
    : ExcInnerModel .F4 := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo L hL
  by_cases h5 : 5 ≤ Nat.card K
  · exact excCompModel_oddExcInnerDiag_F4_of_five_le hp hp2 hKp h5 hαg hαo hL
  ·
    obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hKp
    have hKodd : Odd (Nat.card K) := by
      rw [hKp]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hq3 : Nat.card K = 3 := by
      obtain ⟨k, hk⟩ := hKodd
      omega
    have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
    have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
    have hα1 : α ≠ 1 := fun h => by
      rw [h, orderOf_one] at hαo
      exact absurd hαo (by norm_num)
    obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
      exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inl rfl)) hKodd hαg hα
    exact ExcCompModel.of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
      (excCompModel_f4_toralCentralizer_component_of_reps hK2
        (fun N hN => excCompModel_f4_toral_C3_component_three hp hp2 hKp hq3 hN)
        (fun N hN => excCompModel_f4_toral_B4_component_frame hp hp2 hKp hN) hb (hb1 hα1)
        (LocalCores.isComponent_map_mulEquiv Θ hL))


theorem excFamilyModel_F4_holds
    : ExcFamilyModel .F4 :=
  excFamilyModel_F4 excInnerModel_F4

end CFSG.ComponentClassification.Burgoyne.X10
