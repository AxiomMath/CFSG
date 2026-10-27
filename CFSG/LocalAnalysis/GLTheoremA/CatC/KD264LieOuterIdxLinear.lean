module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterLinear
public import CFSG.Adapters.CatalogueFieldBridges.Linear

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL
open CFSG.GorensteinWalter CFSG.GH74.GLS.IVK
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK CFSG.LieType.SeitzGeneration
open Matrix
open CFSG.Adapters.CatalogueFieldBridges

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

private theorem exists_quotient_center_catalogue_projectiveSL {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Field K] [Finite K] (k : Subfield K) {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpf : p ∣ f) (hcard : Nat.card ↥k = ℓ ^ (f / p))
    (hkp : Nat.card ↥k ^ p = ℓ ^ f) :
    ∃ i : TauCeti.CFSGIndex,
      Nonempty (↥(linearSubfieldInclusion (n + 1) k).range ⧸
        Subgroup.center ↥(linearSubfieldInclusion (n + 1) k).range ≃* i.Group) ∧
      subRelC p (.A n ⟨ℓ, f, hℓ, hf⟩) i := by
  have hf0 : 0 < f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  let q₀ : TauCeti.PrimePower := ⟨ℓ, f / p, hℓ, hf0⟩
  have hq₀ : q₀.card = Nat.card ↥k := (TauCeti.PrimePower.card_def q₀).trans hcard.symm
  let T := (linearSubfieldInclusion (n + 1) k).range
  have hinj : Function.Injective (linearSubfieldInclusion (n + 1) k) :=
    linearSubfieldInclusion_injective (by omega) k
  let eT : ↥T ≃* projectiveSL (n + 1) ↥k := (MonoidHom.ofInjective hinj).symm
  let eProj : ↥T ≃* ProjectiveSpecialLinearGroup (Fin (n + 1)) ↥k :=
    eT.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) ↥k).symm
  haveI hsimplePSL : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin (n + 1)) ↥k) :=
    (CFSG.LinearGroups.linear_projective_simple (n := n + 1) (by omega)
      (Or.inl (by omega))).2.1
  have hperfPSL : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin (n + 1)) ↥k) :=
    CFSG.LinearGroups.linear_projective_perfect (n := n + 1) (by omega) (Or.inl (by omega))
  haveI hntPSL : Nontrivial (ProjectiveSpecialLinearGroup (Fin (n + 1)) ↥k) :=
    CFSG.LinearGroups.linear_projective_nontrivial (n := n + 1) (by omega)
  obtain ⟨a, ha⟩ := not_forall.mp
    (not_comm_of_commutator_eq_top hperfPSL.commutator_eq_top)
  obtain ⟨b, hb⟩ := not_forall.mp ha
  have hZT : Subgroup.center ↥T = ⊥ := by
    haveI : IsSimpleGroup ↥T := eProj.isSimpleGroup
    have hnaT : ∃ x y : ↥T, x * y ≠ y * x :=
      ⟨eProj.symm a, eProj.symm b, fun h => hb (by simpa using congrArg eProj h)⟩
    exact CFSG.CGT.Timmesfeld75.center_eq_bot_of_simple_nonabelian ↥T hnaT
  by_cases h2 : n = 2 ∧ Nat.card ↥k = 2
  · obtain ⟨rfl, hk2⟩ := h2
    obtain ⟨q, hv, hq7, ⟨ePi⟩⟩ := nonempty_projectiveSL_three_mulEquiv_catalogue hk2
    refine ⟨.lie ⟨.A 1 q, hv⟩,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZT).trans QuotientGroup.quotientBot).trans
        (eT.trans ePi)⟩,
      Or.inr (Or.inr (Or.inl ⟨⟨q, rfl, hq7⟩, ⟨⟨ℓ, f, hℓ, hf⟩, rfl⟩, ?_⟩))⟩
    show fieldSize (.A 2 ⟨ℓ, f, hℓ, hf⟩) = 2 ^ p
    rw [show fieldSize (.A 2 ⟨ℓ, f, hℓ, hf⟩) = ℓ ^ f from TauCeti.PrimePower.card_def _,
      ← hkp, hk2]
  by_cases h3 : n = 3 ∧ Nat.card ↥k = 2
  · obtain ⟨rfl, hk2⟩ := h3
    obtain ⟨ePi⟩ := nonempty_projectiveSL_four_mulEquiv_alternating_eight hk2
    let i : TauCeti.CFSGIndex := .alternating 8 (by norm_num)
    have eQ : Nonempty (↥T ⧸ Subgroup.center ↥T ≃* i.Group) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZT).trans QuotientGroup.quotientBot).trans
        (eT.trans ePi)⟩
    refine ⟨i, eQ, ?_⟩
    · exact Or.inr (Or.inr ⟨rfl, ⟨⟨⟨ℓ, f, hℓ, hf⟩, rfl⟩, by
        show fieldSize (.A 3 ⟨ℓ, f, hℓ, hf⟩) = 2 ^ p
        rw [show fieldSize (.A 3 ⟨ℓ, f, hℓ, hf⟩) = ℓ ^ f from
          TauCeti.PrimePower.card_def _, ← hkp, hk2]⟩⟩)
  · have hv₀ : (TauCeti.LieTypeIndex.A n ⟨ℓ, f / p, hℓ, hf0⟩).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      refine ⟨⟨by omega, fun h1 => by omega⟩, ?_⟩
      rintro (⟨h1, -⟩ | ⟨h2n, hq2⟩ | ⟨h3n, hq2⟩)
      · omega
      · exact h2 ⟨h2n, hq₀ ▸ hq2⟩
      · exact h3 ⟨by omega, hq₀ ▸ hq2⟩
    obtain ⟨ePi⟩ := nonempty_projectiveSL_mulEquiv_lie (q := q₀) hv₀ hq₀.symm
    refine ⟨.lie ⟨.A n ⟨ℓ, f / p, hℓ, hf0⟩, hv₀⟩,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZT).trans QuotientGroup.quotientBot).trans
        (eT.trans ePi)⟩, Or.inl ⟨rfl, ?_⟩⟩
    show fieldSize (.A n ⟨ℓ, f / p, hℓ, hf0⟩) ^ p = fieldSize (.A n ⟨ℓ, f, hℓ, hf⟩)
    rw [show fieldSize (.A n ⟨ℓ, f / p, hℓ, hf0⟩) = Nat.card ↥k from hq₀,
      show fieldSize (.A n ⟨ℓ, f, hℓ, hf⟩) = ℓ ^ f from TauCeti.PrimePower.card_def _]
    exact hkp

private theorem exists_quotient_center_catalogue_psl2 {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    (h4 : 4 ≤ Nat.card (fixedField σ)) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hpf : p ∣ f) (hcardf : Nat.card (fixedField σ) = ℓ ^ (f / p))
    (hkF : Nat.card (fixedField σ) ^ p = ℓ ^ f) :
    ∃ i : TauCeti.CFSGIndex,
      Nonempty (↥(pslIncl σ).range ⧸ Subgroup.center ↥(pslIncl σ).range ≃* i.Group) ∧
      subRelC p (.A 1 ⟨ℓ, f, hℓ, hf⟩) i := by
  haveI : Fintype F := Fintype.ofFinite F
  have hf0 : 0 < f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hodd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
  let k := fixedField σ
  haveI : Fintype ↥k := Fintype.ofInjective (Subtype.val : ↥k → F) Subtype.val_injective
  let q₀ : TauCeti.PrimePower := ⟨ℓ, f / p, hℓ, hf0⟩
  have hq₀ : q₀.card = Nat.card ↥k := (TauCeti.PrimePower.card_def q₀).trans hcardf.symm
  let T := (pslIncl σ).range
  let eT : ↥T ≃* PSL2 ↥k := (MonoidHom.ofInjective (pslIncl_injective σ)).symm
  haveI hsimple : IsSimpleGroup (PSL2 ↥k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    (by omega)
  have hperf : Group.IsPerfect (PSL2 ↥k) := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ↥k)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact CFSG.LinearGroups.linear_projective_perfect (n := 2) (by norm_num) (Or.inr ⟨s, hs⟩)
  haveI hnt : Nontrivial (PSL2 ↥k) :=
    CFSG.LinearGroups.linear_projective_nontrivial (by norm_num)
  obtain ⟨a, ha⟩ := not_forall.mp (not_comm_of_commutator_eq_top hperf.commutator_eq_top)
  obtain ⟨b, hb⟩ := not_forall.mp ha
  have hZT : Subgroup.center ↥T = ⊥ := by
    haveI : IsSimpleGroup ↥T := eT.isSimpleGroup
    have hnaT : ∃ x y : ↥T, x * y ≠ y * x :=
      ⟨eT.symm a, eT.symm b, fun h => hb (by simpa using congrArg eT h)⟩
    exact CFSG.CGT.Timmesfeld75.center_eq_bot_of_simple_nonabelian ↥T hnaT
  by_cases h45 : Nat.card ↥k = 4 ∨ Nat.card ↥k = 5
  · obtain ⟨ePi⟩ := nonempty_psl2_mulEquiv_alternating_five h45
    let i : TauCeti.CFSGIndex := .alternating 5 (by norm_num)
    have eQ : Nonempty (↥T ⧸ Subgroup.center ↥T ≃* i.Group) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZT).trans QuotientGroup.quotientBot).trans
        (eT.trans ePi)⟩
    refine ⟨i, eQ, Or.inl ⟨rfl, ⟨⟨⟨ℓ, f, hℓ, hf⟩, rfl⟩, ?_⟩⟩⟩
    show fieldSize (.A 1 ⟨ℓ, f, hℓ, hf⟩) = 4 ^ p ∨
      fieldSize (.A 1 ⟨ℓ, f, hℓ, hf⟩) = 5 ^ p
    rw [show fieldSize (.A 1 ⟨ℓ, f, hℓ, hf⟩) = ℓ ^ f from TauCeti.PrimePower.card_def _,
      ← hkF]
    rcases h45 with h | h <;> [left; right] <;> rw [h]
  by_cases h9 : Nat.card ↥k = 9
  · obtain ⟨ePi⟩ := nonempty_psl2_nine_mulEquiv_alternating_six h9
    let i : TauCeti.CFSGIndex := .alternating 6 (by norm_num)
    have eQ : Nonempty (↥T ⧸ Subgroup.center ↥T ≃* i.Group) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZT).trans QuotientGroup.quotientBot).trans
        (eT.trans ePi)⟩
    refine ⟨i, eQ, Or.inr (Or.inl ⟨rfl, Or.inl ⟨⟨⟨ℓ, f, hℓ, hf⟩, rfl⟩, ?_⟩⟩)⟩
    show fieldSize (.A 1 ⟨ℓ, f, hℓ, hf⟩) = 9 ^ p
    rw [show fieldSize (.A 1 ⟨ℓ, f, hℓ, hf⟩) = ℓ ^ f from TauCeti.PrimePower.card_def _,
      ← hkF, h9]
  · have hv₀ : (TauCeti.LieTypeIndex.A 1 ⟨ℓ, f / p, hℓ, hf0⟩).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      refine ⟨⟨le_rfl, fun _ => ?_⟩, ?_⟩
      · rw [hq₀]; exact h4
      · rintro (⟨-, h4q | h5q | h9q⟩ | ⟨h2, -⟩ | ⟨h3, -⟩)
        · exact h45 (Or.inl (hq₀ ▸ h4q))
        · exact h45 (Or.inr (hq₀ ▸ h5q))
        · exact h9 (hq₀ ▸ h9q)
        · omega
        · omega
    obtain ⟨ePi⟩ := nonempty_projectiveSL_mulEquiv_lie (n := 1) (q := q₀) hv₀ hq₀.symm
    refine ⟨.lie ⟨.A 1 ⟨ℓ, f / p, hℓ, hf0⟩, hv₀⟩,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZT).trans QuotientGroup.quotientBot).trans
        (eT.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 ↥k).trans ePi))⟩,
      Or.inl ⟨rfl, ?_⟩⟩
    show fieldSize (.A 1 ⟨ℓ, f / p, hℓ, hf0⟩) ^ p = fieldSize (.A 1 ⟨ℓ, f, hℓ, hf⟩)
    rw [show fieldSize (.A 1 ⟨ℓ, f / p, hℓ, hf0⟩) = Nat.card ↥k from hq₀,
      show fieldSize (.A 1 ⟨ℓ, f, hℓ, hf⟩) = ℓ ^ f from TauCeti.PrimePower.card_def _]
    exact hkF

private theorem idxCoreAt_projectiveSL_fieldAut {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F]
    [Finite F] {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hF : Nat.card F = ℓ ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F)
    (hpdvd : p ∣ Nat.card (projectiveSL (n + 1) F)) {σ : F ≃+* F} (hσ : orderOf σ = p)
    (hFE : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p) :
    IdxCoreAt p (.A n ⟨ℓ, f, hℓ, hf⟩) (fieldAut (n + 1) F σ) := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ c, c ∈ k ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  obtain ⟨hpf, hkcard⟩ := card_semilinearFixedSubfield hℓ hf hF hσ
  have hkp : Nat.card ↥k ^ p = ℓ ^ f := by
    rw [hkcard, ← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hpf]
  have hpFk : ¬ p ∣ Nat.card ↥k := fun hd => hpF (hFE ▸ dvd_pow hd hp.ne_zero)
  have hGL : p ∣ Nat.card (GL (Fin (n + 1)) F) :=
    hpdvd.trans (card_projectiveSL_dvd_card_GL (n := n + 1) (by omega))
  have hinj : Function.Injective (linearSubfieldInclusion (n + 1) k) :=
    linearSubfieldInclusion_injective (by omega) k
  have hTdvd : p ∣ Nat.card (linearSubfieldInclusion (n + 1) k).range := by
    rw [show Nat.card (linearSubfieldInclusion (n + 1) k).range =
        Nat.card (projectiveSL (n + 1) ↥k) from
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact dvd_card_projectiveSL_of_dvd_card_GL hp (by omega) hFE hpFk hGL
  have hTF : (linearSubfieldInclusion (n + 1) k).range ≤ fixSubgroup (fieldAut (n + 1) F σ) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_fixSubgroup]
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) y
  have hTn : ∀ g ∈ fixSubgroup (fieldAut (n + 1) F σ),
      ∀ t ∈ (linearSubfieldInclusion (n + 1) k).range, g * t * g⁻¹ ∈
        (linearSubfieldInclusion (n + 1) k).range := by
    intro g hg t ht
    exact conj_mem_range_linearSubfieldInclusion σ (mem_fixSubgroup.1 hg) ht
  have hTq : CFSG.IsQuasisimple (linearSubfieldInclusion (n + 1) k).range :=
    isQuasisimple_range_linearSubfieldInclusion (n := n + 1) (by omega) k
  obtain ⟨i, ⟨eQ⟩, hRel⟩ := exists_quotient_center_catalogue_projectiveSL hn k hℓ hf hp hp2 hpf
    hkcard hkp
  exact ⟨_, hTF, hTn, hTq, hTdvd, i, ⟨eQ⟩, hRel⟩

private theorem idxCoreAt_psl2_fieldAut {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF8 : p = 3 → Nat.card F ≠ 8) (hpF : ¬ p ∣ Nat.card F)
    (hpdvd : p ∣ Nat.card (PSL2 F)) {σ : F ≃+* F} (hσ : orderOf σ = p) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hFc : Nat.card F = ℓ ^ f) :
    IdxCoreAt p (.A 1 ⟨ℓ, f, hℓ, hf⟩) (psl2FieldAut F σ) := by
  haveI : Finite (PSL2 F) := Finite.of_surjective
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)))
    (QuotientGroup.mk'_surjective _)
  have hodd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
  have hδp : orderOf (psl2FieldAut F σ) = p := by rw [orderOf_psl2FieldAut, hσ]
  have hδpow : (psl2FieldAut F σ) ^ p = 1 := by rw [← hδp]; exact pow_orderOf_eq_one _
  have hpF0 : ¬ p ∣ Nat.card (fixedField σ) := by
    intro hd
    apply hpF
    rw [← fixedField_card_pow σ, hσ]
    exact dvd_pow hd hp.ne_zero
  obtain ⟨y0, hy0, hy0ord⟩ :=
    exists_orderOf_eq_prime_mem_fixSubgroup hp (psl2FieldAut F σ) hδpow hpdvd
  have h4 : 4 ≤ Nat.card (fixedField σ) := by
    by_cases hp35 : p = 3 ∨ p = 5
    · exact four_le_card_fixedField_odd hp hp35 hF8 hσ hpF0 y0 hy0 hy0ord
    · have hp5 : 5 < p := by
        have hpne3 : p ≠ 3 := fun h => hp35 (Or.inl h)
        have hpne5 : p ≠ 5 := fun h => hp35 (Or.inr h)
        have h2 := hp.two_le
        by_contra hle
        have hp6 : p ≤ 5 := by omega
        interval_cases p
        · exact hp2 rfl
        · exact hpne3 rfl
        · exact absurd hp (by norm_num)
        · exact hpne5 rfl
      exact four_le_card_fixedField hp hp5 hσ hpF0 y0 hy0 hy0ord
  have hsub : fixedField σ = semilinearFixedSubfield σ := by
    ext x
    rw [mem_fixedField_iff, RingHom.mem_eqLocusField]
    rfl
  obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hFc hσ
  have hcardf : Nat.card (fixedField σ) = ℓ ^ (f / p) := by
    rw [hsub]; exact hcardk
  have hkF : Nat.card (fixedField σ) ^ p = ℓ ^ f := by
    rw [hcardf, ← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hpf]
  have hTF : (pslIncl σ).range ≤ fixSubgroup (psl2FieldAut F σ) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_fixSubgroup]
    exact (mem_range_pslIncl_iff σ hodd _).1 ⟨y, rfl⟩
  have hTn : ∀ g ∈ fixSubgroup (psl2FieldAut F σ), ∀ t ∈ (pslIncl σ).range,
      g * t * g⁻¹ ∈ (pslIncl σ).range := by
    intro g hg t ht
    rw [mem_fixSubgroup] at hg
    exact (mem_range_pslIncl_iff σ hodd _).2 (by
      have ht' := (mem_range_pslIncl_iff σ hodd t).1 ht
      change psl2FieldAut F σ (g * t * g⁻¹) = g * t * g⁻¹
      rw [map_mul, map_mul, map_inv, hg, ht'])
  have hTq : CFSG.IsQuasisimple (pslIncl σ).range := isQuasisimple_range_pslIncl σ h4
  have hTdvd : p ∣ Nat.card (pslIncl σ).range := by
    have hkrange : y0 ∈ (pslIncl σ).range := (mem_range_pslIncl_iff σ hodd y0).2 hy0
    have hord : orderOf (⟨y0, hkrange⟩ : (pslIncl σ).range) = p := by
      rw [Subgroup.orderOf_mk]; exact hy0ord
    rw [← hord]; exact orderOf_dvd_natCard _
  obtain ⟨i, ⟨eQ⟩, hRel⟩ := exists_quotient_center_catalogue_psl2 hp hp2 hσ h4 hℓ hf hpf hcardf hkF
  exact ⟨_, hTF, hTn, hTq, hTdvd, i, ⟨eQ⟩, hRel⟩

private theorem outerIdxAt_projectiveSL {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hF : Nat.card F = ℓ ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F) (hpdvd : p ∣ Nat.card (projectiveSL (n + 1) F)) :
    OuterIdxAt p (.A n ⟨ℓ, f, hℓ, hf⟩) (projectiveSL (n + 1) F) := by
  haveI : Finite (projectiveSL (n + 1) F) :=
    Finite.of_surjective (proj (n + 1) F) (proj_surjective (n := n + 1) (K := F))
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  refine outerIdxAt_of_idxCoreAt hp ?_
  intro x hxp hxo
  have hxin : x ∉ inner (projectiveSL (n + 1) F) :=
    fun h => hxo (inner_le_innAutDerived _ h)
  have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hxE : x ∈ semilinearAutGroup (n + 1) F :=
    mem_semilinearAutGroup_of_odd (by omega) (by rw [hxord]; exact hpodd)
  have hxlin : x ∉ linearAutGroup (n + 1) F := by
    intro hxD
    exact hxo (mem_innAutDerived_of_mem_linearAutGroup hp hp2 hxp hxD)
  obtain ⟨f₁, hℓ₁, hcard₁⟩ := FiniteField.card F (ringChar F)
  let f' : ℕ := f₁
  have hf'pos : 0 < f' := f₁.pos
  have hFc : Nat.card F = ringChar F ^ f' := by
    rw [Nat.card_eq_fintype_card]
    simpa [f'] using hcard₁
  obtain ⟨hpf, σ, hσ, ⟨h, hh, hxh⟩, hcardk⟩ :=
    higher_linear_prime_semilinear_field_descent' hℓ₁ hf'pos (by omega) hFc hp x hxE hxlin hxord
  have hFE : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p := by
    rw [hFc, hcardk, ← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hpf]
  exact idxCoreAt_of_conj
    (idxCoreAt_projectiveSL_fieldAut hn hℓ hf hF hp hp2 hpF hpdvd hσ hFE) h⁻¹
    (by rw [hxh]; group)

private theorem outerIdxAt_psl2 {F : Type} [Field F] [Finite F] {q : TauCeti.PrimePower} {p : ℕ}
    (hFq : Nat.card F = q.card) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : ¬ p ∣ Nat.card F) (hF8 : p = 3 → Nat.card F ≠ 8)
    (hpdvd : p ∣ Nat.card (PSL2 F)) : OuterIdxAt p (.A 1 q) (PSL2 F) := by
  haveI : Finite (PSL2 F) := Finite.of_surjective
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)))
    (QuotientGroup.mk'_surjective _)
  haveI : Fact p.Prime := ⟨hp⟩
  have hFpow : Nat.card F = q.p ^ q.exponent := hFq.trans (TauCeti.PrimePower.card_def q)
  refine outerIdxAt_of_idxCoreAt hp ?_
  intro x hxp hxo
  have hxin : x ∉ inner (PSL2 F) := fun h => hxo (inner_le_innAutDerived _ h)
  obtain ⟨σ, h, hσ, hxh⟩ := exists_outer_data hp hp2 hxp hxin
  exact idxCoreAt_of_conj
    (idxCoreAt_psl2_fieldAut hp hp2 hF8 hpF hpdvd hσ q.prime_p q.exponent_pos hFpow) h⁻¹
    (by rw [hxh]; group)

theorem lieOuterIdx_linear : LieOuterIdx isLinearIdx := by
  rintro ⟨d, hd⟩ p hp hp2 hpc hP hpdvd hExc
  cases d with
  | A n q =>
    have hpq : q.p ≠ p := by
      rw [TauCeti.LieTypeIndex.characteristic_A] at hpc
      exact fun hqp => hpc hqp.symm
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let F := GaloisField q.p q.exponent
    have hFpow : Nat.card F = q.p ^ q.exponent := by
      dsimp only [F]
      exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
    have hFcard : Nat.card F = q.card := hFpow.trans (TauCeti.PrimePower.card_def q).symm
    have hpF : ¬ p ∣ Nat.card F := by
      rw [hFcard]
      exact not_dvd_card_of_ne hp hpq.symm
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hd).1
    by_cases hn : n = 1
    · subst hn
      have hF8 : p = 3 → Nat.card F ≠ 8 := by
        intro hp3 h8
        refine hExc (Or.inl ⟨hp3, Or.inl ⟨q, Or.inl rfl, ?_⟩⟩)
        rw [← hFcard]; exact h8
      haveI : Finite (PSL2 F) := Finite.of_surjective
        (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)))
        (QuotientGroup.mk'_surjective _)
      have eModel : (TauCeti.CFSGIndex.lie ⟨.A 1 q, hd⟩).Group ≃* PSL2 F :=
        CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hd
      haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A 1 q, hd⟩).Group :=
        Finite.of_equiv (PSL2 F) eModel.toEquiv.symm
      have hpdvdM : p ∣ Nat.card (PSL2 F) := by
        rw [← Nat.card_congr eModel.toEquiv]; exact hpdvd
      exact outerIdxAt_of_mulEquiv hp eModel.symm
        (outerIdxAt_psl2 hFcard hp hp2 hpF hF8 hpdvdM)
    · have hn2 : 2 ≤ n := by
        have := hrange.1
        omega
      haveI : Finite (projectiveSL (n + 1) F) :=
        Finite.of_surjective (proj (n + 1) F) (proj_surjective (n := n + 1) (K := F))
      have eModel : (TauCeti.CFSGIndex.lie ⟨.A n q, hd⟩).Group ≃* projectiveSL (n + 1) F :=
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd).trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) F)
      haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A n q, hd⟩).Group :=
        Finite.of_equiv (projectiveSL (n + 1) F) eModel.toEquiv.symm
      have hpdvdM : p ∣ Nat.card (projectiveSL (n + 1) F) := by
        rw [← Nat.card_congr eModel.toEquiv]; exact hpdvd
      exact outerIdxAt_of_mulEquiv hp eModel.symm
        (outerIdxAt_projectiveSL hn2 q.prime_p q.exponent_pos hFpow hp hp2 hpF hpdvdM)
  | _ => exact absurd hP (by simp [isLinearIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
