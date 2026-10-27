module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcD4ClassLeaves
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4E6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158GInn3
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoKac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Class
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTwoPartDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open
open CFSG.Blueprint (LieModel classicalTags)
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenLabel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.StandardType (markTag markRank markChar MarkedModel)
open CFSG.StandardType.Canonical (largeEvenMarking_mono)
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial

section Exclusion


theorem l154d4_false_of_excl {X' : Type} [Group X'] (h : L154D4Excl X')
    (hD4 : catalogIs X' isD4any) : False := by
  obtain ⟨q, hv, hp2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.T158G.t158g_d4_index hD4
  have hX : LieModel X' .POmegaPlus 4 2 q.exponent := by
    have h' := CFSG.Models.lieModel_D 4 q hv e
    rw [hp2] at h'
    exact CFSG.Models.LieModel.toBlueprint (by decide) h'
  rcases h with ⟨t, n, f, hM, hne⟩ | h6
  · obtain ⟨rfl, rfl, -⟩ := CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique
      (Or.inl rfl) hX hM
    exact hne ⟨rfl, rfl⟩
  · obtain ⟨e6⟩ := h6
    have h360 : Nat.card X' = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hord := CFSG.SeitzReduction.OmegaPilot.card_of_lieModel_POmega_two (Or.inl rfl) hX
    have hdvd := (CFSG.SeitzReduction.OmegaPilot.ordD_two_pow_bounds (n := 4) (by norm_num)
      q.exponent_pos).1
    have hord' : Nat.card X' = Open.ordD 4 (2 ^ q.exponent) := hord
    rw [← hord', h360] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h12 : 2 ^ 12 ≤ 2 ^ (q.exponent * (4 * (4 - 1))) :=
      Nat.pow_le_pow_right (by norm_num) (by have := q.exponent_pos; omega)
    omega

end Exclusion

section Marking


theorem l154d4_excl_of_marking {X : Type} [Group X] {P₀ : LargeEvenLabel → Prop}
    (h : LargeEvenMarking X fun lab _ _ _ _ _ => P₀ lab)
    (hP : ∀ lab, P₀ lab → ¬ (markTag lab = .POmegaPlus ∧ markRank lab = 4) ∧ markChar lab = 2) :
    L154D4Excl (X ⧸ Subgroup.center X) := by
  obtain ⟨lab, -, R, _, I, F, θ, -, -, hP', hMM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel h
  exact l154d4_excl_of_lieModel (hP lab hP').2 (hP lab hP').1 (MarkedModel.of_mulEquiv θ.symm hMM)

end Marking

section E6Form

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p : ℕ}

theorem l154d4_e6_of_form (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    L154D4ExclClass S i := by
  obtain ⟨f, n₁, g, π, hf, hstd, hX⟩ := l154_layer_data S haT i v hΨ
  have key : LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      fun lab _ _ _ _ _ => lab.tag = .E6 ∨ lab.tag = .twE6 := by
    rcases hstd.hπ with h1 | h1
    · haveI : Finite (frobeniusFixedField L 2 f) := finite_frobeniusFixedField hf
      have hL := hstd.stdLayer_eq_map_of_one (f := f) h1
      rw [hL, Subgroup.map_map] at hX
      have hj : Function.Injective ((MulAut.conj g).toMonoidHom.comp
          (baseChangeGL (frobeniusFixedField L 2 f).subtype)) :=
        (MulAut.conj g).injective.comp (baseChangeGL_injective _)
      rw [hX] at hqi ⊢
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inl h)
        (l154td4_e6_marking_inner hf (card_frobeniusFixedField_pow hf) hj hqi)
    · haveI : Finite (K2 L 2 f) := finite_frobeniusFixedField (by omega)
      haveI := certificate123_of_kernel
      have hL := hstd.stdLayer_eq_range_of_rho (f := f) h1
      have hpsi : psi2 τ L 2 f = (baseChangeGL (frobeniusFixedField L 2 (2 * f)).subtype).comp
          (e6Iota τ L f) := rfl
      rw [hL, MonoidHom.map_range, hpsi, ← MonoidHom.comp_assoc] at hX
      have hj : Function.Injective ((MulAut.conj g).toMonoidHom.comp
          (baseChangeGL (frobeniusFixedField L 2 (2 * f)).subtype)) :=
        (MulAut.conj g).injective.comp (baseChangeGL_injective _)
      rw [hX] at hqi ⊢
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inr h)
        (l154td4_e6_marking_outer hf hj hqi)
  refine l154d4_excl_of_marking key ?_
  rintro lab (h | h) <;> simp [markTag, markRank, markChar, h]

end E6Form

section E6Class

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154d4_excl_e6Class {τ : Tag} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ k, a k ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (h6 : L154E6Class a i) : L154D4ExclClass S i := by
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := l154_rootDiagUnit_pow hap
  have hle := l154_compRank_le (componentRoots (rootCharHom a) i)
  have h6r := h6.1
  cases τ with
  | G2 =>
    exfalso
    have hr : Tag.G2.rank = 2 := rfl
    omega
  | F4 =>
    exfalso
    have hr : Tag.F4.rank = 4 := rfl
    omega
  | D4 =>
    exfalso
    have hr : Tag.D4.rank = 4 := rfl
    omega
  | E6 => exact (l154_not_E6 ha1 i h6).elim
  | E7 =>
    obtain ⟨v, hv⟩ := l154_form_E7 S hp hpL hTp i h6
    exact l154d4_e6_of_form S hT i v hv hqi
  | E8 =>
    obtain ⟨v, hv⟩ := l154_form_E8 S hp hpL hTp i h6
    exact l154d4_e6_of_form S hT i v hv hqi

end E6Class

section D4

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154d4_excl_d4outer_E6 (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154D4ExclClass S i := by
  obtain ⟨f, -, hM⟩ := l154r4_of_rank_four_E6 S hp hpL hT hTp i hr hc hnin
  rw [ringChar.eq L 2] at hM
  rcases hM with hM | hM
  · exact l154d4_excl_of_lieModel rfl (by simp) hM
  · exact l154d4_excl_of_lieModel rfl (by simp) hM

end D4

section D4Stable

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem l154d4_E6_stable (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
    (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  exact hρ

end D4Stable

section Dispatch

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154d4_dispatch_E6 (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S 3 a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i)
    (hcon : ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))) :
    L154D4ExclClass S i := by
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  rcases l154_shape_E6 S hcls.prime hpL hTp i hA1 with hD | hE
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨n, e, hnr, hmodel⟩ :=
        l154d4_dInner_E6 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
      by_cases h4 : compRank (componentRoots (rootCharHom a) i) = 4
      · exfalso
        apply hcon
        have hn24 : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hD.2, h4]
        have hρ := l154d4_E6_stable S hcls.prime hpL hcls.torus hTp i h4 hn24
        have hfin : (componentRoots (rootCharHom a) i).Finite :=
          (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
        rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at hinner
        exact ⟨h4, hn24, hρ, hinner⟩
      · exact l154d4_excl_of_statedClassical (ringChar.eq L 2) (by simp [classicalTags])
          (fun h => h4 (hnr.symm.trans h.2)) hmodel
    · by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
      · exact l154d4_excl_twoD hcls.prime S hcls.torus hcls.pow hcls.ne_one i h5 hD.2 hinner
      · have h4 : compRank (componentRoots (rootCharHom a) i) = 4 := by
          have := hD.1
          omega
        exact l154d4_excl_d4outer_E6 S hcls.prime hpL hcls.torus hTp i h4 (by rw [hD.2, h4])
          hinner
  · exfalso
    have hr : compRank (componentRoots (rootCharHom a) i) ≤ 6 := compRank_le_rank _
    have h6 : compRank (componentRoots (rootCharHom a) i) = 6 := by
      have := hE.1
      omega
    exact hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩

theorem l154d4_dispatch_E7 (S : LangSetup Tag.E7 L p₀) {a : Fin Tag.E7.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S 3 a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i) :
    L154D4ExclClass S i := by
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit Tag.E7 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  rcases l154_shape_E7 S hcls.prime hpL hTp i hA1 with hD | hE
  · have hnot4 : ¬ compRank (componentRoots (rootCharHom a) i) = 4 := fun h4 =>
      CFSG.StandardType.ExcThreeAtTwo.not_d4Shape_of_three_E7 S hpL hTp i
        ⟨h4, by rw [hD.2, h4]⟩
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨n, e, hnr, hmodel⟩ :=
        l154d4_dInner_E7 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
      exact l154d4_excl_of_statedClassical (ringChar.eq L 2) (by simp [classicalTags])
        (fun h => hnot4 (hnr.symm.trans h.2)) hmodel
    · have h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
        have := hD.1
        omega
      exact l154d4_excl_twoD hcls.prime S hcls.torus hcls.pow hcls.ne_one i h5 hD.2 hinner
  · exfalso
    have hr : compRank (componentRoots (rootCharHom a) i) ≤ 7 := compRank_le_rank _
    by_cases h6 : compRank (componentRoots (rootCharHom a) i) = 6
    · exact hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩
    · have h7 : compRank (componentRoots (rootCharHom a) i) = 7 := by
        have := hE.1
        omega
      exact hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (by rw [hE.2, h7]; decide))

theorem l154d4_dispatch_E8 (S : LangSetup Tag.E8 L p₀) {a : Fin Tag.E8.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S 3 a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i) :
    L154D4ExclClass S i := by
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit Tag.E8 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  rcases l154_shape_E8 S hcls.prime hpL hTp i hA1 with hD | hE
  · have hnot4 : ¬ compRank (componentRoots (rootCharHom a) i) = 4 := fun h4 =>
      CFSG.StandardType.ExcThreeAtTwo.not_d4Shape_of_three_E8 S hpL hTp i
        ⟨h4, by rw [hD.2, h4]⟩
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨n, e, hnr, hmodel⟩ :=
        l154d4_dInner_E8 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
      exact l154d4_excl_of_statedClassical (ringChar.eq L 2) (by simp [classicalTags])
        (fun h => hnot4 (hnr.symm.trans h.2)) hmodel
    · have h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
        have := hD.1
        omega
      exact l154d4_excl_twoD hcls.prime S hcls.torus hcls.pow hcls.ne_one i h5 hD.2 hinner
  · have hr : compRank (componentRoots (rootCharHom a) i) ≤ 8 := compRank_le_rank _
    have h6' := hE.1
    by_cases h6 : compRank (componentRoots (rootCharHom a) i) = 6
    · exact (hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩).elim
    by_cases h7 : compRank (componentRoots (rootCharHom a) i) = 7
    · have hn : (componentRoots (rootCharHom a) i).ncard = 126 := by rw [hE.2, h7]; rfl
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact l154d4_excl_e7Class S hcls.prime hpL hcls.torus hTp i h7 hn hinner
      · exact (hinner (twistInner_of_shape S hcls.torus i 7 126 h7 hn (by omega) (by omega)
          (by omega) (by omega))).elim
    · have h8 : compRank (componentRoots (rootCharHom a) i) = 8 := by omega
      exact (hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (by rw [hE.2, h8]; decide))).elim

end Dispatch

section Final


theorem l154d4_class_holds : L154D4Class := by
  intro τ L _ _ _ p₀ S a i hT hap ha1 hqi hD4
  have hcls : L154Cls S 3 a i := ⟨Nat.prime_three, by norm_num, hT, hap, ha1, hqi⟩
  by_contra hcon
  refine l154d4_false_of_excl ?_ hD4
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  by_cases hA1 : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact l154d4_excl_typeA S hcls.prime hcls.torus hcls.pow hcls.ne_one i hA1 hqi
  by_cases hE6 : L154E6Class a i
  · exact l154d4_excl_e6Class S hcls.prime hcls.torus hcls.pow hcls.ne_one i hqi hE6
  cases τ with
  | G2 => exact (false_of_g2Class_nonAP hcls.prime S hpL hTp hcls.ne_one i hA1).elim
  | F4 => exact l154d4_excl_f4 S hcls hA1
  | D4 =>
    exact (hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (l154_rootCount_le_of_dShape_D4
      (l154_shape_D4 S hcls.prime hpL hTp i hA1)))).elim
  | E6 => exact l154d4_dispatch_E6 S hcls hA1 hE6 hcon
  | E7 => exact l154d4_dispatch_E7 S hcls hA1 hE6
  | E8 => exact l154d4_dispatch_E8 S hcls hA1 hE6

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
