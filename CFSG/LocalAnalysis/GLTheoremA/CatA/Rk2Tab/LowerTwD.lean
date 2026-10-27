module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootGen
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
open CFSG.SectionRank.EvenCover CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartOne.KFU CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Blueprint.Multiplier
open CFSG.SignalizerFunctorTheorem.NonLocal
open scoped MatrixGroups

private theorem map_orthElementaryGroup_prodHom_le
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ}
    (qA : QuadraticForm F A) :
    (orthElementaryGroup (quadPlus r F)).map (prodHom (K := F) (r := r) A) ≤
      orthElementaryGroup (quadTail r qA) := by
  rw [orthElementaryGroup, orthElementaryGroup, Subgroup.map_le_iff_le_comap]
  refine elementaryGroup_le_of_eichler_mem ?_
  intro u w hu hw
  rw [Subgroup.mem_comap]
  change prodHom A (eichler (quadPlus r F) u w) ∈ elementaryGroup (quadTail r qA)
  rw [prodHom_apply, ← eichler_prod_fst]
  exact eichler_mem_elementaryGroup _ _ _

private theorem prodHom_injective
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ} :
    Function.Injective (prodHom (K := F) (r := r) A) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro v
  have h' := congrArg
    (fun e : ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A) => e (v, 0)) hgh
  rw [prodHom_apply, prodHom_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.prodCongr_apply] at h'
  exact (Prod.ext_iff.1 h').1

private noncomputable def prodHomElem
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ}
    (qA : QuadraticForm F A) :
    orthElementaryGroup (quadPlus r F) →* orthElementaryGroup (quadTail r qA) :=
  ((prodHom (K := F) (r := r) A).comp (orthElementaryGroup (quadPlus r F)).subtype).codRestrict _
    (fun g : orthElementaryGroup (quadPlus r F) =>
      map_orthElementaryGroup_prodHom_le (r := r) (qA := qA)
        (Subgroup.mem_map_of_mem (prodHom (K := F) (r := r) A) g.2))

private theorem prodHomElem_injective
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ}
    (qA : QuadraticForm F A) : Function.Injective (prodHomElem (r := r) qA) := by
  intro x y hxy
  have h : prodHom (K := F) (r := r) A (x : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)) =
      prodHom (K := F) (r := r) A (y : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)) := by
    simpa only [prodHomElem, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype] using congrArg
        (fun z : orthElementaryGroup (quadTail r qA) =>
          (z : ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A))) hxy
  exact Subtype.ext (prodHom_injective (A := A) (r := r) h)

private noncomputable def elementaryGroupEquivStatedOmega
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F}
    (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    elementaryGroup Q ≃* StatedOmega Q₀ :=
  ((toLinEquiv ι F).symm.subgroupMap (elementaryGroup Q)).trans
    (MulEquiv.subgroupCongr (statedOmega_eq_map_elementaryGroup hQ hE).symm)

private noncomputable def tailToMinusEquiv
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (ℓ : ℕ) (hℓ : 4 ≤ ℓ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    orthElementaryGroup (quadTail (ℓ - 1) (minusTailForm (K := F) b c)) ≃*
      orthElementaryGroup (quadMinus ℓ F b c) :=
  elementaryIsometryEquiv (minusTailIsometry ℓ F b c)

private noncomputable def minusToStatedOmegaEquiv
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (ℓ : ℕ) (hℓ : 4 ≤ ℓ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    orthElementaryGroup (quadMinus ℓ F b c) ≃*
      StatedOmega (StatedQuadMinus ℓ F b c) :=
  elementaryGroupEquivStatedOmega (coe_quadMinus ℓ F b c)
    (commutator_orthogonalGroup_quadMinus hℓ hirr)

private noncomputable def statedOmegaToProjEquiv
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (ℓ : ℕ) (hℓ : 4 ≤ ℓ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus ℓ F b c) ≃*
      StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)) := by
  classical
  have hbot : (StatedScalars (Fin (ℓ - 1) ⊕ Fin (ℓ - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus ℓ F b c)) = ⊥ := by
    refine statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus ℓ F b c) (Q₀ := StatedQuadMinus ℓ F b c) (coe_quadMinus ℓ F b c) ?_
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
    rw [quadMinus_apply]
    simp
  exact equivProjOfScalarsBot _ hbot

private noncomputable def twDModelHom
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (ℓ : ℕ) (hℓ : 4 ≤ ℓ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    orthElementaryGroup (quadPlus (ℓ - 1) F) →*
      StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)) :=
  (statedOmegaToProjEquiv F ℓ hℓ b c hirr).toMonoidHom.comp
    ((minusToStatedOmegaEquiv F ℓ hℓ b c hirr).toMonoidHom.comp
      ((tailToMinusEquiv F ℓ hℓ b c hirr).toMonoidHom.comp
        (prodHomElem (F := F) (r := ℓ - 1) (minusTailForm (K := F) b c))))

private theorem twDModelHom_injective
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (ℓ : ℕ) (hℓ : 4 ≤ ℓ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (twDModelHom F ℓ hℓ b c hirr) := by
  intro x y hxy
  exact prodHomElem_injective (r := ℓ - 1) (minusTailForm (K := F) b c)
    ((tailToMinusEquiv F ℓ hℓ b c hirr).injective
      ((minusToStatedOmegaEquiv F ℓ hℓ b c hirr).injective
        ((statedOmegaToProjEquiv F ℓ hℓ b c hirr).injective hxy)))

private theorem posUnip_subgroupOf_ne_bot
    {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ} (hr : 2 ≤ r) :
    (posUnip r F).subgroupOf (orthElementaryGroup (quadPlus r F)) ≠ ⊥ := by
  intro h
  have hc : Nat.card ((posUnip r F).subgroupOf (orthElementaryGroup (quadPlus r F))) =
      Nat.card (posUnip r F) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (posUnip_le_orthElementaryGroup (r := r) (K := F))).toEquiv
  rw [h, Subgroup.card_bot, card_posUnip (r := r) (K := F)] at hc
  have h1 : 1 < Nat.card F := Finite.one_lt_card (α := F)
  have hrr : 1 ≤ r * (r - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : Nat.card F ^ 1 ≤ Nat.card F ^ (r * (r - 1)) :=
    Nat.pow_le_pow_right (by omega) hrr
  rw [pow_one] at h3
  omega

private theorem isPGroup_posUnip_subgroupOf
    {F : Type} [Field F] [Finite F] [CharP F 2] (r : ℕ) :
    IsPGroup 2 ((posUnip r F).subgroupOf (orthElementaryGroup (quadPlus r F))) := by
  have hpos := (orthogonal_geometry_split_positive_unipotent_matrices
    (r := r) (K := F)).2.2.2.2.2.2.2.2.2.2 2
      (inferInstance : CharP F 2) (inferInstance : Finite F)
  exact IsPGroup.of_equiv hpos.2.1
    (Subgroup.subgroupOfEquivOfLe posUnip_le_orthElementaryGroup).symm

theorem exists_isElemAbelian_torus_statedOmegaMinus
    {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ r : ℕ} (hℓ : 4 ≤ ℓ)
    (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card F - 1) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ E X : Subgroup (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c))),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian r E ∧ Nat.card E = r ^ (ℓ - 1) ∧
        E ≤ Subgroup.normalizer
          (X : Set (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)))) := by
  classical
  obtain ⟨E₀, hE₀, hE₀card, hE₀norm⟩ :=
    exists_isElemAbelian_torus_quadPlus (F := F) (ℓ := ℓ - 1) (r := r)
      (by omega) hr hr2 hdvd
  let α := twDModelHom F ℓ hℓ b c hirr
  have hα : Function.Injective α := twDModelHom_injective F ℓ hℓ b c hirr
  let X₀ : Subgroup (orthElementaryGroup (quadPlus (ℓ - 1) F)) :=
    (posUnip (ℓ - 1) F).subgroupOf (orthElementaryGroup (quadPlus (ℓ - 1) F))
  have hX₀ : X₀ ≠ ⊥ := posUnip_subgroupOf_ne_bot (r := ℓ - 1) (by omega)
  have hX₀2 : IsPGroup 2 X₀ := isPGroup_posUnip_subgroupOf (r := ℓ - 1)
  refine ⟨E₀.map α, X₀.map α, ?_, hX₀2.map α,
    CFSG.SectionRank.isElemAbelian_map hE₀ α, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective X₀ hα]
    exact hX₀
  · rw [Subgroup.card_map_of_injective hα, hE₀card]
  · exact (Subgroup.map_mono hE₀norm).trans (Subgroup.le_normalizer_map α)


theorem card_griessHopfMultiplier_pomegaMinus_eq_one {X : Type} [Group X] {ℓ n : ℕ}
    (hn : 1 ≤ n) (h : StatedClassicalModel X .POmegaMinus ℓ 2 n) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaMinus_row h
  have hgen : genericOrders .POmegaMinus ℓ 2 n = (1, 1) := by
    simp only [genericOrders]
    rw [show ((2 : ℕ) ^ n) ^ ℓ = 2 ^ (n * ℓ) by rw [← pow_mul]]
    have hℓ0 : ℓ ≠ 0 := by have := h.1.2.2; omega
    have hodd : Odd (2 ^ (n * ℓ) + 1) :=
      Even.add_one (even_iff_two_dvd.mpr (dvd_pow_self 2 (n := n * ℓ)
        (Nat.mul_ne_zero (by omega) hℓ0)))
    have hco : Nat.Coprime 4 (2 ^ (n * ℓ) + 1) := by
      have h4 := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
      simpa using h4
    rw [show Nat.gcd 4 (2 ^ (n * ℓ) + 1) = 1 from Nat.coprime_iff_gcd_eq_one.mp hco]
  have hex : exceptionalOrders .POmegaMinus ℓ 2 n = (1, 1) := rfl
  rw [Nat.card_congr e.toEquiv,
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hgen, hex]
  norm_num


theorem rk2_low_twd_ge (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twD) (hr : 4 ≤ lab.rank) (hn : 2 ≤ lab.n) :
    lab.rank - 1 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at htag hr hn
  subst htag
  have ht : markTag (⟨.twD, ℓ, n⟩ : GLALabel) = .POmegaMinus := by
    simp [CFSG.StandardType.markTag, show ℓ ≠ 2 by omega, show ℓ ≠ 3 by omega]
  have hrk : markRank (⟨.twD, ℓ, n⟩ : GLALabel) = ℓ := by
    simp [CFSG.StandardType.markRank, show ℓ ≠ 2 by omega, show ℓ ≠ 3 by omega]
  have hch : markChar (⟨.twD, ℓ, n⟩ : GLALabel) = 2 := by
    simp [CFSG.StandardType.markChar]
  have hdg : markDeg (⟨.twD, ℓ, n⟩ : GLALabel) = n := by
    simp [CFSG.StandardType.markDeg, show ℓ ≠ 2 by omega]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, b, c, hirr, ⟨θ⟩⟩ :=
    hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hn1 : 1 ≤ n := by omega
  have h3 : 3 ≤ Nat.card F - 1 := by
    rw [hcard]
    calc 3 = 2 ^ 2 - 1 := by norm_num
      _ ≤ 2 ^ n - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hn) 1
  obtain ⟨r, hrr, hrdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F - 1) (by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hodd : Odd (Nat.card F - 1) := by
      rw [hcard]
      have hle : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hev : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      exact Nat.Even.sub_odd hle hev odd_one
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hrdvd)
  have hZ : ¬ r ∣ Nat.card (Subgroup.center K) := by
    have hSC : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaMinus ℓ 2 n :=
      hM'.statedClassicalModel (by decide)
    have hmul : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) = 1 :=
      card_griessHopfMultiplier_pomegaMinus_eq_one hn1 hSC
    have hdvd := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
      (MulEquiv.refl _)
    rw [hmul] at hdvd
    exact fun h => hrr.ne_one (Nat.dvd_one.mp (h.trans hdvd))
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_isElemAbelian_torus_statedOmegaMinus (F := F) (ℓ := ℓ) (r := r) hr hrr hr2 hrdvd
      b c hirr
  exact le_evenRank_of_center_quotient θ hrr hr2 hZ hX hX2 hE hEcard hXE


private theorem card_griess_psl_two_dvd_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : StatedClassicalModel X .PSL 2 2 (2 * n)) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 2 := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h
  rw [Nat.card_congr e.toEquiv,
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
  have hg : genericOrders .PSL 2 2 (2 * n) = (1, 1) := by
    simp only [genericOrders]
    have hodd : Odd (2 ^ (2 * n) - 1) := by
      have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
      have hev : Even (2 ^ (2 * n)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      exact Nat.Even.sub_odd h1 hev odd_one
    have hco : Nat.Coprime 2 (2 ^ (2 * n) - 1) := Nat.coprime_two_left.mpr hodd
    simpa using hco
  have he : exceptionalOrders .PSL 2 2 (2 * n) = (1, 1) ∨
      exceptionalOrders .PSL 2 2 (2 * n) = (2, 1) := by
    by_cases h2 : 2 * n = 2
    · right
      simp [exceptionalOrders, h2]
    · left
      simp [exceptionalOrders, h2]
  rw [hg]
  rcases he with he | he <;> rw [he] <;> norm_num

private theorem spSiegel_one_ne_bot {F : Type} [Field F] [Finite F] [CharP F 2] :
    spSiegel 1 F ≠ ⊥ := by
  rw [← Subgroup.one_lt_card_iff_ne_bot, card_spSiegel]
  rw [show 1 * (1 + 1) / 2 = 1 by norm_num, pow_one]
  exact Finite.one_lt_card (α := F)

private theorem isPGroup_spSiegel_one {F : Type} [Field F] [Finite F] [CharP F 2] :
    IsPGroup 2 (spSiegel 1 F) := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  refine IsPGroup.of_card (n := k) ?_
  rw [card_spSiegel, show 1 * (1 + 1) / 2 = 1 by norm_num, pow_one,
    Nat.card_eq_fintype_card, hk]

private noncomputable def projSL2EquivSpOne (F : Type) [Field F] [CharP F 2] :
    StatedProj (StatedSL 2 F) ≃* StatedSp 1 F :=
  (equivProjOfScalarsBot (StatedSL 2 F)
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := F))).symm.trans
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm.trans
      (longBlockEquivOne (K := F)))

theorem rk2_low_twd_two (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twD) (hr : lab.rank = 2) :
    lab.rank - 1 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at htag hr
  subst htag
  subst hr
  have hn1 : 1 ≤ n := hlab.1
  have ht : markTag (⟨.twD, 2, n⟩ : GLALabel) = .PSL := by
    simp [CFSG.StandardType.markTag]
  have hrk : markRank (⟨.twD, 2, n⟩ : GLALabel) = 2 := by
    simp [CFSG.StandardType.markRank]
  have hch : markChar (⟨.twD, 2, n⟩ : GLALabel) = 2 := by
    simp [CFSG.StandardType.markChar]
  have hdg : markDeg (⟨.twD, 2, n⟩ : GLALabel) = 2 * n := by
    simp [CFSG.StandardType.markDeg]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hF : Nat.card F = 4 ^ n := by
    rw [hcard, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h3dvd : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
  obtain ⟨E, hE, hEcard, hEnorm⟩ :=
    exists_isElemAbelian_torus_statedSp (F := F) (ℓ := 1) (r := 3)
      (by norm_num) Nat.prime_three (by norm_num) h3dvd
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hdvdZ : Nat.card (Subgroup.center K) ∣
        Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
        (MulEquiv.refl _)
    have hSC : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 (2 * n) :=
      hM'.statedClassicalModel (by decide)
    have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) ∣ 2 :=
      card_griess_psl_two_dvd_two hn1 hSC
    have h32 : 3 ∣ 2 := hdiv.trans (hdvdZ.trans h2)
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h32
    omega
  refine le_evenRank_of_center_quotient (e.trans (projSL2EquivSpOne F))
    Nat.prime_three (by norm_num) hZ (spSiegel_one_ne_bot (F := F))
      (isPGroup_spSiegel_one (F := F)) hE ?_ hEnorm
  simpa using hEcard

end CFSG.LocalAnalysis.GLTheoremA
