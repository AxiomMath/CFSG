module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin9
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace LinEngine

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {p : ℕ}

private theorem blockEndSL_mem_pow [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p}
    (x : SpecialLinearGroup F V) (hx : (x : V ≃ₗ[F] V) = blockEnd A hp hpF hA t ht D) :
    x ^ p = 1 := by
  refine Subtype.ext ?_
  change (x : V ≃ₗ[F] V) ^ p = 1
  rw [hx]
  exact blockEnd_pow A hp hpF hA t ht D

private theorem blockEndSL_mem_ne_one [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p}
    (hD : blockSpace A D.1 ≠ ⊥) (x : SpecialLinearGroup F V)
    (hx : (x : V ≃ₗ[F] V) = blockEnd A hp hpF hA t ht D) : x ≠ 1 := by
  intro h
  have hval : blockEnd A hp hpF hA t ht D = 1 := by
    rw [← hx]
    exact congrArg (fun z : SpecialLinearGroup F V => (z : V ≃ₗ[F] V)) h
  exact hD (eq_one_of_blockEnd_eq_one A hp hpF hA t ht hval)

private theorem blockEndSL_mem_orderOf [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p}
    (hD : blockSpace A D.1 ≠ ⊥) (x : SpecialLinearGroup F V)
    (hx : (x : V ≃ₗ[F] V) = blockEnd A hp hpF hA t ht D) : orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (blockEndSL_mem_pow A hp hpF hA t ht x hx)
    (blockEndSL_mem_ne_one A hp hpF hA t ht hD x hx)

private theorem blockEndSL_mem_notMem_zpowers [Fintype F] (A : Subgroup (V ≃ₗ[F] V))
    [Fintype A] (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D E : Hyperplane A p} (hDE : D ≠ E)
    (hE : blockSpace A E.1 ≠ ⊥) (x y : SpecialLinearGroup F V)
    (hx : (x : V ≃ₗ[F] V) = blockEnd A hp hpF hA t ht D)
    (hy : (y : V ≃ₗ[F] V) = blockEnd A hp hpF hA t ht E) :
    y ∉ Subgroup.zpowers x := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply blockEnd_notMem_zpowers A hp hpF hA t ht hDE hE
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have hval := congrArg (fun z : SpecialLinearGroup F V => (z : V ≃ₗ[F] V)) hk
  change (x : V ≃ₗ[F] V) ^ k = (y : V ≃ₗ[F] V) at hval
  rwa [hx, hy] at hval

private theorem centralizer_singleton_eq_blockEndSL [Fintype F] (A : Subgroup (V ≃ₗ[F] V))
    [Fintype A] (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1) {D : Hyperplane A p} (x : SpecialLinearGroup F V)
    (hx : (x : V ≃ₗ[F] V) = blockEnd A hp hpF hA t ht D) :
    Subgroup.centralizer ({x} : Set (SpecialLinearGroup F V)) =
      Subgroup.centralizer ({blockEndSL (A := A) hp hpF hA t ht hpd D} :
        Set (SpecialLinearGroup F V)) := by
  ext g
  rw [mem_centralizer_blockEndSL_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h := congrArg (fun z : SpecialLinearGroup F V => (z : V ≃ₗ[F] V)) hg
    simp only [SpecialLinearGroup.coe_mul] at h
    rwa [hx] at h
  · intro hg
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul]
    rw [hx]
    exact hg

variable [Fintype F]
variable {n q d : ℕ}

theorem exists_blockElements_quasisimple {A : Subgroup (SpecialLinearGroup F V)}
    {Agl : Subgroup (V ≃ₗ[F] V)} [Fintype ↥Agl]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (hAgl : IsElemAbelian p Agl)
    (t : Hyperplane Agl p → ↥Agl) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1)
    (hmap : Agl = A.map SpecialLinearGroup.toLinearEquiv)
    (hmemAgl : ∀ D, blockEnd Agl hp hpF hAgl t ht D ∈ Agl)
    {D₁ D₂ D₃ : Hyperplane Agl p} (hD₁₃ : D₁ ≠ D₃) (hD₂₃ : D₂ ≠ D₃)
    (hD₃ : blockSpace Agl D₃.1 ≠ ⊥)
    (hfixed4 : 4 ≤ Module.finrank F
      ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)))
    (hcard : Fintype.card F = 2 ^ n) (hn1 : 1 ≤ n)
    (hm0 : 2 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    (hsmall : 2 ≤ n ∨ 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n) :
    ∃ t₁ t₂ : SpecialLinearGroup F V,
      (t₁ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₁ ∧
      (t₂ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₂ ∧
      CFSG.IsQuasisimple
        (SpecialLinearGroup F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁))) ∧
      CFSG.IsQuasisimple (SpecialLinearGroup F
        ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
          fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂))) ∧
      t₁ ∈ A ∧ t₂ ∈ A := by
  classical
  have hD₃le : Module.finrank F ↥(blockSpace Agl D₃.1) ≤
      Module.finrank F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
        fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)) :=
    finrank_blockSpace_le_finrank_fixedByEnd_inf (A := Agl) hp hpF hAgl t ht
      (D := D₁) (E := D₂) (G := D₃) hD₁₃.symm hD₂₃.symm
  have hm0dvd : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∣
      Module.finrank F ↥(blockSpace Agl D₃.1) :=
    dvd_finrank_blockSpace (A := Agl) hp hp2 hpF hAgl t ht hcard hn1 D₃ hD₃
  have hblockpos : 0 < Module.finrank F ↥(blockSpace Agl D₃.1) := by
    by_contra h
    exact hD₃ (Submodule.finrank_eq_zero.mp (by omega))
  have hm0le : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≤
      Module.finrank F ↥(blockSpace Agl D₃.1) := Nat.le_of_dvd hblockpos hm0dvd
  have hdim3 : 2 ≤ Module.finrank F ↥(blockSpace Agl D₃.1) := le_trans hm0 hm0le
  have hdimL : 2 ≤ Module.finrank F
      ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
        fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)) := le_trans hdim3 hD₃le
  have hW1 : 3 ≤ Module.finrank F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)) :=
    le_trans (by norm_num) hfixed4
  have hqJ : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁))) := by
    haveI : Module.Free F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)) :=
      Module.Free.of_divisionRing F _
    haveI : Module.Finite F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)) :=
      Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
    exact isQuasisimple_specialLinearGroup_of_three_le (Module.finBasis F _) hW1
  have hqL : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
        fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂))) := by
    haveI : Module.Free F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
        fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)) := Module.Free.of_divisionRing F _
    haveI : Module.Finite F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
        fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)) :=
      Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
    by_cases hL3 : 3 ≤ Module.finrank F
        ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
          fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂))
    · exact isQuasisimple_specialLinearGroup_of_three_le (Module.finBasis F _) hL3
    · have hL2 : Module.finrank F
          ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
            fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)) = 2 := by omega
      have h4 : 4 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card, hcard]
        rcases Nat.lt_or_ge n 2 with hn | hn
        · have hn₁ : n = 1 := by omega
          have hm03 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n := by
            rcases hsmall with h2n | h3m0
            · omega
            · exact h3m0
          have h3block : 3 ≤ Module.finrank F ↥(blockSpace Agl D₃.1) :=
            le_trans hm03 hm0le
          omega
        · exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
      have hb : Module.Basis (Fin 2) F
          ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
            fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)) :=
        (Module.finBasis F _).reindex (finCongr hL2)
      exact isQuasisimple_specialLinearGroup_of_two hb h4
  set t₁ : SpecialLinearGroup F V :=
    ⟨blockEnd Agl hp hpF hAgl t ht D₁,
      blockEnd_mem_specialLinear Agl hp hpF hAgl t ht hpd D₁⟩ with ht₁def
  set t₂ : SpecialLinearGroup F V :=
    ⟨blockEnd Agl hp hpF hAgl t ht D₂,
      blockEnd_mem_specialLinear Agl hp hpF hAgl t ht hpd D₂⟩ with ht₂def
  have ht₁coe : (t₁ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₁ := by
    rw [ht₁def]
  have ht₂coe : (t₂ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₂ := by
    rw [ht₂def]
  have hmemA_iff : ∀ x : SpecialLinearGroup F V, x ∈ A ↔ (x : V ≃ₗ[F] V) ∈ Agl := by
    intro x
    rw [hmap]
    constructor
    · intro hx
      exact Subgroup.mem_map_of_mem SpecialLinearGroup.toLinearEquiv hx
    · intro hx
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
      have : a = x := Subtype.ext hax
      simpa [this] using ha
  have ht₁A : t₁ ∈ A := (hmemA_iff t₁).2 (by simpa [ht₁coe] using hmemAgl D₁)
  have ht₂A : t₂ ∈ A := (hmemA_iff t₂).2 (by simpa [ht₂coe] using hmemAgl D₂)
  exact ⟨t₁, t₂, ht₁coe, ht₂coe, hqJ, hqL, ht₁A, ht₂A⟩

private theorem exists_pWitnesses {A : Subgroup (SpecialLinearGroup F V)}
    {Agl : Subgroup (V ≃ₗ[F] V)} [Fintype ↥Agl]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAgl : IsElemAbelian p Agl)
    (hAdet : Agl ≤ LinearEquiv.det.ker) (hpd : ¬ p ∣ Fintype.card F - 1)
    (hkAgl : Nat.card ↥Agl = p ^ CFSG.Open.pRank p A)
    (t : Hyperplane Agl p → ↥Agl) (ht : ∀ D, t D ∉ D.1)
    {D₁ D₂ : Hyperplane Agl p} (hD₁ : blockSpace Agl D₁.1 ≠ ⊥)
    (hD₂ : blockSpace Agl D₂.1 ≠ ⊥) (hD₁₂ : D₁ ≠ D₂)
    (h3 : 3 ≤ CFSG.Open.pRank p A) (hAe : IsElemAbelian p A)
    {t₁ t₂ : SpecialLinearGroup F V}
    (ht₁coe : (t₁ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₁)
    (ht₂coe : (t₂ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₂)
    (ht₁A : t₁ ∈ A) (ht₂A : t₂ ∈ A)
    (hqJ : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁))))
    (hqL : CFSG.IsQuasisimple (SpecialLinearGroup F
      ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
        fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)))) :
    ∃ Dgrp Egrp J : Subgroup (SpecialLinearGroup F V),
      Dgrp ≤ Egrp ∧ Egrp ≤ A ∧ Nat.card ↥Dgrp = p ∧ Nat.card ↥Egrp = p ^ 2 ∧
      GLAPComponent p (Subgroup.centralizer (Dgrp : Set (SpecialLinearGroup F V))) J ∧
      A ≤ Subgroup.normalizer (J : Set (SpecialLinearGroup F V)) ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (Egrp : Set (SpecialLinearGroup F V))) ≠ ⊥ ∧
      Subgroup.centralizer (Dgrp : Set (SpecialLinearGroup F V)) =
        Subgroup.centralizer ({t₁} : Set (SpecialLinearGroup F V)) ∧
      J ≤ Subgroup.centralizer ({t₁} : Set (SpecialLinearGroup F V)) ∧
      J = Jsub Agl hp hpF hAgl t ht D₁ := by
  classical
  set Dgrp : Subgroup (SpecialLinearGroup F V) := Subgroup.zpowers t₁ with hDgrp
  set Egrp : Subgroup (SpecialLinearGroup F V) :=
    Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hEgrp
  have hDcard : Nat.card ↥Dgrp = p := by
    rw [hDgrp, Nat.card_zpowers]
    exact blockEndSL_mem_orderOf Agl hp hpF hAgl t ht hD₁ t₁ ht₁coe
  have hDE : Dgrp ≤ Egrp := by rw [hDgrp, hEgrp]; exact le_sup_left
  have hEA : Egrp ≤ A := by
    rw [hEgrp]
    exact sup_le (Subgroup.zpowers_le.mpr ht₁A) (Subgroup.zpowers_le.mpr ht₂A)
  have hcomm : ∀ x ∈ Subgroup.zpowers t₁, ∀ y ∈ Subgroup.zpowers t₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (show Commute t₁ t₂ from hAe.comm ht₁A ht₂A).zpow_zpow i j
  have hbain : t₂ ∉ Subgroup.zpowers t₁ :=
    blockEndSL_mem_notMem_zpowers Agl hp hpF hAgl t ht hD₁₂ hD₂ t₁ t₂ ht₁coe ht₂coe
  have hEcard : Nat.card ↥Egrp = p ^ 2 := by
    rw [hEgrp]
    exact card_sup_zpowers_eq_prime_sq hp
      (blockEndSL_mem_pow Agl hp hpF hAgl t ht t₁ ht₁coe)
      (blockEndSL_mem_pow Agl hp hpF hAgl t ht t₂ ht₂coe)
      (blockEndSL_mem_ne_one Agl hp hpF hAgl t ht hD₁ t₁ ht₁coe)
      (blockEndSL_mem_ne_one Agl hp hpF hAgl t ht hD₂ t₂ ht₂coe)
      hcomm hbain
  set J : Subgroup (SpecialLinearGroup F V) := Jsub Agl hp hpF hAgl t ht D₁ with hJdef
  have hJleCent : J ≤ Subgroup.centralizer ({t₁} : Set (SpecialLinearGroup F V)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hc := (mem_Jsub.mp hg).2 (blockEnd Agl hp hpF hAgl t ht D₁) (Set.mem_singleton _)
    simpa [ht₁coe] using hc
  have hcentD : Subgroup.centralizer (Dgrp : Set (SpecialLinearGroup F V)) =
      Subgroup.centralizer ({t₁} : Set (SpecialLinearGroup F V)) := by
    rw [hDgrp, CFSG.centralizer_zpowers_eq_centralizer_singleton]
  have hcomp : GLAPComponent p
      (Subgroup.centralizer (Dgrp : Set (SpecialLinearGroup F V))) J := by
    rw [hcentD, hJdef,
      centralizer_singleton_eq_blockEndSL (A := Agl) hp hpF hAgl t ht hpd t₁ ht₁coe]
    exact glaPComponent_Jsub (A := Agl) hp hpF hAgl t ht hAdet hpd
      (k := CFSG.Open.pRank p A) hkAgl h3 D₁ hqJ
  have hJn : (J.subgroupOf (Subgroup.centralizer
      ({t₁} : Set (SpecialLinearGroup F V)))).Normal := by
    rw [hJdef,
      centralizer_singleton_eq_blockEndSL (A := Agl) hp hpF hAgl t ht hpd t₁ ht₁coe]
    exact normal_Jsub (A := Agl) hp hpF hAgl t ht hpd D₁
  have hAJ : A ≤ Subgroup.normalizer (J : Set (SpecialLinearGroup F V)) := by
    have hcentnorm : Subgroup.centralizer ({t₁} : Set (SpecialLinearGroup F V)) ≤
        Subgroup.normalizer (J : Set (SpecialLinearGroup F V)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJleCent).mp hJn
    intro a ha
    apply hcentnorm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAe.comm ha ht₁A
  have hcentE : Subgroup.centralizer (Egrp : Set (SpecialLinearGroup F V)) =
      Subgroup.centralizer ({t₁} : Set (SpecialLinearGroup F V)) ⊓
        Subgroup.centralizer ({t₂} : Set (SpecialLinearGroup F V)) := by
    rw [hEgrp, CFSG.centralizer_sup_zpowers_eq,
      CFSG.centralizer_zpowers_eq_centralizer_singleton]
  have hinfJ : J ⊓ Subgroup.centralizer (Egrp : Set (SpecialLinearGroup F V)) =
      J ⊓ Subgroup.centralizer ({t₂} : Set (SpecialLinearGroup F V)) := by
    rw [hcentE, ← inf_assoc, inf_eq_left.mpr hJleCent]
  have hlay : GLAPLayer p
      (J ⊓ Subgroup.centralizer (Egrp : Set (SpecialLinearGroup F V))) ≠ ⊥ := by
    rw [hinfJ, hJdef,
      centralizer_singleton_eq_blockEndSL (A := Agl) hp hpF hAgl t ht hpd t₂ ht₂coe]
    exact glaPLayer_Jsub_inf_centralizer (A := Agl) hp hpF hAgl t ht hAdet hpd
      (k := CFSG.Open.pRank p A) hkAgl h3 hD₁₂ hqL
  exact ⟨Dgrp, Egrp, J, hDE, hEA, hDcard, hEcard, hcomp, hAJ, hlay, hcentD, hJleCent, hJdef⟩

theorem concl165Avoid_of_blockData {A : Subgroup (SpecialLinearGroup F V)}
    {Agl : Subgroup (V ≃ₗ[F] V)} [Fintype ↥Agl] [CharP F 2]
    [Finite (SpecialLinearGroup F V)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAgl : IsElemAbelian p Agl)
    (hAdet : Agl ≤ LinearEquiv.det.ker) (hpd : ¬ p ∣ Fintype.card F - 1)
    (hkAgl : Nat.card ↥Agl = p ^ CFSG.Open.pRank p A)
    (t : Hyperplane Agl p → ↥Agl) (ht : ∀ D, t D ∉ D.1)
    {D₁ D₂ : Hyperplane Agl p} (hD₁ : blockSpace Agl D₁.1 ≠ ⊥)
    (hD₂ : blockSpace Agl D₂.1 ≠ ⊥) (hD₁₂ : D₁ ≠ D₂)
    (hfixed : Module.finrank F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)) =
      Module.finrank F V - Module.finrank F ↥(blockSpace Agl D₁.1))
    (hthree : 3 * Module.finrank F ↥(blockSpace Agl D₁.1) ≤ Module.finrank F V)
    (hfixed4 : 4 ≤ Module.finrank F
      ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)))
    (hV : Module.finrank F V = d) (hcard : Fintype.card F = 2 ^ n)
    (hsmall : 2 ≤ n ∨ 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    (hm0 : 2 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    (hd : 3 * CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≤ d)
    (h3 : 3 ≤ CFSG.Open.pRank p A) (hq : q.Prime)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (hAe : IsElemAbelian p A)
    {t₁ t₂ : SpecialLinearGroup F V}
    (ht₁coe : (t₁ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₁)
    (ht₂coe : (t₂ : V ≃ₗ[F] V) = blockEnd Agl hp hpF hAgl t ht D₂)
    (ht₁A : t₁ ∈ A) (ht₂A : t₂ ∈ A)
    (hqJ : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁))))
    (hqL : CFSG.IsQuasisimple (SpecialLinearGroup F
      ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁) ⊓
        fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₂)))) :
    Concl165Avoid (SpecialLinearGroup F V) p q A
      (Subgroup.center (SpecialLinearGroup F V)) := by
  classical
  obtain ⟨Dgrp, Egrp, J, hDE, hEA, hDcard, hEcard, hcomp, hAJ, hlay, hcentD, hJleCent, hJdef⟩ :=
    exists_pWitnesses (A := A) (Agl := Agl) (D₁ := D₁) (D₂ := D₂) hp hpF hAgl hAdet hpd
      hkAgl t ht hD₁ hD₂ hD₁₂ h3 hAe ht₁coe ht₂coe ht₁A ht₂A hqJ hqL
  obtain ⟨Q, hQJ, hQea, hQrank⟩ : ∃ Q : Subgroup (SpecialLinearGroup F V),
      Q ≤ J ∧ IsElemAbelian q Q ∧ 3 ≤ CFSG.Open.pRank q Q := by
    rcases hqdiv with hqdvd | ⟨hn, hq3⟩
    · rw [hJdef]
      exact exists_elemAbelian_q_Jsub_of_split (A := Agl) hp hpF hAgl t ht hq
        (by rwa [hcard]) D₁ hfixed4
    · subst hn
      subst hq3
      have hfixed6 : 6 ≤ Module.finrank F
          ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)) := by
        rw [hfixed, hV]
        have hm03 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p 1 := by
          rcases hsmall with h2n | h3m0
          · omega
          · exact h3m0
        have hd9 : 9 ≤ d := by omega
        omega
      rw [hJdef]
      exact exists_elemAbelian_three_Jsub_of_f2 (A := Agl) hp hpF hAgl t ht D₁ hfixed6
  have hQFD : Q ≤ Subgroup.centralizer (Dgrp : Set (SpecialLinearGroup F V)) := by
    rw [hcentD]
    exact hQJ.trans hJleCent
  have hQFJ : Q ≤ Subgroup.normalizer (J : Set (SpecialLinearGroup F V)) :=
    hQJ.trans Subgroup.le_normalizer
  have hQFZ : Q ⊓ Subgroup.center (SpecialLinearGroup F V) = ⊥ := by
    rw [hJdef] at hQJ
    exact inf_center_eq_bot_of_le_Jsub (A := Agl) hp hpF hAgl t ht hD₁ hQJ
  exact ⟨Dgrp, Egrp, Q, J, hDE, hEA, hDcard, hEcard, hcomp, hAJ, hlay,
    hQFD, hQea, hQFJ, hQrank, hQFZ⟩

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
