module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed
public import CFSG.Goldschmidt.Steps.G53Tools
public import CFSG.GroupTheory.PCore.CommutingBalance
import CFSG.Adapters.GeneralizedFitting

public section

open CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GorensteinWalter
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IG512Proof

theorem gfs_top_eq (Y : Type) [Group Y] [Finite Y] :
    generalizedFittingSubgroupOf (⊤ : Subgroup Y) = CFSG.generalizedFitting Y :=
  CFSG.Adapters.generalizedFittingSubgroupOf_top_eq_foundations Y

theorem Fs_eq {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    Fs M = generalizedFittingSubgroupOf M := by
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq M, gfs_top_eq]
  rfl

theorem Fs_eq_Op_iff {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    Fs X = Op p X ↔ IsPGroup p ↥(generalizedFittingSubgroupOf X) := by
  rw [Fs_eq X]
  constructor
  · intro h
    have : generalizedFittingSubgroupOf X = qCoreOf X p := h
    rw [this]
    exact qCoreOf_isPGroup X p
  · intro hpg
    have hRA := generalizedFittingSubgroupOf_isNormalIn X
    apply le_antisymm
    · exact le_qCoreOf_of_normal_isPGroup X _ p hRA.1
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hRA.1).mpr (le_normalizer_of_isNormalIn hRA)) hpg
    · exact (qCoreOf_le_fittingSubgroupOf X p hp).trans (le_sup_left)

theorem isPGroup_gfs_inf_centralizer {G : Type} [Group G] [Finite G] {X U : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hX : IsPGroup p (generalizedFittingSubgroupOf X)) (hUX : U ≤ X)
    (hU : IsPGroup p U) :
    IsPGroup p (generalizedFittingSubgroupOf (X ⊓ Subgroup.centralizer (U : Set G))) := by
  have hX' : IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup X)) := by
    have e : generalizedFittingSubgroupOf (⊤ : Subgroup X) ≃* generalizedFittingSubgroupOf X :=
      ((generalizedFittingSubgroupOf (⊤ : Subgroup X)).equivMapOfInjective X.subtype
        X.subtype_injective).trans
        (MulEquiv.subgroupCongr (generalizedFittingSubgroupOf_subgroup_top_eq X))
    exact hX.of_equiv e.symm
  have hU' : IsPGroup p (U.subgroupOf X) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  have h := (bender1970_1_8_centralizerNormalizer_pGroup (G := X) p hp hX' _ hU').1
  have hmap := h.map X.subtype
  rw [CFSG.Walter.generalizedFittingSubgroupOf_map_subtype'] at hmap
  have hc : (Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X)).map X.subtype =
      X ⊓ Subgroup.centralizer (U : Set G) := by
    rw [CFSG.centralizer_subgroupOf_eq U X hUX, Subgroup.subgroupOf_map_subtype, inf_comm]
  rwa [hc] at hmap

theorem gfs_normalizer_pGroup_of_centralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {N P : Subgroup G} (hP : IsPGroup p ↥P) (hPN : P ≤ N)
    (hC : IsPGroup p ↥(generalizedFittingSubgroupOf (N ⊓ Subgroup.centralizer (P : Set G)))) :
    IsPGroup p ↥(generalizedFittingSubgroupOf (N ⊓ Subgroup.normalizer (P : Set G))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Y : Subgroup G := N ⊓ Subgroup.normalizer (P : Set G) with hYdef
  set C : Subgroup G := N ⊓ Subgroup.centralizer (P : Set G) with hCdef
  have hPY : P ≤ Y := le_inf hPN Subgroup.le_normalizer
  have hCY : C ≤ Y := inf_le_inf_left N (Subgroup.centralizer_le_normalizer (P : Set G))
  have hYN : Y ≤ N := inf_le_left
  have hYnorm : Y ≤ Subgroup.normalizer (P : Set G) := inf_le_right
  have hPnormY : (P.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPY]; exact hYnorm
  have hPq : P ≤ qCoreOf Y p := le_qCoreOf_of_normal_isPGroup Y P p hPY hPnormY hP
  have hPF : P ≤ CFSG.fittingSubgroupOf Y := hPq.trans (qCoreOf_le_fittingSubgroupOf Y p hp)
  have hStepB : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf Y q = ⊥ := by
    intro q hq hqp
    have : Fact q.Prime := ⟨hq⟩
    have hQnorm : IsNormalIn (qCoreOf Y q) Y := qCoreOf_normal_in Y q
    have hQq : IsPGroup q ↥(qCoreOf Y q) := qCoreOf_isPGroup Y q
    have hdisj : Disjoint P (qCoreOf Y q) :=
      IsPGroup.disjoint_of_ne p q (Ne.symm hqp) P (qCoreOf Y q) hP hQq
    have hQcent : qCoreOf Y q ≤ Subgroup.centralizer (P : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxY : x ∈ Y := hQnorm.1 hx
      have hyY : y ∈ Y := hPY hy
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ P := by
        have hxy : x * y * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hYnorm hxY) y).mp hy
        exact P.mul_mem hxy (P.inv_mem hy)
      have h2 : x * y * x⁻¹ * y⁻¹ ∈ qCoreOf Y q := by
        have : y * x⁻¹ * y⁻¹ ∈ qCoreOf Y q := hQnorm.2 y hyY x⁻¹ ((qCoreOf Y q).inv_mem hx)
        have h3 := (qCoreOf Y q).mul_mem hx this
        simpa [mul_assoc] using h3
      have h4 := Subgroup.disjoint_def.1 hdisj h1 h2
      have h5 : x * y = y * x := by
        have : x * y * x⁻¹ * y⁻¹ = 1 := h4
        calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
          _ = y * x := by rw [this, one_mul]
      exact h5.symm
    have hQC : qCoreOf Y q ≤ C := le_inf (hQnorm.1.trans hYN) hQcent
    have hCnorm : C ≤ Subgroup.normalizer (qCoreOf Y q : Set G) :=
      hCY.trans (le_normalizer_of_isNormalIn hQnorm)
    have hQCnorm : ((qCoreOf Y q).subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr hCnorm
    have hQle : qCoreOf Y q ≤ generalizedFittingSubgroupOf C :=
      (le_qCoreOf_of_normal_isPGroup C _ q hQC hQCnorm hQq).trans
        ((qCoreOf_le_fittingSubgroupOf C q hq).trans le_sup_left)
    have hQp : IsPGroup p ↥(qCoreOf Y q) := hC.to_le hQle
    have := IsPGroup.disjoint_of_ne q p hqp _ _ hQq hQp
    exact disjoint_self.1 this
  have hFle : CFSG.fittingSubgroupOf Y ≤ qCoreOf Y p := by
    rw [(show CFSG.fittingSubgroupOf Y = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf Y)]
    refine iSup_le fun q => ?_
    by_cases h : q.1.1 = p
    · rw [h]
    · rw [hStepB q.1.1 (Nat.prime_of_mem_primeFactors q.1.2) h]
      exact bot_le
  have hFp : IsPGroup p ↥(CFSG.fittingSubgroupOf Y) := (qCoreOf_isPGroup Y p).to_le hFle
  have hE : componentLayerOf Y = ⊥ := by
    refine eq_bot_iff.2 (sSup_le fun L hL => ?_)
    exfalso
    have hLcomm : ⁅L, CFSG.fittingSubgroupOf Y⁆ = ⊥ := component_centralizes_fittingSubgroupOf hL
    have hLcentP : L ≤ Subgroup.centralizer (P : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLcomm).trans (Subgroup.centralizer_le hPF)
    have hLC : L ≤ C := le_inf (hL.1.trans hYN) hLcentP
    have hLsub : (L.subgroupOf C).IsSubnormal := by
      have h := hL.2.1.comap (Subgroup.inclusion hCY)
      have heq : (L.subgroupOf Y).comap (Subgroup.inclusion hCY) = L.subgroupOf C := by
        ext x; simp [Subgroup.mem_subgroupOf]
      rwa [heq] at h
    have hLcomp : IsComponentOf L C := ⟨hLC, hLsub, hL.2.2⟩
    have hLle : L ≤ generalizedFittingSubgroupOf C :=
      (le_sSup (s := {E : Subgroup G | IsComponentOf E C}) hLcomp : L ≤ componentLayerOf C).trans le_sup_right
    have hLp : IsPGroup p ↥L := hC.to_le hLle
    exact not_isNilpotent_of_isQuasisimple L hL.2.2 hLp.isNilpotent
  show IsPGroup p ↥(generalizedFittingSubgroupOf Y)
  have : generalizedFittingSubgroupOf Y = CFSG.fittingSubgroupOf Y := by
    unfold generalizedFittingSubgroupOf; rw [hE, sup_bot_eq]; rfl
  rw [this]; exact hFp

theorem ig_5_12_thm : CFSG.GH74.GLS.Stage2.Bender.Thm2.IG_5_12 := by
  unfold CFSG.GH74.GLS.Stage2.Bender.Thm2.IG_5_12
  intro G _ _ p hp N P hP hPN
  have hPY : P ≤ N ⊓ Subgroup.normalizer (P : Set G) := le_inf hPN Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  · intro h
    rw [Fs_eq_Op_iff hp] at h ⊢
    exact Goldschmidt.G53.isPGroup_generalizedFitting_inf_normalizer hp h hPN hP
  · rw [Fs_eq_Op_iff hp, Fs_eq_Op_iff hp]
    constructor
    · intro h
      have := isPGroup_gfs_inf_centralizer hp h hPY hP
      have e : N ⊓ Subgroup.normalizer (P : Set G) ⊓ Subgroup.centralizer (P : Set G) =
          N ⊓ Subgroup.centralizer (P : Set G) := by
        ext x; simp only [Subgroup.mem_inf]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.centralizer_le_normalizer (P : Set G) h.2⟩, h.2⟩⟩
      rwa [e] at this
    · intro h
      exact gfs_normalizer_pGroup_of_centralizer hp hP hPN h

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IG512Proof

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

theorem ig_5_12_thm : IG_5_12 := IG512Proof.ig_5_12_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm2

