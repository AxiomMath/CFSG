module

public import CFSG.GH74.Generic.S1.Exo.SetupCore
public import CFSG.GH74.Generic.S1.Exo.Growth

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem iso_xbar_eq_neg (mo : ModelOps S) {y : G} (D : LayerData y S) (hy : orderOf y = 2)
    (hxK : xbar y ∈ D.K) : D.iso ⟨xbar y, hxK⟩ = mo.neg := by
  have hz : (⟨xbar y, hxK⟩ : ↥D.K) ∈ Subgroup.center ↥D.K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm y (g : CentralizerBar y))
  have h1 := (mem_center_iff_of_mulEquiv D.iso _).2 hz
  rcases (mo.neg_center _).1 h1 with h | h
  · exfalso
    have : (⟨xbar y, hxK⟩ : ↥D.K) = 1 := D.iso.injective (by rw [h, map_one])
    exact xbar_ne_one hy (congrArg Subtype.val this)
  · exact h

theorem ι_neg_eq (mo : ModelOps S) {y : G} (D : LayerData y S) (hy : orderOf y = 2)
    (hxK : xbar y ∈ D.K) : D.ι mo.neg = y := by
  apply D.ι_eq_of_xbar hy
  rw [← iso_xbar_eq_neg mo D hy hxK]
  simp

theorem resCent_le_pair (mo : ModelOps S) {y w : G} (D : LayerData y S) (hwD : D.ι mo.z0 = w) :
    resCent ({y, w} : Set G) ≤ (mo.ops.blk 2 3).map D.ι ⊔ (mo.ops.blk 0 1).map D.ι := by
  set P : Subgroup G := resCent ({y, w} : Set G) with hP
  have hPperf : ⁅P, P⁆ = P := resCent_perfect _
  have hPC : P ≤ centralizer ({y, w} : Set G) := resCent_le _
  have hPy : P ≤ centralizer ({y} : Set G) := fun p hp =>
    centralizer_le (Set.singleton_subset_iff.2 (by simp)) (hPC hp)
  have hPw : P ≤ centralizer ({w} : Set G) := fun p hp =>
    centralizer_le (Set.singleton_subset_iff.2 (by simp)) (hPC hp)
  have hrange := D.le_range_ι hPperf hPy
  set P' : Subgroup ↥S := P.comap D.ι with hP'
  have hmapP : P'.map D.ι = P := by
    rw [hP', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective D.ι_injective
    rw [Subgroup.map_commutator, hmapP, hPperf]
  have hP'comm : ∀ g ∈ P', g * mo.z0 = mo.z0 * g := by
    intro g hg
    have h1 : D.ι g ∈ centralizer ({w} : Set G) := hPw hg
    have h2 := mem_centralizer_singleton_iff.1 h1
    rw [← hwD] at h2
    apply D.ι_injective
    rw [map_mul, map_mul]
    exact h2
  have hle := mo.pf.perf_le 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) mo.z0 mo.z0_mem mo.z0_sq mo.z0_ne P' hP'comm hP'perf
  rw [← hmapP, ← Subgroup.map_sup]
  exact Subgroup.map_mono hle


theorem exotic_setup (mo : ModelOps S) (hExact : S1LiftExactProp)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (e : ↥K ≃* ↥S) {q : ℕ} (hq5 : 5 ≤ q)
    {v : G} (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v) (hvx : v ≠ x) (hv2 : v * v = 1)
    (hvK : barOf hv ∉ K) (α : MulAut ↥K)
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    (hExo : IsExoticAutAt q α) :
    ∃ (wK : ↥K) (w : G) (hwx : w ∈ centralizer ({x} : Set G)) (h : G), w ∈ centralizer ({v} : Set G) ∧
      wK * wK = 1 ∧ wK ≠ 1 ∧ wK ≠ ⟨xbar x, hset.shape.2⟩ ∧ α wK = wK ∧
      w = (layerOf hExact hset hfront e).ι (e wK) ∧ barOf hwx = (wK : CentralizerBar x) ∧
      h * w * h⁻¹ = w * v ∧
      ¬ layer (CentralizerBar w) ≤ S45.barSub w (resCent ({x, w} : Set G)) := by
  classical
  obtain ⟨wK, w, hwx, h, Dx, Dv, hwv, hvord, hwK2, hwK1, hwKz, hwKα, hw, hwbar, hh, hDxK, hwDx, hwDv, hnegDv⟩ :=
    exotic_setup_core mo.core hExact hset hfront e (by omega) hv hconj hvx hv2 hvK α hα hExo
  have hwv' : w * v = v * w := mem_centralizer_singleton_iff.1 hwv
  have hgrowth := growth_abstract mo.ops mo.pf mo.blkq hvord (mem_centralizer_singleton_iff.2 hwv'.symm)
    hv hwx hwv Dx Dv mo.z0_mem mo.z0_sq mo.z0_ne mo.z0_cent hwDx hwDv mo.neg_mem_center mo.neg_sq
    mo.neg_ne hnegDv (by rw [hDxK]; exact hvK)
  have hgrowth' : ¬ layer (CentralizerBar w) ≤ S45.barSub w (resCent ({x, w} : Set G)) := by
    intro hle
    apply hgrowth
    exact hle.trans (S45.barSub_mono (resCent_le_pair mo Dx hwDx))
  exact ⟨wK, w, hwx, h, hwv, hwK2, hwK1, hwKz, hwKα, hw, hwbar, hh, hgrowth'⟩

end CFSG.GH74.Generic.S1.Exo
