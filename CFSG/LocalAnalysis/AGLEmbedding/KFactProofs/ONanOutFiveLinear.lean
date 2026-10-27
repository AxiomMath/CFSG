module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFiveSeries
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.AGLEmbedding.OutFive

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.OutStructure
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem linearAutGroup_quotient_cyclic (hn : 1 ≤ n) :
    ∃ g ∈ linearAutGroup n K, ∀ δ ∈ linearAutGroup n K,
      ∃ k : ℤ, g ^ k * δ ∈ Inn (projectiveSL n K) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨A₀, hA₀⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin n) (R := K) ζ
  refine ⟨conjAut n K A₀, mem_linearAutGroup_iff.mpr ⟨A₀, rfl⟩, ?_⟩
  intro δ hδ
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hδ
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hζ (GeneralLinearGroup.det A))
  refine ⟨-j, ?_⟩
  have hdet : (A₀ ^ (-j) * A : GL (Fin n) K).det = 1 := by
    rw [map_mul, map_zpow, hA₀, ← hj, ← _root_.zpow_add, neg_add_cancel, zpow_zero]
  obtain ⟨g', hg'⟩ : ∃ g' : SpecialLinearGroup (Fin n) K,
      SpecialLinearGroup.toGL g' = A₀ ^ (-j) * A := by
    refine ⟨⟨((A₀ ^ (-j) * A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ?_⟩, Units.ext rfl⟩
    rw [← GeneralLinearGroup.val_det_apply, hdet]
    rfl
  have h1 : conjAut n K A₀ ^ (-j) * conjAut n K A = conjAut n K (A₀ ^ (-j) * A) := by
    rw [map_mul, map_zpow]
  rw [h1, ← hg', conjAut_toGL]
  exact ⟨proj n K g', rfl⟩

theorem outPlaneSeries_projectiveSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutPlaneSeries p (projectiveSL n K) := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDn, -, -, ⟨g, hgE, hg⟩, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  have hpE : ∀ α : MulAut (projectiveSL n K), (∃ k : ℕ, α ^ (p ^ k) ∈ linearAutGroup n K) →
      α ∈ semilinearAutGroup n K := by
    rintro α ⟨k, hk⟩
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2
    have hpodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two hp hp2).pow
    exact mem_of_pow_mem_of_index_le_two _ hidx' hpodd (linearAutGroup_le_semilinearAutGroup hk)
  refine ⟨linearAutGroup n K, hDnorm, ?_, ?_⟩
  · intro R hRD hR hcard hRI
    obtain ⟨g₀, hg₀D, hg₀⟩ := linearAutGroup_quotient_cyclic (K := K) (n := n) (by omega)
    have : IsCyclic (↥(linearAutGroup n K) ⧸
        (Inn (projectiveSL n K)).subgroupOf (linearAutGroup n K)) :=
      isCyclic_quotient_of_forall _ ⟨g₀, hg₀D⟩ fun α => hg₀ α α.2
    exact false_of_plane_in_cyclic_quotient hp hRD hR hcard hRI
  · intro R hR hcard hRD
    have hRE : R ≤ semilinearAutGroup n K := fun x hx =>
      hpE x ⟨1, by rw [pow_one, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx]; exact one_mem _⟩
    have : IsCyclic (↥(semilinearAutGroup n K) ⧸
        (linearAutGroup n K).subgroupOf (semilinearAutGroup n K)) :=
      isCyclic_quotient_of_forall _ ⟨g, hgE⟩ fun α => hg α α.2
    exact false_of_plane_in_cyclic_quotient hp hRE hR hcard hRD

theorem outPlaneSeries_PSL_model {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n r m : ℕ} (hn : 3 ≤ n) (h : StatedClassicalModel X .PSL n r m) : OutPlaneSeries p X := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  have e' : X ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  exact OutPlaneSeries.of_mulEquiv e' (outPlaneSeries_projectiveSL hn hp hp2)

end CFSG.AGLEmbedding.OutFive
