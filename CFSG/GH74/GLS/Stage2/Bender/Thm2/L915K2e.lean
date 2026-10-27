module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup
open CFSG.ComponentClassification.CatFactsSp4
open scoped commutatorElement

variable {K : Type} [Field K]

theorem u2_not_mem_Lsub : u2 K ∉ Lsub K := by
  rintro ⟨_, ⟨g, rfl⟩, hg⟩
  have hg' : proj 2 K (diagSL K g) = proj 2 K (T2 K) := hg
  rcases eq_or_eq_neg_of_proj_eq hg' with h | h
  · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
    simp [coe_diagSL, coe_T2, kron, J₁] at this
  · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
    simp [coe_diagSL, coe_T2, kron, J₁] at this

theorem not_mem_derived2_of_le_centralizer_u2 (h2 : (2 : K) ≠ 0)
    {Y : Subgroup (StatedProj (StatedSp 2 K))} (hY : Y ≤ centralizer {u2 K}) :
    u2 K ∉ ⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆ := by
  intro h
  have h1 : ⁅Y, Y⁆ ≤ (centralizer {T2 K}).map (proj 2 K) :=
    (commutator_mono hY hY).trans (commutator_centralizer_proj_le (T2 K))
  have h3 : ⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆ ≤ Lsub K :=
    calc ⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆ ≤ ⁅(centralizer {T2 K}).map (proj 2 K), (centralizer {T2 K}).map (proj 2 K)⁆ :=
          commutator_mono h1 h1
      _ = ⁅centralizer {T2 K}, centralizer {T2 K}⁆.map (proj 2 K) := (map_commutator _ _ _).symm
      _ ≤ Lsub K := map_mono (commutator_centralizer_T2_le h2)
  exact u2_not_mem_Lsub (h3 h)

theorem not_conj_u2_of_mem_derived2 (h2 : (2 : K) ≠ 0) {t : StatedProj (StatedSp 2 K)}
    {Y : Subgroup (StatedProj (StatedSp 2 K))} (hY : Y ≤ centralizer {t})
    (ht : t ∈ ⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆) : ¬ ∃ g, g⁻¹ * t * g = u2 K := by
  rintro ⟨g, hg⟩
  set φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K) := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφt : φ t = u2 K := by
    rw [← hg]
    simp [hφ]
  have hYφ : Y.map φ ≤ centralizer {u2 K} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hφt, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hY hy)]
  refine not_mem_derived2_of_le_centralizer_u2 h2 hYφ ?_
  have e : ⁅⁅Y.map φ, Y.map φ⁆, ⁅Y.map φ, Y.map φ⁆⁆ = (⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆).map φ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, ← Subgroup.map_commutator,
      ← Subgroup.map_commutator]
  rw [e, ← hφt]
  exact Subgroup.mem_map_of_mem φ ht

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
