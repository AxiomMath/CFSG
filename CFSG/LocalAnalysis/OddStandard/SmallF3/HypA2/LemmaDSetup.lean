module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.NcData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.PumpIn
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaS

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem pump_of_ncData {G : Type} [Group G] [Finite G] {y z : G} {K T N : Subgroup G}
    {q₀ : ℕ} (h : NcData G y z K T N q₀) (hbal : oddCore ↥(centralizer ({z} : Set G)) = ⊥) :
    ∃ M : Subgroup G, Omega.IsComponentIn M (centralizer ({z} : Set G)) ∧
      ((M.map (MulAut.conj y).toMonoidHom = M ∧ T ≤ M) ∨
        (M.map (MulAut.conj y).toMonoidHom ≠ M ∧
          ⁅M, M.map (MulAut.conj y).toMonoidHom⁆ = ⊥ ∧
          ∃ φ : ↥M →* G, (∀ m : ↥M, φ m = (m : G) * (y * m * y⁻¹)) ∧ T = φ.range ∧
            φ.ker ≤ center ↥M)) := by
  have hTpair := isTwoComponentIn_centralizer_pair h.hK h.hzK h.hzc h.hT
  rw [centralizer_pair_eq_inf, inf_comm] at hTpair
  have hyz : y ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ((Subgroup.mem_centralizer_iff.1 (h.hK.1 h.hzK)) y (by simp)).symm
  exact exists_component_pump_in hbal hyz h.oy hTpair

end CFSG.OddStandard.SmallF3.HypA2
