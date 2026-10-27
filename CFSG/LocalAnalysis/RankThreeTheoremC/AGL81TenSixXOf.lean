module

import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace TenSixX

theorem exists_pow_two_mem_oUpperTwo {X : Subgroup G} {x : G} (hx : x ∈ X) :
    ∃ a : ℕ, x ^ (2 ^ a) ∈ CFSG.ComponentClassification.AS76b.oUpperTwo X := by
  obtain ⟨a, m, hm, horder⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, Subgroup.subset_closure ⟨X.pow_mem hx _, ?_⟩⟩
  apply hm.of_dvd_nat
  rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← horder, pow_orderOf_eq_one]

theorem d1X0_le_normalizer_d1KBar (p : ℕ) (M H : Subgroup G) :
    d1X0 p M H ≤ normalizer (d1KBar p M H : Set (H ⧸ primeComplementCore (G := H) p)) := by
  intro x hx
  apply TenNineOneThree.mem_normalizer_of_conj_mem
  have hmap : (d1KBar p M H).map (MulAut.conj x).toMonoidHom ≤ d1KBar p M H := by
    unfold d1KBar
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    refine le_d1KBar (isComponentOf_map_conj hL.1 x) fun hle => hL.2 ?_
    intro l hl
    have h1 : (MulAut.conj x).toMonoidHom l ∈ d1X0 p M H := hle ⟨l, hl, rfl⟩
    have h2 : x⁻¹ * ((MulAut.conj x).toMonoidHom l) * x⁻¹⁻¹ ∈ d1X0 p M H :=
      (d1X0 p M H).mul_mem ((d1X0 p M H).mul_mem ((d1X0 p M H).inv_mem hx) h1)
        ((d1X0 p M H).inv_mem ((d1X0 p M H).inv_mem hx))
    simpa [MulAut.conj_apply, mul_assoc] using h2
  intro k hk
  exact hmap ⟨k, hk, rfl⟩

end TenSixX

open TenSixX

end CFSG.LocalAnalysis.RankThreeTheoremC
