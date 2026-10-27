module

public import CFSG.ClassicalInvolution.RouteD.TypeAModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def adjPair (n a : ℕ) (h : a + 2 ≤ n) : Pair n :=
  ⟨{⟨a, by omega⟩, ⟨a + 1, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩

theorem range_blockSL_eq_Lc (h2 : (2 : F) ≠ 0) {n a : ℕ} (h : a + 2 ≤ n) :
    (blockSL F n 2 a h).range = Lc F (adjPair n a h) := by
  rw [range_blockSL_eq_longRootGroup h2 h, negBlock_eq_zMat h]
  rfl

theorem exists_perp_not_commutes (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    {R₀ Rβ : Subgroup SL(n, F)} {i₀ iβ : SL(n, F)}
    (h₀ : IsLongRootSL2 (by omega : 2 ≤ n) R₀ i₀) (hβ : IsLongRootSL2 (by omega : 2 ≤ n) Rβ iβ)
    (hc : Commute i₀ iβ) (hne : i₀ ≠ iβ) (hnc : ¬ Commutes R₀ Rβ) :
    ∃ (R : Subgroup SL(n, F)) (i : SL(n, F)), IsLongRootSL2 (by omega : 2 ≤ n) R i ∧
      Commutes R R₀ ∧ ¬ Commutes R Rβ := by
  rcases inf_eq_bot_or_exists_conj h2 (by omega : 3 ≤ n) h₀ hβ hc hne with hbot | ⟨P, hR₀, hRβ, -, -⟩
  · exact absurd hbot (inf_ne_bot_of_not_commutes h2 h₀ hβ hc hnc)
  · have hP : Function.Injective (MulAut.conj P).toMonoidHom := (MulAut.conj P).injective
    rw [range_blockSL_eq_Lc h2 (by omega : 0 + 2 ≤ n)] at hR₀
    rw [range_blockSL_eq_Lc h2 (by omega : 1 + 2 ≤ n)] at hRβ
    have hL : IsLongRootSL2 (by omega : 2 ≤ n) ((Lc F (adjPair n 2 (by omega))).map
        (MulAut.conj P).toMonoidHom) (P * zElt F (adjPair n 2 (by omega)) * P⁻¹) :=
      (isLongRootSL2_Lc h2 (by omega : 2 ≤ n) (adjPair n 2 (by omega))).conj P
    refine ⟨_, _, hL, ?_, ?_⟩
    · rw [hR₀]
      refine (commutes_map_iff _ hP).mpr (commutes_Lc_of_disjoint h2 ?_)
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [adjPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx hx'
      omega
    · rw [hRβ]
      intro hcomm
      have := (commutes_map_iff _ hP).mp hcomm
      exact not_commutes_Lc_overlap h2 (by omega : 3 ≤ n)
        (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (k := ⟨3, by omega⟩) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (fun a ha b hb => (this b hb a ha).symm)

end CFSG.ClassicalInvolution.RouteD.Gaps
