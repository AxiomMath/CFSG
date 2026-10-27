module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts.L34

variable {k : Type} [Field k]

theorem card_comap_conj_of_le_range (hk : Nat.card k = 4)
    {E : Subgroup (MulAut (projectiveSL 3 k))} (hE : Nat.card E = 9)
    (hinn : E ≤ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    Nat.card (E.comap (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k))) = 9 := by
  have hmap : (E.comap (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k))).map
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hinn
  rw [← hE, ← hmap, Subgroup.card_map_of_injective (conj_injective hk)]
  rw [hmap]

theorem inner_core (hk : Nat.card k = 4) {E S : Subgroup (MulAut (projectiveSL 3 k))}
    {x : projectiveSL 3 k} (hE : Nat.card E = 9)
    (hinn : E ≤ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range)
    (hx1 : x ≠ 1) (hxE : MulAut.conj x ∈ E) (hS : ¬ 3 ∣ Nat.card S)
    (hN : E ≤ Subgroup.normalizer (S : Set (MulAut (projectiveSL 3 k)))) :
    ∀ s ∈ S, ∀ c : projectiveSL 3 k, c * x = x * c → s c = c := by
  intro s hs c hc
  set E₀ := E.comap (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) with hE₀
  have hE₀9 : Nat.card E₀ = 9 := card_comap_conj_of_le_range hk hE hinn
  have hxE₀ : x ∈ E₀ := hxE
  have hcent := centralizer_eq_of_card_eq_nine hk hE₀9 hxE₀ hx1
  have hcE₀ : c ∈ E₀ := by
    rw [← hcent, Subgroup.mem_centralizer_singleton_iff]
    exact hc
  exact forall_apply_eq_of_invariant hk hE₀9 hS (fun e he => hN he) hs hcE₀

end CFSG.HardMathSupport.Solomon.Coordinator
