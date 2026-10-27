module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma36_of_35 (h35 : Asc82Lemma35) (hP : Asc82PocketExists) : Asc82Lemma36 := by
  intro G _ _ t L hS x X hx hX hXF
  have hXstar : InFStar X := hXF.elim inFStar_of_inF (inFStar_of_isL3Eps3 hX)
  obtain ⟨y, K, hy, hKX, hpocket⟩ := hP G x X hx hX hXF
  have hyX : y ∈ X := hKX hpocket.1
  have hyCx : y ∈ centralizer ({x} : Set G) := (hpocket.2.1.trans inf_le_left) hpocket.1
  have hPD : Sec3PocketData x X y K := ⟨hx, hX, hXstar, hy, hyX, hKX, hpocket⟩
  have hxy : x ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (Subgroup.mem_centralizer_iff.1 hyCx x (Set.mem_singleton x)).symm
  refine ⟨hXstar, ?_⟩
  intro I hI hIF
  by_contra hne
  have hcomm : ∀ a ∈ I, ∀ b ∈ X, a * b = b * a := hI.commute_of_ne hX hne
  have hIcy : I ≤ centralizer ({y} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hcomm a ha y hyX).symm
  have hIpair : I ≤ centralizer ({x, y} : Set G) := by
    rw [centralizer_pair_eq_inf]
    exact le_inf hI.le hIcy
  have hIxy : IsComponentIn I (centralizer ({x, y} : Set G)) :=
    hI.mono hIpair (by rw [centralizer_pair_eq_inf]; exact inf_le_left)
  exact h35 G t L hS x X y K x hPD hx hxy I ⟨hIxy, hIF⟩

end CFSG.OddStandard.SmallF3.Omega
