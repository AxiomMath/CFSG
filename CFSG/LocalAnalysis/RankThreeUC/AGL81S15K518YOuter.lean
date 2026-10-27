module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YCent
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512G
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open

section General

variable {Y : Type} [Group Y] [Finite Y]

theorem rankThreeLayer_le_sup_centralizer {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    CFSG.Open.rankThreeLayer (⊤ : Subgroup Y) ≤ L ⊔ Subgroup.centralizer (L : Set Y) := by
  refine sSup_le fun I hI => ?_
  by_cases h : I = L
  · exact h ▸ le_sup_left
  · refine le_sup_of_le_right fun z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := Subgroup.commutator_mem_commutator hg hz
    rw [kComp_holds.1 _ L I hL hI (Ne.symm h), Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem dvd_index_of_pElement_not_mem {N : Subgroup Y} [N.Normal] {q : ℕ} (hq : q.Prime)
    {g : Y} (hgq : ∃ k : ℕ, orderOf g = q ^ k) (hg : g ∉ N) : q ∣ N.index := by
  obtain ⟨k, hk⟩ := hgq
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).1
    (hk ▸ orderOf_map_dvd (QuotientGroup.mk' N) g : orderOf (QuotientGroup.mk' N g) ∣ q ^ k)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hg ((QuotientGroup.eq_one_iff g).1 hj)
  have h1 : orderOf (QuotientGroup.mk' N g) ∣ Nat.card (Y ⧸ N) := orderOf_dvd_natCard _
  rw [hj] at h1
  rw [Subgroup.index_eq_card]
  exact (dvd_pow_self q hj0).trans h1

end General

variable {X : Type} [Group X] [Finite X]

theorem exists_pElement_not_mem_sup_of_cover {T T₁ T₂ : Subgroup X} (hcov : GNCoverP T T₁ T₂)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ls : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤)
    (hn : Ls.Normal) {g : X} (hgp : ∃ k : ℕ, orderOf g = p ^ k)
    (hg : toStar T g ∉ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))) :
    ∃ x : X, (∃ k : ℕ, orderOf x = p ^ k) ∧
      (x ∈ Subgroup.centralizer (T₁ : Set X) ∨ x ∈ Subgroup.normalizer (T₂ : Set X)) ∧
      toStar T x ∉ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
  haveI := hn
  set M : Subgroup (X ⧸ gnC T) := Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) with hM
  haveI hB : (M.comap (toStar T)).Normal := Subgroup.Normal.comap inferInstance _
  have hCB : gnC T ≤ M.comap (toStar T) := fun x hx => by
    rw [Subgroup.mem_comap, (toStar_eq_one_iff_mem_gnC x).2 hx]
    exact Subgroup.one_mem _
  have hLB : (⊤ : Subgroup X) ⊓ gnLayerPre T ≤ M.comap (toStar T) := by
    intro x hx
    have hxE : toStar T x ∈ CFSG.Open.rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) :=
      (Subgroup.mem_inf.1 hx).2
    exact rankThreeLayer_le_sup_centralizer hLs hxE
  have hidx : p ∣ (M.comap (toStar T)).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    exact dvd_index_of_pElement_not_mem hp hgp hg
  obtain ⟨x, -, hxB, hxp, hxT⟩ := hcov p hp hp2 ⊤ (M.comap (toStar T)) inferInstance hB hCB
    le_top hLB hidx
  exact ⟨x, hxp, hxT, hxB⟩

theorem pElementSubgroup_le_comap_of_sup {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {p : ℕ}
    (hp : p.Prime) (hK : ¬ p ∣ Nat.card (Subgroup.centralizer (Ls : Set (X ⧸ gnC T))))
    (h : ∀ g : X, (∃ k : ℕ, orderOf g = p ^ k) →
      toStar T g ∈ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))) :
    pElementSubgroup p (⊤ : Subgroup X) ≤ Ls.comap (toStar T) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨-, k, hk⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (hk ▸ orderOf_map_dvd (toStar T) g : orderOf (toStar T g) ∣ p ^ k)
  exact mem_of_pElement_sup_of_le_centralizer hp (Subgroup.le_centralizer_iff.2 le_rfl) hK
    (h g ⟨k, hk⟩) hj

end CFSG.LocalAnalysis.RankThreeUC.S15
