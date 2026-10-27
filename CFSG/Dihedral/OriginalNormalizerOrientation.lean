module

public import CFSG.Dihedral.OriginalASevenOddCore
public import CFSG.Dihedral.StationarySylowCore
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.OriginalCharacterKernelBounds

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem opposite_original_fourgroup_of_stationarity
    (hs : d.Stationarity) (hm : d.MaximalOddKernel) (hR : d.R ≠ ⊥)
    (i : Fin 2) (hi : Cycles d.N (d.V i)) :
    ∀ j : Fin 2, j ≠ i → ¬ Cycles d.N (d.V j) ∧ d.E j = d.commonE := by
  have hN : d.N ≠ ⊤ := hm.2.2.2.1 hR
  have hCN : d.C ≤ d.N := hm.2.2.1
  have hSN : (d.S : Subgroup G) ≤ d.N := d.sylow_le_centralizer.trans hCN
  have hnotboth := hs.2.2.2.2.2.2.2 d.N hN hCN
  intro j hji
  have hnot : ¬ Cycles d.N (d.V j) := by
    intro hj
    have hboth : Cycles d.N (d.V 0) ∧ Cycles d.N (d.V 1) := by
      fin_cases i <;> fin_cases j
      · exact (hji rfl).elim
      · exact ⟨hi, hj⟩
      · exact ⟨hj, hi⟩
      · exact (hji rfl).elim
    exact hnotboth (Or.inl hboth.1) hboth
  refine ⟨hnot, ?_⟩
  have heq := (hs.2.2.2.2.2.2.1 d.N hN hSN).1 i j hji.symm hi hnot
  have hE : d.E j ≤ d.N := inf_le_left.trans (d.R_le.trans hCN)
  have hcommon : d.commonE ≤ d.N := inf_le_left.trans (d.R_le.trans hCN)
  simpa only [inf_eq_left.mpr hE, inf_eq_left.mpr hcommon] using heq.1

theorem original_even_rotation_centralizes_R_of_aSeven_model
    (e : G ≃* alternatingGroup (Fin 7))
    (i : Fin 2) (hi : d.E i = d.R) :
    Subgroup.closure ({d.r ^ 2, d.s * d.r ^ i.val} : Set G) ≤
      Subgroup.centralizer (d.R : Set G) := by
  apply (Subgroup.closure_le (Subgroup.centralizer (d.R : Set G))).mpr
  intro x hx
  rcases hx with rfl | hx
  · have hn := d.n_eq_three_of_aSeven_model e
    have hr2 : d.r ^ 2 = d.t := by simp [t, hn]
    rw [hr2]
    change d.t ∈ Subgroup.centralizer (d.R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hcent : r ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.R_le hr
    exact Subgroup.mem_centralizer_singleton_iff.mp hcent
  · rw [Set.mem_singleton_iff.mp hx]
    exact d.fourgroup_le_R_centralizer i hi (Subgroup.subset_closure (by simp))

theorem original_prime_eq_three_and_sylow_eq_R_of_aSeven_model
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R)
    (P : Subgroup G) (hP : IsSylowIn p P d.R) : p = 3 ∧ P = d.R := by
  have hcard := d.R_card_of_aSeven_model hR e
  have hp3 : p = 3 := by
    have hdiv := hp.2
    rw [hcard] at hdiv
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · exact (hp.1.ne_one h1).elim
    · exact h3
  exact ⟨hp3, isSylowIn_eq_of_card_prime p hp.1 P d.R hP (hcard.trans hp3.symm)⟩

theorem original_prime_family_control_of_common_cycle
    (hc : d.CanonicalNormalizers) (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7))
    (i : Fin 2) (hi : d.E i = d.R) (hcycle : Cycles d.N (d.V i)) :
    ∀ p ∈ primeSupport d.R, ∀ P : Subgroup G, IsSylowIn p P d.R →
      NormalizedBy P (d.S : Subgroup G) →
      P ≤ Subgroup.centralizer (d.V i : Set G) ∧ d.HP P ≠ ⊤ ∧
      Cycles (Subgroup.normalizer (P : Set G)) (d.V i) ∧ d.JP P ≤ d.R := by
  intro p hp P hP hPS
  have hPeq := (d.original_prime_eq_three_and_sylow_eq_R_of_aSeven_model hR e p hp P hP).2
  have hdata := hc.1 p hp P hP hPS
  have hPcent : P ≤ Subgroup.centralizer (d.V i : Set G) := by
    rw [hPeq]
    exact d.R_le_fourgroup_centralizer i hi
  refine ⟨hPcent, hdata.2.2.1, ?_, ?_⟩
  · rw [hPeq]
    exact hcycle
  · have hcyclic : IsCyclic d.R := by
      let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card (d.R_card_of_aSeven_model hR e)
    let : IsCyclic P := hPeq ▸ hcyclic
    have hcenter : (Subgroup.center P).map P.subtype = P := by
      rw [Subgroup.center_eq_top, Subgroup.map_top, Subgroup.range_subtype]
    have hHP : d.HP P = Subgroup.normalizer (P : Set G) := by
      rw [HP, hcenter]
    change d.JP P ≤ d.R
    rw [JP, hHP, hPeq]
    have hcore := d.N_oddCore_of_aligned_aSeven_model hR
      (d.aSeven_equiv_aligned e).choose (d.aSeven_equiv_aligned e).choose_spec
    exact le_of_eq hcore

end CFSG.DihedralBlueprint.OriginalData
