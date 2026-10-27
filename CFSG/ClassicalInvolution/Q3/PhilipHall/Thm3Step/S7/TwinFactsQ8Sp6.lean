module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8Spec
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import Certificates.Certificate517201

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.M12Cover CFSG.EvenSmallLie.Sp6 Certificates.S7Twin
  Certificates.S7TwinSp6 Certificates.S5Rows CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

namespace Sp6

abbrev H : Subgroup (Equiv.Perm (Fin 36)) := sp6Q.originalSubgroup

abbrev S : Subgroup (Equiv.Perm (Fin 36)) := (sylQ ()).originalSubgroup

theorem degree_lt : (36 : ℕ) < 2 ^ 32 := by norm_num

theorem sylGens_mem : ∀ g ∈ sylGens (), g ∈ H := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  rw [tab_eq]
  exact evalCodes_mem _ sp6Gens_mem w

theorem S_eq : S = Subgroup.closure {g | g ∈ sylGens ()} :=
  certificate_originalSubgroup _ _ _ _ _

theorem sylGens_mem_S : ∀ g ∈ sylGens (), g ∈ S := fun g hg => by
  rw [S_eq]
  exact Subgroup.subset_closure hg

theorem S_le : S ≤ H := by
  rw [S_eq, Subgroup.closure_le]
  exact fun g hg => sylGens_mem g hg

section Cert


theorem parts : sp6TwinSylow () = true ∧ sp6TwinReps () = true ∧ sp6TwinK0 () = true ∧
    sp6TwinPairs () = true :=
  Certificates.certificate517201

theorem sylQ_valid : ValidSchreier (sylQ ()) := by
  have h := parts.1
  simp only [sp6TwinSylow, Bool.and_eq_true] at h
  exact h.1

theorem sp6_card_syl : Nat.card S = 512 := by
  have h := parts.1
  simp only [sp6TwinSylow, Bool.and_eq_true, beq_iff_eq] at h
  rw [← (sylQ ()).orderCertificate_eq_card sylQ_valid, h.2]

theorem S_isPGroup : IsPGroup 2 S := IsPGroup.of_card (n := 9) (by rw [sp6_card_syl]; norm_num)


theorem S_index : ¬ 2 ∣ (S.subgroupOf H).index := by
  have h := (S.subgroupOf H).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le).toEquiv, sp6_card_syl, card_sp6Q] at h
  have : (S.subgroupOf H).index = 2835 := by omega
  rw [this]
  decide

theorem fourReps_mem : ∀ r ∈ fourReps (), r ∈ S ∧ orderOf r = 4 := by
  have h := parts.2.1
  simp only [sp6TwinReps, Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  refine ⟨?_, (ordTest_iff perm_faithful (rep_toTable degree_lt r) (by norm_num)).1
    (h.2 _ (List.mem_map_of_mem hr))⟩
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
  exact evalCodes_mem _ sylGens_mem_S w

theorem sp6_cov : ∀ u ∈ S, orderOf u = 4 → ∃ r ∈ fourReps (), ∃ s ∈ S, u = s * r * s⁻¹ := by
  have h := parts.2.1
  simp only [sp6TwinReps, Bool.and_eq_true] at h
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK degree_lt (sylQ ()) sylQ_valid
    (listTables_spec degree_lt sylGens_mem_S) 1 (fun g hg => by simpa using hg) (by norm_num)
    (fourReps ()) (fun r hr => by simpa using fourReps_mem r hr) 4000 h.1
  intro u hu ho
  exact hcov u (by simpa using hu) ho

theorem x0_mem : x0 () ∈ S := evalCodes_mem _ sylGens_mem_S _

theorem y0_mem : y0 () ∈ S := evalCodes_mem _ sylGens_mem_S _

theorem sp6_K0 : Q8Rel (x0 ()) (y0 ()) := by
  have h := parts.2.2.1
  have hn := degree_lt
  exact q8RelT_spec hn (rep_toTable hn _) (rep_toTable hn _) (rep_toTable hn _)
    (rep_toTable hn _) h

theorem repCands_spec :
    ∀ cs ∈ repCands (), ∀ c ∈ cs, ∃ g ∈ H, Rep 36 c.1 g ∧ Rep 36 c.2 g⁻¹ := by
  intro cs hcs c hc
  simp only [repCands, List.mem_map] at hcs
  obtain ⟨l, -, rfl⟩ := hcs
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  rcases getD_mem_or_eq (((candPerms ()).map fun g => (toTable g, toTable g⁻¹)).toArray) i
      (toTable (1 : Equiv.Perm (Fin 36)), toTable (1 : Equiv.Perm (Fin 36))) with h | h
  · rw [List.toList_toArray] at h
    obtain ⟨g, hg, hgc⟩ := List.mem_map.mp h
    rw [← hgc]
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
    exact ⟨_, evalCodes_mem _ sp6Gens_mem w, rep_toTable degree_lt _, rep_toTable degree_lt _⟩
  · rw [h]
    exact ⟨1, H.one_mem, rep_toTable degree_lt _, by rw [inv_one]; exact rep_toTable degree_lt _⟩

theorem sp6_wit : ∀ r ∈ fourReps (), ∀ y ∈ S, Q8Rel r y →
    ∃ c ∈ H, PairWit (x0 ()) (y0 ()) r y c := by
  have h := parts.2.2.2
  have hn := degree_lt
  refine pairsOK_spec hn (sylQ ()) sylQ_valid
    (forall₂_spanT hn (rep_toTable hn _) (rep_toTable hn _) (rep_toTable hn _) (rep_toTable hn _))
    ?_ repCands_spec rfl h
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.2 fun r _ => rep_toTable hn r

theorem sp6_model (T : Subgroup ↥H) (hT : Nonempty (↥T ≃* QuaternionGroup 2))
    (hΩ : HypOmegaGen (CoreAssembly.conjClass T)) :
    T ∈ CoreAssembly.conjClass (Subgroup.closure
      ({⟨x0 (), S_le x0_mem⟩, ⟨y0 (), S_le y0_mem⟩} : Set ↥H)) :=
  mem_conjClass_of_model H S S_le S_isPGroup S_index (fourReps ()) sp6_cov (S_le x0_mem)
    (S_le y0_mem) sp6_K0 sp6_wit T hT hΩ


theorem sp6_mem_conjClass {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1) {T₁ T₂ : Subgroup X}
    (h₁ : Nonempty (↥T₁ ≃* QuaternionGroup 2)) (h₂ : Nonempty (↥T₂ ≃* QuaternionGroup 2))
    (hΩ₁ : HypOmegaGen (CoreAssembly.conjClass T₁))
    (hΩ₂ : HypOmegaGen (CoreAssembly.conjClass T₂)) : T₂ ∈ CoreAssembly.conjClass T₁ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hX
  have : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [card_sp6Q]; norm_num)
  exact mem_conjClass_of_mulEquiv (e.trans (MulEquiv.subgroupCongr sp6Q_originalSubgroup.symm))
    _ sp6_model h₁ h₂ hΩ₁ hΩ₂

end Cert

end Sp6

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin
