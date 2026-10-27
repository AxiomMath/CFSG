module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8Spec
public import Certificates.Certificate517202

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.M12Cover CFSG.EvenSmallLie.OmegaEight Certificates.S7Twin
  Certificates.S7TwinO8 Certificates.S5Rows CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  CFSG.Monster.B.Co2.Native

namespace O8

noncomputable abbrev H : Subgroup (Equiv.Perm (Fin 120)) := omega1T

abbrev S : Subgroup (Equiv.Perm (Fin 120)) := (sylQ ()).originalSubgroup

theorem degree_lt : (120 : ℕ) < 2 ^ 32 := by norm_num

theorem rep_permOfInv {n : ℕ} {t r : Array ℕ} (h : invPairB n t r = true) :
    CFSG.Monster.B.Co2.Rep n t (permOfInv n t r) := by
  intro x
  unfold permOfInv
  rw [dif_pos h]
  rfl

section Cert


theorem parts : o8TwinGens () = true ∧ o8TwinSylow () = true ∧ o8TwinReps () = true ∧
    o8TwinK0 () = true ∧ o8TwinPairs () = true :=
  Certificates.certificate517202

theorem gens1c_eq {i : ℕ} (hi : i < 8) :
    permOfInv 120 (genArr i) (invCand 120 (genArr i)) = gen1 i := by
  have h := parts.1
  simp only [o8TwinGens, List.all_eq_true, List.mem_range] at h
  have h1 : CFSG.Monster.B.Co2.Rep 120 (genArr i) (gen1 i) := by
    unfold genArr
    exact rep_gen1 hi
  exact CFSG.Monster.B.Co2.Rep.unique (rep_permOfInv (h i hi)) h1

theorem gens1c_mem : ∀ g ∈ gens1c (), g ∈ H := by
  intro g hg
  simp only [gens1c, List.mem_map, List.mem_range] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  rw [gens1c_eq hi]
  show gen1 i ∈ omega1T
  rw [omega1T_eq]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem sylGens_mem : ∀ g ∈ sylGens (), g ∈ H := by
  intro g hg
  simp only [sylGens, List.mem_map] at hg
  obtain ⟨w, -, rfl⟩ := hg
  rw [tab_eq]
  exact evalCodes_mem _ gens1c_mem w

theorem S_eq : S = Subgroup.closure {g | g ∈ sylGens ()} :=
  certificate_originalSubgroup _ _ _ _ _

theorem sylGens_mem_S : ∀ g ∈ sylGens (), g ∈ S := fun g hg => by
  rw [S_eq]
  exact Subgroup.subset_closure hg

theorem S_le : S ≤ H := by
  rw [S_eq, Subgroup.closure_le]
  exact fun g hg => sylGens_mem g hg

theorem sylQ_valid : ValidSchreier (sylQ ()) := by
  have h := parts.2.1
  simp only [o8TwinSylow, Bool.and_eq_true] at h
  exact h.1

theorem o8_card_syl : Nat.card S = 4096 := by
  have h := parts.2.1
  simp only [o8TwinSylow, Bool.and_eq_true, beq_iff_eq] at h
  rw [← (sylQ ()).orderCertificate_eq_card sylQ_valid, h.2]

theorem S_isPGroup : IsPGroup 2 S := IsPGroup.of_card (n := 12) (by rw [o8_card_syl]; norm_num)

theorem S_index : ¬ 2 ∣ (S.subgroupOf H).index := by
  have h := (S.subgroupOf H).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le).toEquiv, o8_card_syl,
    card_omega1T] at h
  have : (S.subgroupOf H).index = 42525 := by omega
  rw [this]
  decide

theorem fourReps_mem : ∀ r ∈ fourReps (), r ∈ S ∧ orderOf r = 4 := by
  have h := parts.2.2.1
  simp only [o8TwinReps, Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  refine ⟨?_, (ordTest_iff perm_faithful (rep_toTable degree_lt r) (by norm_num)).1
    (h.2 _ (List.mem_map_of_mem hr))⟩
  simp only [fourReps, List.mem_map] at hr
  obtain ⟨w, -, rfl⟩ := hr
  exact evalCodes_mem _ sylGens_mem_S w

theorem o8_cov : ∀ u ∈ S, orderOf u = 4 → ∃ r ∈ fourReps (), ∃ s ∈ S, u = s * r * s⁻¹ := by
  have h := parts.2.2.1
  simp only [o8TwinReps, Bool.and_eq_true] at h
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK degree_lt (sylQ ()) sylQ_valid
    (listTables_spec degree_lt sylGens_mem_S) 1 (fun g hg => by simpa using hg) (by norm_num)
    (fourReps ()) (fun r hr => by simpa using fourReps_mem r hr) 4000 h.1
  intro u hu ho
  exact hcov u (by simpa using hu) ho

theorem x0_mem : x0 () ∈ S := evalCodes_mem _ sylGens_mem_S _

theorem y0_mem : y0 () ∈ S := evalCodes_mem _ sylGens_mem_S _

theorem o8_K0 : Q8Rel (x0 ()) (y0 ()) := by
  have h := parts.2.2.2.1
  have hn := degree_lt
  exact q8RelT_spec hn (rep_toTable hn _) (rep_toTable hn _) (rep_toTable hn _)
    (rep_toTable hn _) h

theorem candPerms_mem : ∀ g ∈ candPerms (), g ∈ H := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact evalCodes_mem _ gens1c_mem w

theorem repCands_spec :
    ∀ cs ∈ repCands (), ∀ c ∈ cs, ∃ g ∈ H, Rep 120 c.1 g ∧ Rep 120 c.2 g⁻¹ :=
  cands_spec degree_lt (candPerms ()) candPerms_mem perRep

theorem o8_wit : ∀ r ∈ fourReps (), ∀ y ∈ S, Q8Rel r y →
    ∃ c ∈ H, PairWit (x0 ()) (y0 ()) r y c := by
  have h := parts.2.2.2.2
  have hn := degree_lt
  refine pairsOK_spec hn (sylQ ()) sylQ_valid
    (forall₂_spanT hn (rep_toTable hn _) (rep_toTable hn _) (rep_toTable hn _) (rep_toTable hn _))
    ?_ repCands_spec rfl h
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.2 fun r _ => rep_toTable hn r

theorem o8_model (T : Subgroup ↥H) (hT : Nonempty (↥T ≃* QuaternionGroup 2))
    (hΩ : HypOmegaGen (CoreAssembly.conjClass T)) :
    T ∈ CoreAssembly.conjClass (Subgroup.closure
      ({⟨x0 (), S_le x0_mem⟩, ⟨y0 (), S_le y0_mem⟩} : Set ↥H)) := by
  exact mem_conjClass_of_model H S S_le S_isPGroup S_index (fourReps ()) o8_cov (S_le x0_mem)
    (S_le y0_mem) o8_K0 o8_wit T hT hΩ

theorem o8_mem_conjClass {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1) {T₁ T₂ : Subgroup X}
    (h₁ : Nonempty (↥T₁ ≃* QuaternionGroup 2)) (h₂ : Nonempty (↥T₂ ≃* QuaternionGroup 2))
    (hΩ₁ : HypOmegaGen (CoreAssembly.conjClass T₁))
    (hΩ₂ : HypOmegaGen (CoreAssembly.conjClass T₂)) : T₂ ∈ CoreAssembly.conjClass T₁ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hX
  exact mem_conjClass_of_mulEquiv (e.trans omegaRestrictEquiv) _ o8_model h₁ h₂ hΩ₁ hΩ₂

end Cert

end O8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin
