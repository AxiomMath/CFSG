module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModelAux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ε : ZMod 3}

theorem ffOutFFE8CentModel_pair_mem (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {k m : Fin 4}
    (hkm : k ≠ m) : fr.signChange (ffE8Hat {k, m}) ∈ ffE8Group fr :=
  ⟨{k, m}, by rw [Finset.card_pair hkm]; exact even_two, rfl⟩

private theorem pair_trace_ne {k m : Fin 4} (hkm : k ≠ m) :
    (Fintype.card FFE8Idx : ZMod 3) - 2 * (ffE8Hat {k, m}).card ≠ 0 := by
  have h1 : (ffE8Hat {k, m}).card = 2 := by
    rw [ffE8Hat, Finset.card_map, Finset.card_pair hkm]
  have h2 : Fintype.card FFE8Idx = 6 := by
    simp [Fintype.card_sum]
  rw [h1, h2]
  decide

theorem ffOutFFE8CentModel_centralizer_eq (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) :
    centralizer (((ffE8Group fr).map (ffSim Q) : Subgroup (ProjSim Q)) : Set (ProjSim Q)) =
      (ffOutFFE8CentModel_grp fr).map (ffSim Q) := by
  ext x
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨μ, hμ⟩ := γ.2
    have hcomm : ∀ k m : Fin 4, k ≠ m → ∀ v,
        ((fr.signChange (ffE8Hat {k, m}) : OGroup Q) : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v) =
          (γ : V ≃ₗ[ZMod 3] V)
            (((fr.signChange (ffE8Hat {k, m}) : OGroup Q) : V ≃ₗ[ZMod 3] V) v) := by
      intro k m hkm
      have hmem : ffSim Q (fr.signChange (ffE8Hat {k, m})) ∈ (ffE8Group fr).map (ffSim Q) :=
        ⟨_, ffOutFFE8CentModel_pair_mem fr hkm, rfl⟩
      rcases ffOutFFE8CentModel_commute_cases (fr.signChange (ffE8Hat {k, m})) γ (hx _ hmem) with
        h2 | h2
      · exact h2
      · exact absurd (ffOutFFE8CentModel_trace_neg fr (ffE8Hat {k, m}) h2) (pair_trace_ne hkm)
    obtain ⟨g, hgγ, K, rfl⟩ := ffOutFFE8CentModel_diag hε fr hμ
      (fun i j hij hinr => ffOutFFE8CentModel_offdiag fr hcomm hij hinr)
    refine ⟨fr.signChange K, ⟨K, rfl⟩, ?_⟩
    show (QuotientGroup.mk (orthToSim Q (fr.signChange K)) : ProjSim Q) = QuotientGroup.mk γ
    congr 1
    exact Subtype.ext hgγ
  · rintro ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    have hts : t ∈ ffOutFFE8CentModel_grp fr := by
      obtain ⟨J, -, rfl⟩ := ht
      exact ⟨_, rfl⟩
    rw [← map_mul, ← map_mul, ffOutFFE8CentModel_grp_comm fr hts hs]

theorem ffOutFFE8CentModel_grp_isMulCommutative {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ι → ZMod 3} (fr : PFrame Q ι c) : IsMulCommutative (ffOutFFE8CentModel_grp fr) :=
  IsMulCommutative.of_setLike_mul_comm fun _ ha _ hb => ffOutFFE8CentModel_grp_comm fr ha hb

theorem ffOutFFE8CentModel_map_elemAbelian {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ι → ZMod 3} (fr : PFrame Q ι c) :
    CFSG.Open.IsElemAbelian 2 ((ffOutFFE8CentModel_grp fr).map (ffSim Q)) := by
  haveI := ffOutFFE8CentModel_grp_isMulCommutative fr
  refine ⟨inferInstance, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  rw [← map_pow, pow_two, ffOutFFE8CentModel_grp_mul_self fr hg, map_one]

theorem ffOutFFE8CentModel_ffSim_piOrth : ffSim Q (piOrth Q) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (mem_piSim_iff.mpr (Or.inr rfl))

theorem ffOutFFE8CentModel_ffSim_compl {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (K : Finset ι) :
    ffSim Q (fr.signChange Kᶜ) = ffSim Q (fr.signChange K) := by
  rw [show Kᶜ = symmDiff Finset.univ K by ext i; simp [Finset.mem_symmDiff],
    ← fr.signChange_mul, ← fr.piOrth_eq_signChange_univ, map_mul,
    ffOutFFE8CentModel_ffSim_piOrth, one_mul]

theorem ffOutFFE8CentModel_card_le {c : FFE8Idx → ZMod 3} (fr : PFrame Q FFE8Idx c) :
    Nat.card ((ffOutFFE8CentModel_grp fr).map (ffSim Q)) ≤ 32 := by
  classical
  let T : Finset (Finset FFE8Idx) := (Finset.univ.erase (Sum.inl 0)).powerset
  have hT : T.card = 32 := by
    simp [T, Finset.card_powerset, Finset.card_erase_of_mem, Fintype.card_sum]
  have hsub : (((ffOutFFE8CentModel_grp fr).map (ffSim Q) : Subgroup (ProjSim Q)) :
      Set (ProjSim Q)) ⊆ (fun K => ffSim Q (fr.signChange K)) '' (T : Set (Finset FFE8Idx)) := by
    rintro _ ⟨g, ⟨K, rfl⟩, rfl⟩
    by_cases hK : (Sum.inl 0 : FFE8Idx) ∈ K
    · refine ⟨Kᶜ, ?_, ffOutFFE8CentModel_ffSim_compl fr K⟩
      simp only [T, Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
      intro i hi
      simp only [Finset.mem_compl] at hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact hi hK
    · refine ⟨K, ?_, rfl⟩
      simp only [T, Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
      intro i hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact hK hi
  calc Nat.card ((ffOutFFE8CentModel_grp fr).map (ffSim Q))
      = Set.ncard (((ffOutFFE8CentModel_grp fr).map (ffSim Q) : Subgroup (ProjSim Q)) :
          Set (ProjSim Q)) := Nat.card_coe_set_eq _
    _ ≤ Set.ncard ((fun K => ffSim Q (fr.signChange K)) '' (T : Set (Finset FFE8Idx))) :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet T).image _)
    _ ≤ Set.ncard (T : Set (Finset FFE8Idx)) := Set.ncard_image_le (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ = 32 := hT

end CFSG.OddStandard.SmallF3.Omega
