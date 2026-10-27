module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {X : Type*} [Group X]

@[expose] def litPerf (K : Subgroup X) : Subgroup X :=
  sSup {L : Subgroup X | L ≤ K ∧ ⁅L, L⁆ = L}

theorem litPerf_le (K : Subgroup X) : litPerf K ≤ K := by
  exact sSup_le fun L hL => hL.1

theorem litPerf_perfect (K : Subgroup X) : ⁅litPerf K, litPerf K⁆ = litPerf K := by
  refine le_antisymm (commutator_le_of_le le_rfl le_rfl) ?_
  refine sSup_le ?_
  rintro L ⟨hLK, hL⟩
  calc L = ⁅L, L⁆ := hL.symm
    _ ≤ ⁅litPerf K, litPerf K⁆ :=
        commutator_mono (le_sSup ⟨hLK, hL⟩) (le_sSup ⟨hLK, hL⟩)

theorem le_litPerf {K L : Subgroup X} (hLK : L ≤ K) (hL : ⁅L, L⁆ = L) : L ≤ litPerf K := by
  exact le_sSup ⟨hLK, hL⟩

theorem litPerf_map (e : X ≃* X) (K : Subgroup X) :
    (litPerf K).map e.toMonoidHom = litPerf (K.map e.toMonoidHom) := by
  have hfwd : ∀ (e : X ≃* X) (K : Subgroup X),
      (litPerf K).map e.toMonoidHom ≤ litPerf (K.map e.toMonoidHom) := by
    intro e K
    refine le_litPerf (Subgroup.map_mono (litPerf_le K)) ?_
    rw [← Subgroup.map_commutator, litPerf_perfect]
  refine le_antisymm (hfwd e K) ?_
  have h := hfwd e.symm (K.map e.toMonoidHom)
  have hK : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  rw [hK] at h
  have hmap : ((litPerf (K.map e.toMonoidHom)).map e.symm.toMonoidHom).map e.toMonoidHom
      = litPerf (K.map e.toMonoidHom) := by
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id X := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  have h2 := Subgroup.map_mono (f := e.toMonoidHom) h
  rwa [hmap] at h2

theorem litPerf_normal (K : Subgroup X) [K.Normal] : (litPerf K).Normal := by
  rw [normal_iff_map_conj_eq]
  intro g
  show (litPerf K).map (MulAut.conj g).toMonoidHom = litPerf K
  rw [litPerf_map (MulAut.conj g) K, MulEquiv.toMonoidHom_eq_coe, Normal.map_conj_eq K g]

variable {G : Type*} [Group G]

theorem lit_perf_map [Finite X] {π : X →* G} (hπ : Function.Surjective π) {M : Subgroup G}
    (hM : ⁅M, M⁆ = M) : (litPerf (M.comap π)).map π = M := by
  classical
  have hKmap : (M.comap π).map π = M := Subgroup.map_comap_eq_self_of_surjective hπ M
  let S : Set ℕ := {n | ∃ L : Subgroup X, L ≤ M.comap π ∧ L.map π = M ∧ Nat.card L = n}
  have hS : S.Nonempty := ⟨Nat.card (M.comap π), M.comap π, le_rfl, hKmap, rfl⟩
  obtain ⟨L, hLK, hLmap, hcard⟩ := Nat.find_spec hS
  have hcomm_le : ⁅L, L⁆ ≤ L := commutator_le_of_le le_rfl le_rfl
  have hcomm_map : (⁅L, L⁆).map π = M := by
    rw [Subgroup.map_commutator, hLmap, hM]
  have hcomm_K : ⁅L, L⁆ ≤ M.comap π := by
    rw [← Subgroup.map_le_iff_le_comap]
    rw [hcomm_map]
  have hcard_le : Nat.card L ≤ Nat.card (⁅L, L⁆ : Subgroup X) := by
    have hmem : Nat.card (⁅L, L⁆ : Subgroup X) ∈ S := ⟨⁅L, L⁆, hcomm_K, hcomm_map, rfl⟩
    rw [hcard]
    exact Nat.find_min' hS hmem
  have hperf : ⁅L, L⁆ = L := Subgroup.eq_of_le_of_card_ge hcomm_le hcard_le
  refine le_antisymm ?_ ?_
  · calc (litPerf (M.comap π)).map π ≤ (M.comap π).map π := Subgroup.map_mono (litPerf_le _)
      _ = M := hKmap
  · calc M = L.map π := hLmap.symm
      _ ≤ (litPerf (M.comap π)).map π := Subgroup.map_mono (le_litPerf hLK hperf)

theorem lit_perfect_le_of_le_sup_solvable {H D P : Subgroup X} [D.Normal] (hH : ⁅H, H⁆ = H)
    (hP : Group.IsSolvable ↥P) (hHDP : H ≤ D ⊔ P) : H ≤ D := by
  let q : X →* X ⧸ D := QuotientGroup.mk' D
  haveI : Group.IsSolvable ↥P := hP
  have hDmap : D.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    show D ≤ q.ker
    rw [show q.ker = D from QuotientGroup.ker_mk' D]
  have hHmap_le : H.map q ≤ P.map q := by
    calc H.map q ≤ (D ⊔ P).map q := Subgroup.map_mono hHDP
      _ = D.map q ⊔ P.map q := Subgroup.map_sup D P q
      _ = P.map q := by rw [hDmap, bot_sup_eq]
  haveI : Group.IsSolvable ↥(P.map q) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective q P)
  haveI : Group.IsSolvable ↥(H.map q) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHmap_le)
  have hperf_map : ⁅H.map q, H.map q⁆ = H.map q := by
    rw [← Subgroup.map_commutator, hH]
  have hbot : H.map q = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(H.map q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsPerfect ↥(H.map q) := Subgroup.isPerfect_iff.mpr hperf_map
    exact (Group.IsPerfect.not_isSolvable ↥(H.map q)) inferInstance
  rwa [Subgroup.map_eq_bot_iff, show q.ker = D from QuotientGroup.ker_mk' D] at hbot

theorem lit_perf_le {π : X →* G} (hsolv : Group.IsSolvable ↥π.ker) {M : Subgroup G}
    {D : Subgroup X} [D.Normal] (hMD : M ≤ D.map π) : litPerf (M.comap π) ≤ D := by
  refine lit_perfect_le_of_le_sup_solvable (H := litPerf (M.comap π)) (P := π.ker)
    (litPerf_perfect _) hsolv ?_
  calc litPerf (M.comap π) ≤ M.comap π := litPerf_le _
    _ ≤ (D.map π).comap π := Subgroup.comap_mono hMD
    _ = D ⊔ π.ker := Subgroup.comap_map_eq π D

end CFSG.OddStandard.HigherRank.YamadaG23
