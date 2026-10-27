module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Reduction

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B : Subgroup G} {z : G}

section

variable (H : ThCyc G L R t) {SL : Subgroup G} (hS : IsThSylow L SL)

include H hS

theorem ThCyc.not_two_dvd_relIndex_centralizer {K : Subgroup G} (hK : SL ⊔ R ≤ K) :
    ¬ 2 ∣ K.relIndex (centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  have hSC : SL ⊔ R ≤ C := H.sup_le_centralizer hS
  have hker : IsPGroup 2 C.subtype.ker := by
    rw [Subgroup.ker_subtype]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hP : IsPGroup 2 ↥((SL ⊔ R).subgroupOf C) :=
    IsPGroup.comap_of_ker_isPGroup (H.pgroup_sup hS) C.subtype hker
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hQle : (Q : Subgroup ↥C).map C.subtype ≤ SL ⊔ R := by
    refine H.sup_max hS (X := (Q : Subgroup ↥C).map C.subtype) ?_ (Q.isPGroup'.map _) ?_
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · intro x hx
      exact ⟨⟨x, hSC hx⟩, hQ hx, rfl⟩
  have hQeq : (SL ⊔ R).subgroupOf C = (Q : Subgroup ↥C) := by
    refine le_antisymm hQ (fun y hy => ?_)
    exact hQle ⟨y, hy, rfl⟩
  have hodd : ¬ 2 ∣ ((SL ⊔ R).subgroupOf C).index := by
    rw [hQeq]
    exact Sylow.not_dvd_index Q
  intro hdvd
  apply hodd
  refine dvd_trans hdvd ?_
  exact Subgroup.index_dvd_of_le fun y hy =>
    Subgroup.mem_subgroupOf.2 (hK (Subgroup.mem_subgroupOf.1 hy))

end

end CFSG.EvenSporadicStandard.ThStd
