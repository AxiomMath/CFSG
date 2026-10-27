module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_exists_T {G : Type} [Group G] [Finite G] {t : G} {X R : Subgroup G}
    (hR : IsSylow2Of R (X ⊓ centralizer ({t} : Set G))) :
    ∃ T : Subgroup G, IsSylow2Of T X ∧ R ≤ T ∧ T ⊓ centralizer ({t} : Set G) = R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  set Y : Subgroup G := X ⊓ C
  have hRX : R ≤ X := hR.1.trans inf_le_left
  have hRC : R ≤ C := hR.1.trans inf_le_right
  have hRpg : IsPGroup 2 (R.subgroupOf X) :=
    hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm
  obtain ⟨Q, hRQ⟩ := hRpg.exists_le_sylow
  let T : Subgroup G := (Q : Subgroup ↥X).map X.subtype
  have hT : IsSylow2Of T X := isSylow2Of_map_sylow Q
  have hRT : R ≤ T := by
    calc R = (R.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hRX).symm
      _ ≤ (Q : Subgroup ↥X).map X.subtype := Subgroup.map_mono hRQ
  have hTX : T ≤ X := Subgroup.map_subtype_le _
  obtain ⟨P, hP⟩ := hR.exists_sylow
  have hTY : T ⊓ C ≤ Y := inf_le_inf_right C hTX
  have hKpg : IsPGroup 2 ((T ⊓ C).subgroupOf Y) :=
    (hT.2.1.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hPK : (P : Subgroup ↥Y) ≤ (T ⊓ C).subgroupOf Y := by
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact hRT (hP ▸ ⟨x, hx, rfl⟩ : Y.subtype x ∈ R)
    · exact hRC (hP ▸ ⟨x, hx, rfl⟩ : Y.subtype x ∈ R)
  have hKeq : (T ⊓ C).subgroupOf Y = (P : Subgroup ↥Y) := P.is_maximal' hKpg hPK
  have hTCeq : T ⊓ C = R := by
    calc T ⊓ C = ((T ⊓ C).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hTY).symm
      _ = ((P : Subgroup ↥Y)).map Y.subtype := by rw [hKeq]
      _ = R := hP
  exact ⟨T, hT, hRT, hTCeq⟩

end CFSG.OddStandard.SmallF3.Omega
