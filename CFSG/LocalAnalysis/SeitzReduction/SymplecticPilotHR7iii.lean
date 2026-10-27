module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotPositionBSp4B1
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {n : ℕ}

theorem spRep_ne_one (n : ℕ) (κ : SpTwoCentral) : spRep (K := K) n κ ≠ 1 := by
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_one, Fin.val_two] at h'
    omega
  rw [spRep, twoCentralRep, Ne, twoCentralElt_eq_one_iff h12]
  exact κ.params_ne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem coe_symm_mem_map_symm {C : Type*} [Group C] (e : L ≃* C) {B : Subgroup C} {x : C}
    (hx : x ∈ B) : (e.symm x : G) ∈ (B.map e.symm.toMonoidHom).map L.subtype :=
  ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩

omit [Finite G] in
theorem map_symm_trans_conj_symm {C : Type*} [Group C] (e : L ≃* C) (c : C) (B : Subgroup C) :
    ((B.map (e.trans (MulAut.conj c).symm).symm.toMonoidHom).map L.subtype : Subgroup G) =
      ((B.map (MulAut.conj c).toMonoidHom).map e.symm.toMonoidHom).map L.subtype := by
  rw [Subgroup.map_map (f := (MulAut.conj c).toMonoidHom) (g := e.symm.toMonoidHom)]
  rfl

section PlaneZero

variable [Finite K] [CharP K 2]

theorem not_normal_neighbour_rootTorusSp_zero_of_spLongRootF5 (hset : SeitzSetting G L)
    (hK : 4 ≤ Nat.card K) (hF5 : ∀ κ, SpLongRootF5 K n κ) (e : L ≃* StatedSp (n + 3) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((rootTorusSp K (0 : Fin (n + 3))).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hD : D = ((complSp K (0 : Fin (n + 3))).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  obtain ⟨f, -, hKc⟩ := exists_card_eq_two_pow (K := K)
  have hKt := inf_centralizer_eq_zpowers_of_mulEquiv hset hKc (by omega) e htC ht
  obtain ⟨-, htX, -, -, hXodd, -, hDXt, hDq, -, hZD, hOutD⟩ :=
    neighbour_data_rootTorusSp (n := n + 2) hK (by omega) e 0 htC hX hD
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_rootTorusSp (n := n + 2)
    hset.standardSetting.standard htC ht hKt hK (by omega) e 0 hX htX hD
  have hXJ : X ≤ ((longRootSp2 K (n + 3) 0).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (rootTorusSp_le_longRootSp2 0))
  obtain ⟨g, κ, -, P, hP, hPD⟩ :=
    exists_conj_eq_mul_spRep_le_centralizer_mulEquiv hset hK hF5 e ht hKt hXodd hXJ
  have hyD : (e.symm (spRep n κ) : G) ∈ D := hD ▸ coe_symm_mem_map_symm e (spRep_mem_complSp n κ)
  have hy1 : (e.symm (spRep n κ) : G) ≠ 1 := by
    intro h
    apply spRep_ne_one (K := K) n κ
    have h' : e.symm (spRep n κ) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (spRep n κ), h', map_one]
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht (hDXt.trans inf_le_left)
    hDq hZD hOutD (hDXt.trans inf_le_right) hsyl hyD hy1 (Or.inr rfl) hP (hD ▸ hPD)

end PlaneZero

section Planes

variable [Finite K] [CharP K 2]

theorem not_normal_neighbour_rootTorusSp_of_spLongRootF5 (hset : SeitzSetting G L)
    (hK : 4 ≤ Nat.card K) (hF5 : ∀ κ, SpLongRootF5 K n κ) (e : L ≃* StatedSp (n + 3) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n + 3))
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  set π : Equiv.Perm (Fin (n + 3)) := Equiv.swap 0 k with hπ
  refine not_normal_neighbour_rootTorusSp_zero_of_spLongRootF5 hset hK hF5
    (e.trans (MulAut.conj (permSp K π)).symm) htC ht ?_ ?_
  · rw [hX, map_symm_trans_conj_symm, map_conj_permSp_rootTorusSp, hπ, Equiv.swap_apply_left]
  · rw [hD, map_symm_trans_conj_symm, map_conj_permSp_complSp, hπ, Equiv.swap_apply_left]

theorem not_normal_neighbour_rootTorusSp (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K)
    (e : L ≃* StatedSp (n + 3) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (n + 3)) {X : Subgroup G}
    (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_neighbour_rootTorusSp_of_spLongRootF5 hset hK (spLongRootF5_of_four_le_card hK) e
    htC ht k hX hD

theorem not_normal_neighbour_rootTorusSp_of_three_le {m : ℕ} (hset : SeitzSetting G L)
    (hK : 4 ≤ Nat.card K) (hm : 3 ≤ m) (e : L ≃* StatedSp m K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin m)
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  exact not_normal_neighbour_rootTorusSp hset hK e htC ht k hX hD

theorem neighbour_rootTorusSp_of_three_le {m : ℕ} (hset : SeitzSetting G L)
    (hK : 4 ≤ Nat.card K) (hm : 3 ≤ m) (e : L ≃* StatedSp m K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin m)
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ∃ htX : t ∈ centralizer (X : Set G),
      CFSG.Open.IsComponentOf
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
          (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
            Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
        (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
          IsPGroup 2 U →
          U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
            Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
          Nat.card U ≤ 2) ∧
        standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) ∧
        ¬ ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨f, -, hKc⟩ := exists_card_eq_two_pow (K := K)
  have hKt := inf_centralizer_eq_zpowers_of_mulEquiv hset hKc (by omega) e htC ht
  obtain ⟨-, htX, -⟩ := neighbour_data_rootTorusSp hK (by omega) e k htC hX hD
  obtain ⟨h1, h2, h3⟩ := neighbour_standard_rootTorusSp hset.standardSetting.standard htC ht hKt
    hK (by omega) e k hX htX hD
  exact ⟨htX, h1, h2, h3, not_normal_neighbour_rootTorusSp_of_three_le hset hK hm e htC ht k hX hD⟩

end Planes

end CFSG.SeitzReduction.SymplecticPilot
