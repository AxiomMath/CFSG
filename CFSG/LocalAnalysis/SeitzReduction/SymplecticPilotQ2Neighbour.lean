module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR8
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR8RootTorus
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv)
open CFSG.SeitzReduction.F4Pilot (HasBLift)
open CFSG.Blueprint (LieModel)

variable {K : Type} [Field K] {n : ℕ}

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} [Finite K] [CharP K 2]

theorem eq_one_of_fix_map_nsTorusSp (hK : Nat.card K = 2) (hn : 2 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1)) {X D : Subgroup G}
    (hX : ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((complSp K k).map e.symm.toMonoidHom).map L.subtype ≤ D) :
    ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∀ m : ℕ, β ^ 2 ^ m = 1 → β = 1 := by
  intro β hβX hβD m hβm
  have key : MulAut.congr e β = 1 :=
    eq_one_of_two_pow_fix_nsTorusSp hK hn k (congr_apply_eq_of_fix e hX hβX)
      (congr_apply_eq_of_fix e hD hβD) (m := m) (by rw [← map_pow, hβm, map_one])
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem exists_mem_map_nsTorusSp_eq_conj_of_fix (hK : Nat.card K = 2) (hn : 2 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1)) {X D : Subgroup G}
    (hX : ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hD : ((complSp K k).map e.symm.toMonoidHom).map L.subtype ≤ D) (β : MulAut L)
    (hβX : ∀ x : L, (x : G) ∈ X → β x = x) (hβD : ∀ x : L, (x : G) ∈ D → β x = x) :
    ∃ y : L, (y : G) ∈ ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype ∧
      β = MulAut.conj y := by
  obtain ⟨x, hx, hβ'⟩ := exists_mem_nsTorusSp_eq_conj_of_fix hK hn k
    (congr_apply_eq_of_fix e hX hβX) (congr_apply_eq_of_fix e hD hβD)
  exact ⟨e.symm x, ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩, eq_conj_symm_of_congr_eq_conj e hβ'⟩

theorem mem_of_odd_of_mem_centralizer_nsTorusSp [Finite G] {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hK : Nat.card K = 2) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X D : Subgroup G} (hXe : X = ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  intro c hc hco
  have hXo : Odd (Nat.card X) := by
    rw [hXe, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact odd_card_nsTorusSp k
  refine LinearPilot.mem_of_forall_fix_eq_conj htC ht hLt hKt (D := X ⊔ D) hXo
    (fun β hβ => ?_) hc.1.2 (mem_centralizer_sup hc.1.1 hc.2) hco
  rw [hXe]
  exact exists_mem_map_nsTorusSp_eq_conj_of_fix hK hn e k (hXe ▸ le_rfl) (hDe ▸ le_rfl) β
    (fun x hx => hβ x (mem_sup_left hx)) (fun x hx => hβ x (mem_sup_right hx))

end Transport

section Neighbour

variable {G : Type*} [Group G] {L : Subgroup G} [Finite K] [CharP K 2]

theorem neighbour_data_nsTorusSp (hK : Nat.card K = 2) (hn : 3 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1)) {t : G} (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G} (hX : X = ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Nat.card X = 3 ∧
      Odd (Nat.card X) ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧
      CFSG.Open.IsQuasisimple D ∧ Nonempty (D ≃* StatedSp n K) ∧ center D = ⊥ ∧
      Group.IsSolvable (Outer D) := by
  subst hX hDe
  set ψ : (((complSp K k).map e.symm.toMonoidHom).map L.subtype : Subgroup G) ≃* StatedSp n K :=
    (LinearPilot.mapSymmMulEquiv e (complSp K k)).trans (complSpEquiv k).symm
  have hXc : Nat.card (((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype : Subgroup G) =
      3 := (LinearPilot.card_map_symm e _).trans (card_nsTorusSp k)
  have : Group.IsSolvable (Outer (StatedSp n K)) := isSolvable_outer_statedSp (by omega)
  exact ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.isCyclic_map_symm e (isCyclic_nsTorusSp k), hXc, hXc ▸ (by decide),
    (layer_inf_centralizer_nsTorusSp hK hn e k).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e (complSp_le_centralizer_nsTorusSp k))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    isQuasisimple_open_map_complSp_two hK hn e k, ⟨ψ⟩,
    center_eq_bot_of_mulEquiv ψ (center_statedSp_eq_bot n), solvable_of_equiv ψ.symm⟩

variable [Finite G]

theorem neighbour_standard_nsTorusSp (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
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
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨-, -, -, -, -, hD, -, hDq, -⟩ := neighbour_data_nsTorusSp hK hn e k htC hX hDe
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hKt htX hD hDq
    (eq_one_of_fix_map_nsTorusSp hK (by omega) e k hX.ge hDe.ge)

theorem bLift_neighbour_nsTorusSp (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  obtain ⟨-, -, -, -, -, hD, -⟩ := neighbour_data_nsTorusSp hK hn e k htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_complSp_two hK hn e k
  have hmax := mem_of_odd_of_mem_centralizer_nsTorusSp htC ht hLt hKt hK (by omega) e k hX hDe
  exact ⟨hmax,
    LinearPilot.mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hmax,
    fun E hE htE hEt => LinearPilot.hasBLift_of_forall_odd_mem htC ht hLt htX hD hDq hmax hE htE
      hEt⟩

end Neighbour

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_standard_nsTorusSp_of_seitzSetting (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
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
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
  exact neighbour_standard_nsTorusSp hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_of_mulEquiv hset (f := 1) (by rw [hK, pow_one]) (by omega) e htC
      ht) hK hn e k hX htX hDe

theorem bLift_neighbour_nsTorusSp_of_seitzSetting (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
  exact bLift_neighbour_nsTorusSp hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_of_mulEquiv hset (f := 1) (by rw [hK, pow_one]) (by omega) e htC
      ht) hK hn e k hX htX hDe

theorem neighbour_overgroup_nsTorusSp_of_not_normal (hcat : Sp2mCatalogueClausesAt n)
    (hset : SeitzSetting G L) (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    ∃ htX : t ∈ centralizer (X : Set G),
      NeighbourOvergroupSp2m (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) n 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, htX, -, hXcard, -, -, hDXt, -, ⟨ψ⟩, -, -⟩ :=
    neighbour_data_nsTorusSp hK hn e k htC hX hD
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_nsTorusSp_of_seitzSetting hset hK hn e htC ht k hX htX hD
  have hDm : LieModel D .PSp n 2 1 :=
    lieModel_of_mulEquiv_statedSp ψ hKc (by omega)
      (fun h => by simp only [Prod.mk.injEq] at h; omega)
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hXcard
    omega
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_bot_of_simple hset.standardSetting.simple
      hset.standardSetting.nonab hXne
  exact ⟨htX, neighbour_overgroup_sp2m hcat hset.standardSetting.kProper hXG htX ht
    (hDXt.trans inf_le_left) hDm hcomp hsyl hstd hnn⟩

end Setting

end CFSG.SeitzReduction.SymplecticPilot
