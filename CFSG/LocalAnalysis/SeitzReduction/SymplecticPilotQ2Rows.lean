module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRowsTransport
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMainInputs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

@[expose] def NsKindSp (e : L ≃* StatedSp (n + 1) K) (t : G) (k : Fin (n + 1)) (κ : Sp2mKind) :
    Prop :=
  HR8KindAtSp t n 1 (modelToG e (nsTorusSp K k)) (modelToG e (complSp K k)) κ

theorem nsKindSp_perm [Finite G] (e : L ≃* StatedSp (n + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (π : Equiv.Perm (Fin (n + 1))) {k : Fin (n + 1)}
    {κ : Sp2mKind} (h : NsKindSp e t k κ) : NsKindSp e t (π k) κ := by
  have h1 := HR8KindAtSp.map_mulEquiv (MulAut.conj ((e.symm (permSp K π) : L) : G)) h
  have hwt : MulAut.conj ((e.symm (permSp K π) : L) : G) t = t := by
    rw [MulAut.conj_apply, mem_centralizer_iff.mp htC _ (e.symm (permSp K π)).2,
      mul_inv_cancel_right]
  have hX : (modelToG e (nsTorusSp K k)).map
      (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom =
      modelToG e (nsTorusSp K (π k)) := by
    rw [← UnitaryPilot.modelToG_map_conj, map_conj_permSp_nsTorusSp]
  have hD : (modelToG e (complSp K k)).map
      (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom =
      modelToG e (complSp K (π k)) := by
    rw [← UnitaryPilot.modelToG_map_conj, map_conj_permSp_complSp]
  rw [hwt, hX, hD] at h1
  exact h1

theorem nsKindSp_iff [Finite G] (e : L ≃* StatedSp (n + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (k l : Fin (n + 1)) (κ : Sp2mKind) :
    NsKindSp e t k κ ↔ NsKindSp e t l κ := by
  constructor
  · intro h
    have h' := nsKindSp_perm e htC (Equiv.swap k l) h
    rwa [Equiv.swap_apply_left] at h'
  · intro h
    have h' := nsKindSp_perm e htC (Equiv.swap k l) h
    rwa [Equiv.swap_apply_right] at h'

theorem exists_nsKindSp_of_not_normal [Finite G] [Finite K] (hcat : Sp2mCatalogueClausesAt n)
    (hset : SeitzSetting G L) (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n + 1))
    (hnn : ¬ (((modelToG e (complSp K k)).subgroupOf
        (centralizer (modelToG e (nsTorusSp K k) : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e (nsTorusSp K k) : Set G))))).Normal) :
    ∃ κ : Sp2mKind, NsKindSp e t k κ := by
  obtain ⟨htX, h⟩ := neighbour_overgroup_nsTorusSp_of_not_normal hcat hset hK hn e htC ht k
    (X := modelToG e (nsTorusSp K k)) rfl (D := modelToG e (complSp K k)) rfl hnn
  exact exists_hr8KindAtSp_of_neighbourOvergroupSp2m htX h

@[expose] def SpTwoPositionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 3 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 → t ∈ centralizer (L : Set G) →
      ¬ (((modelToG e (complSp K 0)).subgroupOf
          (centralizer (modelToG e (nsTorusSp K 0) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e (nsTorusSp K 0) : Set G))))).Normal

@[expose] def SpTwoRowInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 3 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → False

theorem spTwoInput_of_rows (hcat : ∀ m : ℕ, 3 ≤ m → Sp2mCatalogueClausesAt m)
    (hpos : SpTwoPositionInput) (hrows : ∀ κ : Sp2mKind, SpTwoRowInput κ) : SpTwoInput := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 3 ≤ m := by omega
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨κ, hκ⟩ := exists_nsKindSp_of_not_normal (hcat m hm) hset hK hm e htC ht 0
    (hpos G L hset m K hK hm e t ht htC)
  exact hrows κ G L hset m K hK hm e t ht hKt fun k => (nsKindSp_iff e htC 0 k κ).1 hκ

end CFSG.SeitzReduction.SymplecticPilot
