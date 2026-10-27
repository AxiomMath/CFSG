module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type*} [Group G] {L : Subgroup G}

section Transport

variable {K : Type*} [Field K] [Finite K] {n : ℕ} {a b : Fin n}
  {h : Matrix.SpecialLinearGroup (Fin n) K}

theorem layer_inf_centralizer_of_split_of_le_centralizer (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 4 ≤ n) (hh : IsRootSplit a b h) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hDX : blockSL (({a, b} : Finset (Fin n))ᶜ) ≤
      centralizer (X₀ : Set (LinearFlag.projectiveSL n K)))
    (hhX : LinearFlag.proj n K h ∈ X₀) :
    inSubgroup layer
        (L ⊓ centralizer (((X₀.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hh.ne]
  exact inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e hDX
    (fun g hg g' hg' => commutator_mem_blockSL_of_mem_centralizer_split hn hh hhX hg hg')
    (isQuasisimple_blockSL (by omega) (by omega) (Or.inr hh.four_le_card))

theorem layer_inf_centralizer_of_split (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n)
    (hh : IsRootSplit a b h) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hhX : LinearFlag.proj n K h ∈ X₀) :
    inSubgroup layer
        (L ⊓ centralizer (((X₀.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype :=
  layer_inf_centralizer_of_split_of_le_centralizer e hn hh (blockSL_compl_le_centralizer hX₀) hhX

theorem layer_inf_centralizer_rootTorus (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n)
    (hq : 4 ≤ Nat.card K) (hab : a ≠ b) :
    inSubgroup layer
        (L ⊓ centralizer ((((rootTorus (K := K) hab).map e.symm.toMonoidHom).map
          L.subtype : Subgroup G) : Set G)) =
      ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨h, hh, hhX⟩ := exists_isRootSplit_proj_mem_rootTorus (n := n) hq hab
  exact layer_inf_centralizer_of_split e hn hh (rootTorus_le_rootSL2 hab) hhX

variable [CharP K 2]

theorem eq_one_of_fix_map_split (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n)
    (hh : IsRootSplit a b h) {X D : Subgroup G}
    (hhX : ((e.symm (LinearFlag.proj n K h) : L) : G) ∈ X)
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∀ k : ℕ, β ^ 2 ^ k = 1 → β = 1 := by
  intro β hβX hβD k hβk
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_two_group_fix_split hn hh ?_ (fun x hx => ?_) (k := k) ?_
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβX _ hhX,
        MulEquiv.apply_symm_apply]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      have hmem : ((e.symm x : L) : G) ∈ D := by
        rw [hDe]
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hβD _ hmem, MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβk, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

end Transport

section Neighbour

variable [Finite G] {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem neighbour_standard_split (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {a b : Fin n}
    {h : Matrix.SpecialLinearGroup (Fin n) K} (hh : IsRootSplit a b h)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    (hhX : ((e.symm (LinearFlag.proj n K h) : L) : G) ∈ X) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
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
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hh.ne]
  have hDq : CFSG.Open.IsQuasisimple D :=
    hDe ▸ isQuasisimple_open_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_split e hn hh hhX hDe)

omit [Finite G] in
theorem neighbour_data_rootTorus (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n)
    (hq : 4 ≤ Nat.card K) {a b : Fin n} (hab : a ≠ b) {t : G} (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Odd (Nat.card X) ∧
      X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧
      CFSG.Open.IsQuasisimple D ∧ Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin (n - 2)) K) ∧
      Odd (Nat.card (center D)) ∧ Group.IsSolvable (Outer (D ⧸ center D)) := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨φ⟩ := blockSL_mulEquiv (K := K) (I := ({a, b} : Finset (Fin n))ᶜ) (by omega)
  subst hX hDe
  set ψ := (mapSymmMulEquiv e _).trans (φ.trans (reindexSpecialLinear (finCongr hcard)))
  exact ⟨map_subtype_le _, mem_centralizer_map_symm e _ htC,
    isCyclic_map_symm e (isCyclic_rootTorus hab),
    (card_map_symm e _).symm ▸ odd_card_rootTorus hab,
    map_mono (map_mono (rootTorus_le_rootSL2 hab)),
    (layer_inf_centralizer_rootTorus e (by omega) hq hab).symm,
    le_inf (map_symm_le_centralizer_map_symm e
        (blockSL_compl_le_centralizer (rootTorus_le_rootSL2 hab)))
      (map_symm_le_centralizer_singleton e _ htC),
    isQuasisimple_open_map_blockSL e (by omega) (by omega) (Or.inl (by omega)), ⟨ψ⟩,
    odd_card_center_of_mulEquiv (by omega) ψ,
    isSolvable_outer_quotient_center_of_mulEquiv (by omega) ψ⟩

theorem neighbour_standard_rootTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) (hq : 4 ≤ Nat.card K) {a b : Fin n}
    (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
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
  obtain ⟨-, -, -, -, -, hD, -⟩ := neighbour_data_rootTorus e hn hq hab htC hX hDe
  obtain ⟨h, hh, hhX⟩ := exists_isRootSplit_proj_mem_rootTorus (n := n) hq hab
  have hhX' : ((e.symm (LinearFlag.proj n K h) : L) : G) ∈ X := hX ▸ ⟨_, ⟨_, hhX, rfl⟩, rfl⟩
  exact neighbour_standard_split hL htC ht hK e hn hh htX hhX' hDe hD

end Neighbour

end CFSG.SeitzReduction.LinearPilot
