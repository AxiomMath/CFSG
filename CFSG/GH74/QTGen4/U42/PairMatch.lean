module

public import CFSG.GH74.QTGen4.U42.PairAction

public section

namespace CFSG.GH74.QTGen4.U42

variable {G G' : Type*} [Group G] [Group G']
    {H B T U : Subgroup G} {H' B' T' U' : Subgroup G'}

def pairUEquiv (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (lam : ↥B ≃* ↥B')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') : ↥U ≃* ↥U' :=
  ((Subgroup.subgroupOfEquivOfLe (h.U_le_T.trans h.T_le_B)).symm.trans
    (restrictEquiv (U.subgroupOf B) (U'.subgroupOf B') lam (fun b => hU b))).trans
      (Subgroup.subgroupOfEquivOfLe (h'.U_le_T.trans h'.T_le_B))

theorem pairUEquiv_apply (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (lam : ↥B ≃* ↥B')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') (u : ↥U) :
    ((pairUEquiv h h' lam hU u : ↥U') : G') =
      ((lam ⟨(u : G), h.T_le_B (h.U_le_T u.2)⟩ : ↥B') : G') := by
  simp only [pairUEquiv, MulEquiv.trans_apply, restrictEquiv_apply]
  rfl

theorem pairUEquiv_conj (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (lam : ↥B ≃* ↥B')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') (b : ↥B) (u : ↥U) :
    pairUEquiv h h' lam hU (conjOn h.U_normal (Subgroup.inclusion h.B_le_H b) u) =
      conjOn h'.U_normal (Subgroup.inclusion h'.B_le_H (lam b)) (pairUEquiv h h' lam hU u) := by
  apply Subtype.ext
  rw [pairUEquiv_apply]
  change ((lam ⟨(b : G) * (u : G) * (b : G)⁻¹, _⟩ : ↥B') : G') =
    ((lam b : ↥B') : G') * ((pairUEquiv h h' lam hU u : ↥U') : G') *
      ((lam b : ↥B') : G')⁻¹
  rw [pairUEquiv_apply]
  have he : (⟨(b : G) * (u : G) * (b : G)⁻¹, _⟩ : ↥B) =
      b * ⟨(u : G), h.T_le_B (h.U_le_T u.2)⟩ * b⁻¹ := Subtype.ext rfl
  rw [he, map_mul, map_mul, map_inv]
  rfl

def pairUCoords (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (e : ↥U ≃* U0) (lam : ↥B ≃* ↥B')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') : ↥U' ≃* U0 :=
  (pairUEquiv h h' lam hU).symm.trans e

theorem nuHom_lam (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (e : ↥U ≃* U0) (lam : ↥B ≃* ↥B')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') (b : ↥B) :
    nuHom h.U_normal e (Subgroup.inclusion h.B_le_H b) =
      nuHom h'.U_normal (pairUCoords h h' e lam hU) (Subgroup.inclusion h'.B_le_H (lam b)) := by
  apply MulEquiv.ext
  intro y
  change e (conjOn h.U_normal (Subgroup.inclusion h.B_le_H b) (e.symm y)) =
    e ((pairUEquiv h h' lam hU).symm
      (conjOn h'.U_normal (Subgroup.inclusion h'.B_le_H (lam b))
        (pairUEquiv h h' lam hU (e.symm y))))
  rw [← pairUEquiv_conj h h' lam hU, MulEquiv.symm_apply_apply]

theorem map_T_nuHom_eq (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (e : ↥U ≃* U0) (lam : ↥B ≃* ↥B')
    (hT : ∀ b : ↥B, (b : G) ∈ T ↔ ((lam b : ↥B') : G') ∈ T')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') :
    (T.subgroupOf H).map (nuHom h.U_normal e) =
      (T'.subgroupOf H').map (nuHom h'.U_normal (pairUCoords h h' e lam hU)) := by
  apply le_antisymm
  · rintro a ⟨t, ht, rfl⟩
    let b : ↥B := ⟨(t : G), h.T_le_B ht⟩
    refine ⟨Subgroup.inclusion h'.B_le_H (lam b), (hT b).mp ht, ?_⟩
    exact (nuHom_lam h h' e lam hU b).symm
  · rintro a ⟨t, ht, rfl⟩
    let b' : ↥B' := ⟨(t : G'), h'.T_le_B ht⟩
    let b : ↥B := lam.symm b'
    have hb : (b : G) ∈ T := (hT b).mpr (by
      change ((lam (lam.symm b') : ↥B') : G') ∈ T'
      rw [MulEquiv.apply_symm_apply]
      exact ht)
    refine ⟨Subgroup.inclusion h.B_le_H b, hb, ?_⟩
    have htval : Subgroup.inclusion h'.B_le_H (lam b) = t := by
      apply Subtype.ext
      change ((lam (lam.symm b') : ↥B') : G') = (t : G')
      rw [MulEquiv.apply_symm_apply]
    simpa only [htval] using (nuHom_lam h h' e lam hU b)

theorem pair_action_range_eq [Finite G] [Finite G']
    (h : PairCore H B T U) (h' : PairCore H' B' T' U') (e : ↥U ≃* U0) (lam : ↥B ≃* ↥B')
    (hT : ∀ b : ↥B, (b : G) ∈ T ↔ ((lam b : ↥B') : G') ∈ T')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') :
    (nuHom h.U_normal e).range = (nuHom h'.U_normal (pairUCoords h h' e lam hU)).range := by
  let f := nuHom h.U_normal e
  let e' := pairUCoords h h' e lam hU
  let f' := nuHom h'.U_normal e'
  obtain ⟨P, hP, hPa, hPT⟩ := exists_pair_action_three h e
  obtain ⟨P', hP', hPa', hPT'⟩ := exists_pair_action_three h' e'
  have hf : f.range = P.map f ⊔ (T.subgroupOf H).map f := by
    rw [← Subgroup.map_sup, hPT, Subgroup.map_top]
  have hf' : f'.range = P'.map f' ⊔ (T'.subgroupOf H').map f' := by
    rw [← Subgroup.map_sup, hPT', Subgroup.map_top]
  have hm : (T.subgroupOf H).map f = (T'.subgroupOf H').map f' := map_T_nuHom_eq h h' e lam hT hU
  rw [hf, hf', ← hm]
  exact three_part_sup_eq (P.map f) (P'.map f') ((T.subgroupOf H).map f) hPa hPa'
    (inner_le_map_T h e)

end CFSG.GH74.QTGen4.U42
