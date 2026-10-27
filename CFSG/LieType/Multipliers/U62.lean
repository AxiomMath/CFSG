module

public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Cover
public import CFSG.LieType.Multipliers.U62Action

public section

namespace CFSG.LieType.Multipliers.U62

open Subgroup CFSG.CosetTable CFSG.Fischer CFSG.Open

private theorem mk_append (u v : List (Fin 5 × Bool)) {G : Type*} [Group G]
    (φ : FreeGroup (Fin 5) →* G) : φ (FreeGroup.mk (u ++ v)) = φ (FreeGroup.mk u) *
      φ (FreeGroup.mk v) := by
  rw [← FreeGroup.mul_mk, map_mul]

private theorem mk_pow_three {G : Type*} [Group G] (φ : FreeGroup (Fin 5) →* G)
    (u : List (Fin 5 × Bool)) :
    φ (FreeGroup.mk (u ++ u ++ u)) = φ (FreeGroup.mk u) ^ 3 := by
  rw [mk_append, mk_append, pow_three, mul_assoc]

private theorem mk_pow_two {G : Type*} [Group G] (φ : FreeGroup (Fin 5) →* G)
    (u : List (Fin 5 × Bool)) :
    φ (FreeGroup.mk (u ++ u)) = φ (FreeGroup.mk u) ^ 2 := by
  rw [mk_append, sq]

private theorem kerThree_mem : kerThree ∈ rels := by decide

private theorem kerTwo_mem : kerTwo ∈ rels := by decide

private theorem kerSix_mem : kerSix ∈ rels := by decide

theorem multiplier_PSU_six_two
    (X : Type) [Group X] (h : CFSG.Blueprint.LieModel X .PSU 6 2 1) :
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃* Multiplicative (ZMod 3 × ZMod 2 × ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_T46 h
  set g : Fin 5 → X := fun i => e.symm (genE i) with hg
  have hP : IsPresentation g (wordSet rels) := isPresentation_T46.mulEquiv e.symm
  have hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (coverPairs i))) = g i := fun i => by
    rw [hg, lift_mulEquiv, lift_genE_comm]
  set w : Fin 5 → FreeGroup (Fin 5) := fun i => FreeGroup.mk (commWords (coverPairs i))
  have hw : ∀ i, w i ∈ commutator (FreeGroup (Fin 5)) := fun i => mk_commWords_mem_commutator _
  refine ⟨(isPerfect_of_isPresentation hP hw hwg).commutator_eq_top, ?_⟩
  have hX : Nat.card X = 9196830720 := by rw [Nat.card_congr e.toEquiv, card_T46]
  obtain ⟨hfin, hle⟩ := cover_card_le
  obtain ⟨E, _, ψ, hfix, hmove⟩ := kernel_hom
  set mkP := PresentedGroup.mk {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk}
  set z₃ := ψ (mkP (FreeGroup.mk kerThree))
  set z₂ := ψ (mkP (FreeGroup.mk kerTwo))
  set z₂' := ψ (mkP (FreeGroup.mk kerTwo'))
  have hcen : ∀ r ∈ rels, mkP (FreeGroup.mk r) ∈ center (PG 5 coverWs) := by
    intro r hr
    have hS := coverRelators_wordSet rels fun i => commWords (coverPairs i)
    have key : ∀ S : Set (FreeGroup (Fin 5)), S = coverRelators (wordSet rels) w →
        S = {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk} →
        PresentedGroup.mk S (FreeGroup.mk r) ∈ center (PresentedGroup S) := by
      rintro S rfl -
      exact mk_mem_center w (List.mem_map_of_mem hr)
    exact key _ hS.symm rfl
  have hcomm : ∀ r ∈ rels, ∀ r' ∈ rels, Commute (ψ (mkP (FreeGroup.mk r)))
      (ψ (mkP (FreeGroup.mk r'))) := fun r hr r' hr' =>
    (show Commute (mkP (FreeGroup.mk r)) (mkP (FreeGroup.mk r')) from
      (Subgroup.mem_center_iff.mp (hcen r hr) _).symm).map ψ
  have hz₂' : z₂' = ψ (mkP (FreeGroup.mk kerSix)) ^ 3 := by
    exact mk_pow_three (ψ.comp mkP) kerSix
  obtain ⟨φ, hφ, hrange⟩ := exists_injective_three_two_two (x := z₂) (y := z₂') (z := z₃)
    (by rw [hz₂']; exact (hcomm _ kerTwo_mem _ kerSix_mem).pow_right 3)
    (hcomm _ kerThree_mem _ kerTwo_mem)
    (by rw [hz₂']; exact (hcomm _ kerThree_mem _ kerSix_mem).pow_right 3)
    (by
      change (ψ.comp mkP) (FreeGroup.mk _) ^ 2 = 1
      rw [← mk_pow_two]
      exact hfix _ (by simp [fixWords]))
    (by
      change (ψ.comp mkP) (FreeGroup.mk _) ^ 2 = 1
      rw [← mk_pow_two]
      exact hfix _ (by simp [fixWords]))
    (by
      change (ψ.comp mkP) (FreeGroup.mk _) ^ 3 = 1
      rw [← mk_pow_three]
      exact hfix _ (by simp [fixWords]))
    (hmove _ (by simp [moveWords])) (hmove _ (by simp [moveWords]))
    (by
      change (ψ.comp mkP) (FreeGroup.mk _) * (ψ.comp mkP) (FreeGroup.mk _) ≠ 1
      rw [← mk_append]
      exact hmove _ (by simp [moveWords]))
    (hmove _ (by simp [moveWords]))
  set e' : Fin 5 → E := fun i => ψ (PresentedGroup.of i)
  have hlift : FreeGroup.lift e' = ψ.comp mkP :=
    FreeGroup.ext_hom _ _ fun i => by simp [e', mkP]; rfl
  have hS := coverRelators_wordSet rels fun i => commWords (coverPairs i)
  have he : ∀ r ∈ coverRelators (wordSet rels) w, FreeGroup.lift e' r = 1 := by
    intro r hr
    rw [show coverRelators (wordSet rels) w = wordSet coverWs from hS] at hr
    rw [hlift, MonoidHom.comp_apply, PresentedGroup.one_of_mem hr, map_one]
  set T : Set (FreeGroup (Fin 5)) :=
    {FreeGroup.mk kerThree, FreeGroup.mk kerTwo, FreeGroup.mk kerTwo'}
  have hT : ∀ t ∈ T, FreeGroup.lift g t = 1 := by
    rintro t (rfl | rfl | rfl)
    · exact hP.lift_eq_one (List.mem_map_of_mem kerThree_mem)
    · exact hP.lift_eq_one (List.mem_map_of_mem kerTwo_mem)
    · rw [kerTwo', mk_pow_three, hP.lift_eq_one (List.mem_map_of_mem kerSix_mem), one_pow]
  have hmemT : ∀ t ∈ T, ψ (mkP t) ∈ closure (FreeGroup.lift e' '' T) := fun t ht =>
    subset_closure ⟨t, ht, by rw [hlift, MonoidHom.comp_apply]⟩
  have hK : φ.range ≤ closure (FreeGroup.lift e' '' T) :=
    hrange _ (hmemT _ (by simp [T])) (hmemT _ (by simp [T])) (hmemT _ (by simp [T]))
  have hK₀ : Nat.card φ.range = 12 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    simp
  have hfinP : Finite (PresentedCover (wordSet rels) w) := by
    rw [PresentedCover, show coverRelators (wordSet rels) w = wordSet coverWs from hS]
    exact hfin
  have hcard : Nat.card (PresentedCover (wordSet rels) w) ≤ 12 * Nat.card X := by
    rw [PresentedCover, show coverRelators (wordSet rels) w = wordSet coverWs from hS, hX]
    exact hle
  obtain ⟨iso⟩ := nonempty_griessHopfMultiplier_mulEquiv_closure hP hw hwg hcard he hT hK₀ hK
  exact ⟨iso.trans (MonoidHom.ofInjective hφ).symm⟩

end CFSG.LieType.Multipliers.U62
