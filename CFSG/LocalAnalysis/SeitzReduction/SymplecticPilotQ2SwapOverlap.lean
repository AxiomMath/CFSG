module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

variable {K : Type} [Field K] {n : ℕ}

theorem complSp_inf_complSp (i j : Fin n) :
    complSp K i ⊓ complSp K j = spBlock K ({i, j}ᶜ : Finset (Fin n)) := by
  ext x
  rw [mem_inf, complSp, complSp, spBlock, mem_suppGroup_iff (parClosed_coords i).compl,
    mem_suppGroup_iff (parClosed_coords j).compl, mem_suppGroup_iff (parClosed_planeCoords _)]
  have key : ∀ (t : Fin n ⊕ Fin n) (k : Fin n), t ∉ (coords k)ᶜ ↔ planeOf t = k := by
    intro t k
    rw [Set.mem_compl_iff, not_not]
    exact ⟨planeOf_eq_of_mem_coords, fun h => h ▸ mem_coords_planeOf t⟩
  have key' : ∀ t : Fin n ⊕ Fin n,
      t ∉ planeCoords ({i, j}ᶜ : Finset (Fin n)) ↔ planeOf t = i ∨ planeOf t = j := by
    intro t
    rw [mem_planeCoords, Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩ t ht r
    rcases (key' t).1 ht with h | h
    · exact h1 t ((key t i).2 h) r
    · exact h2 t ((key t j).2 h) r
  · intro h
    exact ⟨fun t ht r => h t ((key' t).2 (Or.inl ((key t i).1 ht))) r,
      fun t ht r => h t ((key' t).2 (Or.inr ((key t j).1 ht))) r⟩

theorem nsTorusSp_le_complSp {i k : Fin n} (hki : k ≠ i) : nsTorusSp K k ≤ complSp K i := by
  refine (nsTorusSp_le_longRootSp2 k).trans ?_
  rw [← spBlock_singleton, ← spBlock_compl_singleton]
  refine spBlock_mono fun x hx => ?_
  rw [Finset.mem_singleton] at hx
  rw [Finset.mem_compl, Finset.mem_singleton]
  exact hx ▸ hki

theorem perfectCore_complSp_inf_centralizer_nsTorusSp [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (i j : Fin n) :
    perfectCore (complSp K i ⊓ centralizer (nsTorusSp K j : Set (StatedSp n K))) =
      perfectCore (spBlock K ({i, j}ᶜ : Finset (Fin n))) := by
  set H := complSp K i ⊓ centralizer (nsTorusSp K j : Set (StatedSp n K)) with hH
  have hcomm : ⁅H, H⁆ ≤ spBlock K ({i, j}ᶜ : Finset (Fin n)) := by
    rw [← complSp_inf_complSp]
    refine commutator_le.2 fun g hg g' hg' => mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg.1 hg'.1) (inv_mem hg.1)) (inv_mem hg'.1)
    · rw [commutatorElement_def]
      exact commutator_mem_complSp_of_mem_centralizer_nsTorusSp hK j hg.2 hg'.2
  have hle : spBlock K ({i, j}ᶜ : Finset (Fin n)) ≤ H := by
    rw [← complSp_inf_complSp]
    exact inf_le_inf_left _ (complSp_le_centralizer_nsTorusSp j)
  apply le_antisymm
  · refine le_perfectCore_of_perfect ?_ (perfectCore_perfect H)
    calc perfectCore H = ⁅perfectCore H, perfectCore H⁆ := (perfectCore_perfect H).symm
      _ ≤ ⁅H, H⁆ := commutator_mono (perfectCore_le H) (perfectCore_le H)
      _ ≤ _ := hcomm
  · exact le_perfectCore_of_perfect ((perfectCore_le _).trans hle) (perfectCore_perfect _)

omit [Field K] in
theorem nonempty_statedSp_mulEquiv_perm_of_eq [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : m = 2) : Nonempty (StatedSp m K ≃* Equiv.Perm (Fin 6)) := by
  subst hm
  have : Fintype K := Fintype.ofFinite K
  exact CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (by rw [← Nat.card_eq_fintype_card]; exact hK)

theorem perfectCore_spBlock_of_card_two [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {N : Finset (Fin n)} (hN : 2 ≤ N.card) :
    IsSimpleGroup (perfectCore (spBlock K N)) ∧ center (perfectCore (spBlock K N)) = ⊥ ∧
      ⁅spBlock K N, spBlock K N⁆ ≤ perfectCore (spBlock K N) := by
  rcases Nat.lt_or_ge N.card 3 with h2 | h3
  ·
    obtain ⟨e6⟩ := nonempty_statedSp_mulEquiv_perm_of_eq hK (m := N.card) (by omega)
    obtain ⟨ψ⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating
      ((spBlockEquiv N).symm.trans e6)
    have hA6 : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    have hCp : Group.IsPerfect (⁅spBlock K N, spBlock K N⁆ : Subgroup (StatedSp n K)) :=
      Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
    have hCperf := isPerfect_iff.mp hCp
    have hcore : perfectCore (spBlock K N) = ⁅spBlock K N, spBlock K N⁆ :=
      le_antisymm (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1)
        (le_perfectCore_of_perfect (commutator_le_self _) hCperf)
    have hS : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    refine ⟨?_, ?_, hcore.symm.le⟩
    · rw [hcore]
      exact ψ.isSimpleGroup
    · rw [hcore]
      exact F4Pilot.center_eq_bot_congr ψ.symm (alternatingGroup.center_eq_bot (by simp))
  ·
    have hq : CFSG.IsQuasisimple (spBlock K N) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (spBlockEquiv N)
        (CFSG.LieType.Universal.Symplectic.isQuasisimple N.card K (by omega)
          (Or.inr (Or.inr ⟨hK, h3⟩)))
    have hperf : ⁅spBlock K N, spBlock K N⁆ = spBlock K N := isPerfect_iff.mp hq.1
    have hcore : perfectCore (spBlock K N) = spBlock K N :=
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf
    have hZ : center (spBlock K N) = ⊥ := center_spBlock_eq_bot N
    have : IsSimpleGroup (spBlock K N ⧸ center (spBlock K N)) := hq.2.1
    refine ⟨?_, ?_, ?_⟩
    · rw [hcore]
      exact ((QuotientGroup.quotientBot (G := spBlock K N)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup
    · rw [hcore]
      exact hZ
    · rw [hperf, hcore]

theorem card_compl_pair_planes {i j : Fin n} (hij : i ≠ j) :
    (({i, j}ᶜ : Finset (Fin n))).card = n - 2 := by
  rw [Finset.card_compl, Finset.card_pair hij, Fintype.card_fin]

theorem perfectCore_modelToG_complSp_inf_centralizer_nsTorusSp {G : Type} [Group G] [Finite G]
    {L : Subgroup G} [Finite K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* StatedSp n K)
    (i j : Fin n) :
    perfectCore (modelToG e (complSp K i) ⊓ centralizer (modelToG e (nsTorusSp K j) : Set G)) =
      modelToG e (perfectCore (spBlock K ({i, j}ᶜ : Finset (Fin n)))) := by
  rw [OmegaPilot.perfectCore_modelToG_inf_centralizer,
    perfectCore_complSp_inf_centralizer_nsTorusSp hK]

end CFSG.SeitzReduction.SymplecticPilot
