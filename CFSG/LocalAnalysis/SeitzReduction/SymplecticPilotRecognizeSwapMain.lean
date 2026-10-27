module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Coherent

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G}

theorem compl_pair_nonempty (hn : 3 ≤ n) (a b : Fin n) : ({a, b}ᶜ : Finset (Fin n)).Nonempty := by
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne_of_three_le hn a b
  exact ⟨c, mem_compl_pair_iff'.2 ⟨hca, hcb⟩⟩

theorem compl_triple_nonempty (hn : 4 ≤ n) (a b c : Fin n) :
    ({a, b, c}ᶜ : Finset (Fin n)).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
  intro h
  have h1 := Finset.card_insert_le a ({b, c} : Finset (Fin n))
  have h2 := Finset.card_insert_le b ({c} : Finset (Fin n))
  rw [Finset.card_singleton] at h2
  rw [h, Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem subset_compl_singleton_of_notMem' {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I) :
    I ⊆ ({k}ᶜ : Finset (Fin n)) :=
  fun _ hx => mem_compl_singleton_iff'.2 fun h => hk (h ▸ hx)

theorem isQuasisimple_spBlock_compl [Finite K] (hK : 4 ≤ Nat.card K) {I : Finset (Fin n)}
    {k : Fin n} (hk : k ∉ I) (hI : I.Nonempty) :
    CFSG.Open.IsQuasisimple ((spBlock K I).subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))) :=
  isQuasisimple_spBlock_subgroupOf hK (subset_compl_singleton_of_notMem' hk) hI

theorem exists_coherent_swapParam [Finite G] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) (P : ∀ k : Fin n, SwapNeighbourParam e t k) :
    ∃ Q : ∀ k : Fin n, SwapNeighbourParam e t k, ∀ k l : Fin n,
      (Q k).fstF (spBlock K ({k, l}ᶜ : Finset (Fin n))) =
        (Q l).fstF (spBlock K ({k, l}ᶜ : Finset (Fin n))) := by
  classical
  set o : Fin n := ⟨0, by omega⟩ with ho
  have hpiece : ∀ {k k' : Fin n} (R : SwapNeighbourParam e t k) (R' : SwapNeighbourParam e t k')
      {I : Finset (Fin n)}, k ∉ I → k' ∉ I →
      R.fstF (spBlock K I) ⊔ R.sndF (spBlock K I) = R'.fstF (spBlock K I) ⊔ R'.sndF (spBlock K I) :=
    fun R R' _ hk hk' => by
      rw [R.fstF_sup_sndF_eq_planeCore hK hk, R'.fstF_sup_sndF_eq_planeCore hK hk']
  have hnp : ∀ a b : Fin n, a ∉ ({a, b}ᶜ : Finset (Fin n)) := fun a b h =>
    (mem_compl_pair_iff'.1 h).1 rfl
  have hnp' : ∀ a b : Fin n, b ∉ ({a, b}ᶜ : Finset (Fin n)) := fun a b h =>
    (mem_compl_pair_iff'.1 h).2 rfl
  let Q : ∀ k : Fin n, SwapNeighbourParam e t k := fun k =>
    if (P k).fstF (spBlock K ({o, k}ᶜ : Finset (Fin n))) =
      (P o).fstF (spBlock K ({o, k}ᶜ : Finset (Fin n))) then P k else (P k).flip
  have hQoo : Q o = P o := ite_eq_left rfl
  have hQo : ∀ k : Fin n, (Q k).fstF (spBlock K ({o, k}ᶜ : Finset (Fin n))) =
      (P o).fstF (spBlock K ({o, k}ᶜ : Finset (Fin n))) := by
    intro k
    by_cases hc : (P k).fstF (spBlock K ({o, k}ᶜ : Finset (Fin n))) =
        (P o).fstF (spBlock K ({o, k}ᶜ : Finset (Fin n)))
    · change (if _ then P k else (P k).flip).fstF _ = _
      rw [ite_eq_left hc]
      exact hc
    · change (if _ then P k else (P k).flip).fstF _ = _
      rw [ite_eq_right hc, SwapNeighbourParam.flip_fstF]
      have hI := compl_pair_nonempty (by omega) o k
      rcases (P o).fstF_eq_or_eq (P k) (isQuasisimple_spBlock_compl hK (hnp o k) hI)
        (isQuasisimple_spBlock_compl hK (hnp' o k) hI) (hpiece _ _ (hnp o k) (hnp' o k)) with
        h | h
      · exact absurd h hc
      · rw [← (P k).map_conj_fstF, h, (P o).map_conj_sndF]
  refine ⟨Q, fun k l => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  by_cases hko : k = o
  · subst hko
    rw [hQoo, hQo l]
  by_cases hlo : l = o
  · subst hlo
    rw [Finset.pair_comm k o, hQoo, hQo k]
  set I : Finset (Fin n) := {k, l}ᶜ with hIdef
  set T : Finset (Fin n) := {o, k, l}ᶜ with hTdef
  have hT : T.Nonempty := compl_triple_nonempty hn o k l
  have hoT : o ∉ T := fun h => by simp [hTdef] at h
  have hkT : k ∉ T := fun h => by simp [hTdef] at h
  have hlT : l ∉ T := fun h => by simp [hTdef] at h
  have hTI : spBlock K T ≤ spBlock K I :=
    spBlock_mono (Finset.compl_subset_compl.2 (by intro x; simp; tauto))
  have hTok : spBlock K T ≤ spBlock K ({o, k}ᶜ : Finset (Fin n)) :=
    spBlock_mono (Finset.compl_subset_compl.2 (by intro x; simp; tauto))
  have hTol : spBlock K T ≤ spBlock K ({o, l}ᶜ : Finset (Fin n)) :=
    spBlock_mono (Finset.compl_subset_compl.2 (by intro x; simp; tauto))
  have hkT' := isQuasisimple_spBlock_compl hK hkT hT
  have hlT' := isQuasisimple_spBlock_compl hK hlT hT
  have hoT' := isQuasisimple_spBlock_compl hK hoT hT
  have hkTo : (Q k).fstF (spBlock K T) = (P o).fstF (spBlock K T) :=
    (P o).fstF_eq_of_le_of_fstF_eq (Q k) hTok hoT' hkT' (hpiece _ _ hoT hkT) (hQo k)
  have hlTo : (Q l).fstF (spBlock K T) = (P o).fstF (spBlock K T) :=
    (P o).fstF_eq_of_le_of_fstF_eq (Q l) hTol hoT' hlT' (hpiece _ _ hoT hlT) (hQo l)
  have hIne := compl_pair_nonempty (by omega) k l
  rcases (Q l).fstF_eq_or_eq (Q k) (isQuasisimple_spBlock_compl hK (hnp' k l) hIne)
    (isQuasisimple_spBlock_compl hK (hnp k l) hIne) (hpiece _ _ (hnp' k l) (hnp k l)) with h | h
  · exact h
  · exfalso
    have hkTl : (Q k).fstF (spBlock K T) = (Q l).sndF (spBlock K T) :=
      (Q l).fstF_eq_sndF_of_le_of_fstF_eq_sndF (Q k) hTI hlT' hkT' (hpiece _ _ hlT hkT) h
    obtain ⟨-, hbot, -⟩ := (Q l).fstF_props hlT'
    apply hbot
    rw [eq_bot_iff]
    have h1 : (Q l).fstF (spBlock K T) ≤ (Q l).sndF (spBlock K T) := by
      rw [hlTo, ← hkTo, hkTl]
    exact (le_inf le_rfl h1).trans ((Q l).fstF_inf_sndF_eq_bot _ _).le

end Coherent

section Factors

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G}

theorem sup_le_centralizer_sup {X Y Z W : Subgroup G} (hXZ : X ≤ centralizer (Z : Set G))
    (hXW : X ≤ centralizer (W : Set G)) (hYZ : Y ≤ centralizer (Z : Set G))
    (hYW : Y ≤ centralizer (W : Set G)) : X ⊔ Y ≤ centralizer ((Z ⊔ W : Subgroup G) : Set G) := by
  rw [le_centralizer_iff]
  exact sup_le (le_centralizer_iff.1 (sup_le hXZ hYZ)) (le_centralizer_iff.1 (sup_le hXW hYW))

theorem sndF_le_centralizer_fstF_of_coherent [CharP K 2] (hn : 4 ≤ n)
    {Q : ∀ k : Fin n, SwapNeighbourParam e t k}
    (hQ : ∀ k l : Fin n, (Q k).fstF (spBlock K ({k, l}ᶜ : Finset (Fin n))) =
      (Q l).fstF (spBlock K ({k, l}ᶜ : Finset (Fin n)))) (k l : Fin n) :
    (Q l).sndF (spBlock K ({l}ᶜ : Finset (Fin n))) ≤
      centralizer ((Q k).fstF (spBlock K ({k}ᶜ : Finset (Fin n))) : Set G) := by
  by_cases hkl : k = l
  · subst hkl
    exact (Q k).sndF_le_centralizer_fstF _ _
  obtain ⟨m, hmk, hml⟩ := exists_ne_ne_of_three_le (by omega) k l
  have hle : ∀ a b : Fin n, spBlock K ({a, b}ᶜ : Finset (Fin n)) ≤
      spBlock K ({a}ᶜ : Finset (Fin n)) :=
    fun a b => spBlock_mono (Finset.compl_subset_compl.2 (by simp))
  have hDk : spBlock K ({k}ᶜ : Finset (Fin n)) =
      spBlock K ({k, l}ᶜ : Finset (Fin n)) ⊔ spBlock K ({k, m}ᶜ : Finset (Fin n)) :=
    le_antisymm (spBlock_compl_singleton_le_sup hn hkl (Ne.symm hmk) (fun h => hml (h ▸ rfl)))
      (sup_le (hle k l) (hle k m))
  have hDl : spBlock K ({l}ᶜ : Finset (Fin n)) =
      spBlock K ({l, k}ᶜ : Finset (Fin n)) ⊔ spBlock K ({l, m}ᶜ : Finset (Fin n)) :=
    le_antisymm (spBlock_compl_singleton_le_sup hn (Ne.symm hkl) (Ne.symm hml)
      (fun h => hmk (h ▸ rfl))) (sup_le (hle l k) (hle l m))
  rw [hDk, hDl, (Q k).fstF_sup (hle k l) (hle k m), (Q l).sndF_sup (hle l k) (hle l m)]
  have hsk : (Q l).sndF (spBlock K ({l, k}ᶜ : Finset (Fin n))) =
      (Q k).sndF (spBlock K ({k, l}ᶜ : Finset (Fin n))) := by
    rw [← (Q l).map_conj_fstF, ← (Q k).map_conj_fstF, Finset.pair_comm l k, hQ k l]
  have hsm : (Q l).sndF (spBlock K ({l, m}ᶜ : Finset (Fin n))) =
      (Q m).sndF (spBlock K ({l, m}ᶜ : Finset (Fin n))) := by
    rw [← (Q l).map_conj_fstF, ← (Q m).map_conj_fstF, hQ l m]
  have hfm : (Q k).fstF (spBlock K ({k, m}ᶜ : Finset (Fin n))) =
      (Q m).fstF (spBlock K ({m, k}ᶜ : Finset (Fin n))) := by
    rw [hQ k m, Finset.pair_comm k m]
  refine sup_le_centralizer_sup ?_ ?_ ?_ ?_
  · rw [hsk]
    exact (Q k).sndF_le_centralizer_fstF _ _
  · rw [hsk]
    exact (Q k).sndF_le_centralizer_fstF _ _
  · rw [hQ k l]
    exact (Q l).sndF_le_centralizer_fstF _ _
  · rw [hsm, hfm]
    exact (Q m).sndF_le_centralizer_fstF _ _

end Factors

section Main

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem exists_swapFactors_neighbourCore [Finite G] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (hn : 4 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (hparam : ∀ k : Fin n, Nonempty (SwapNeighbourParam e t k)) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = ⨆ k : Fin n, neighbourCore e k ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  classical
  obtain ⟨Q, hQ⟩ := exists_coherent_swapParam hK hn fun k => (hparam k).some
  set A : Fin n → Subgroup G := fun k => (Q k).fstF (spBlock K ({k}ᶜ : Finset (Fin n))) with hA
  have hmapA : ∀ k, (A k).map (MulAut.conj t).toMonoidHom =
      (Q k).sndF (spBlock K ({k}ᶜ : Finset (Fin n))) := fun k => (Q k).map_conj_fstF _
  have h₁₂ : (⨆ k, A k).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((⨆ k, A k : Subgroup G) : Set G) :=
    LinearPilot.map_conj_iSup_le_centralizer fun k l => by
      rw [hmapA l]
      exact sndF_le_centralizer_fstF_of_coherent hn hQ k l
  have hnonempty : ∀ k : Fin n, ({k}ᶜ : Finset (Fin n)).Nonempty := fun k => by
    obtain ⟨c, hc, -⟩ := exists_ne_ne_of_three_le (by omega) k k
    exact ⟨c, mem_compl_singleton_iff'.2 hc⟩
  have hperf : ⁅⨆ k, A k, ⨆ k, A k⁆ = ⨆ k, A k :=
    LinearPilot.commutator_iSup_eq_of_forall A fun k =>
      ((Q k).fstF_props (isQuasisimple_spBlock_subgroupOf hK le_rfl (hnonempty k))).1
  have hS : IsSimpleGroup L :=
    (e.symm.isSimpleGroup_congr).1 (isSimpleGroup_statedSp_of_four_le hK (by omega))
  have hδ : ∀ x ∈ ⨆ k, A k, x * (t * x * t⁻¹) ∈ L :=
    LinearPilot.mul_conj_mem_of_mem_iSup h₁₂ fun k _ hx =>
      UnitaryPilot.modelToG_le e _ ((Q k).mul_conj_mem_modelToG_of_mem_fstF hx)
  have hsurj : ∀ y ∈ L, ∃ x ∈ ⨆ k, A k, x * (t * x * t⁻¹) = y := by
    intro y hy
    have hy' : y ∈ ⨆ k : Fin n, modelToG e (spBlock K ({k}ᶜ : Finset (Fin n))) := by
      rw [← UnitaryPilot.modelToG_iSup, iSup_spBlock_compl_singleton_eq_top (by omega),
        UnitaryPilot.modelToG_top]
      exact hy
    exact LinearPilot.exists_mul_conj_eq_of_mem_iSup h₁₂ (fun k z hz => by
      obtain ⟨x, hx, hxz⟩ := (Q k).exists_mem_fstF_mul_conj_eq le_rfl hz
      exact ⟨x, mem_iSup_of_mem k hx, hxz⟩) y hy'
  refine ⟨⨆ k, A k, LinearPilot.isQuasisimple_of_linearSwapDiag h₁₂ hperf hS hδ hsurj, h₁₂, ?_,
    hδ, hsurj⟩
  rw [Subgroup.map_iSup, ← iSup_sup_eq]
  exact iSup_congr fun k => by rw [hmapA k, (Q k).fstF_sup_sndF_compl]

end Main

end CFSG.SeitzReduction.SymplecticPilot
