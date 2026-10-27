module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PieceTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)

local instance e8PilotQ2PieceFrameNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def q2FrameRoot : Fin 7 → Fin (Tag.rank .E8) → ℤ :=
  ![highRoot .E8, Pi.single 1 1, Pi.single 5 1, ![0, 0, 0, 0, 1, 1, 1, 0],
    ![1, 1, 2, 2, 1, 1, 1, 0], ![1, 1, 2, 2, 2, 1, 0, 0], ![1, 2, 2, 4, 3, 2, 1, 0]]

@[expose] def q2FrameWord : Fin 7 → List (Fin (Tag.rank .E8)) :=
  ![E8Neighbour.high.word, E8Neighbour.two.word, E8Neighbour.six.word,
    [7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
    [7, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
    [6, 7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
    [7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]]

theorem q2FrameWord_smul_highRoot (k : Fin 7) :
    (coxeterSystem .E8).wordProd (q2FrameWord k) • highRoot .E8 = q2FrameRoot k := by
  fin_cases k
  · exact E8Neighbour.weyl_smul_highRoot .high
  · exact E8Neighbour.weyl_smul_highRoot .two
  · exact E8Neighbour.weyl_smul_highRoot .six
  all_goals
    simp only [q2FrameWord, q2FrameRoot, Fin.reduceFinMk, Matrix.cons_val,
      CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem isRoot_q2FrameRoot (k : Fin 7) :
    IsRoot .E8 (q2FrameRoot k) := by
  rw [← q2FrameWord_smul_highRoot]
  exact IsRoot.smul (isRoot_highRoot .E8) _

theorem iform_q2FrameRoot_single_zero (k : Fin 7) :
    iform (q2FrameRoot k) (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) = 0 := by
  revert k
  decide +kernel

theorem iform_q2FrameRoot (k k' : Fin 7) :
    iform (q2FrameRoot k) (q2FrameRoot k') = if k = k' then 2 else 0 := by
  revert k k'
  decide +kernel

@[expose] def E8Neighbour.frameIdx : E8Neighbour → Fin 7
  | .high => 0
  | .two => 1
  | .six => 2

theorem E8Neighbour.q2FrameRoot_frameIdx (N : E8Neighbour) :
    q2FrameRoot N.frameIdx = N.root := by
  cases N <;> rfl

theorem q2Frame_basis_check : ∀ i j : Fin (Tag.rank .E8),
    ∑ k : Fin 7, iform (q2FrameRoot k) (Pi.single j 1) * iform (q2FrameRoot k) (Pi.single i 1) =
      2 * iform (Pi.single i 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single j 1) -
        iform (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single j 1) *
          iform (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single i 1) := by
  decide +kernel

theorem sum_iform_q2FrameRoot
    (v : Fin (Tag.rank .E8) → ℤ) (i : Fin (Tag.rank .E8)) :
    ∑ k : Fin 7, iform v (q2FrameRoot k) * iform (q2FrameRoot k) (Pi.single i 1) =
      2 * iform v (Pi.single i 1) -
        iform v (Pi.single 0 1) *
          iform (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single i 1) := by
  have hv : ∀ b : Fin (Tag.rank .E8) → ℤ, iform v b = ∑ j, v j * iform b (Pi.single j 1) :=
    fun b => by rw [iform_comm, F4Pilot.iform_eq_sum_mul_iform_single]
  have key : ∀ j : Fin (Tag.rank .E8), ∑ k : Fin 7, v j * iform (q2FrameRoot k) (Pi.single j 1) *
      iform (q2FrameRoot k) (Pi.single i 1) =
        2 * (v j * iform (Pi.single i 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single j 1)) -
          v j * iform (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single j 1) *
            iform (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) (Pi.single i 1) := by
    intro j
    have h := q2Frame_basis_check i j
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, h]
    ring
  simp only [hv]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => key j

section Coroot

variable {K₂ : Type} [Field K₂]

theorem corootTuple_eq_prod_q2Frame
    {δ : Fin (Tag.rank .E8) → ℤ}
    (hδ : iform δ (Pi.single 0 1) = 0) {c : K₂ˣ} (hc : c ^ 3 = 1) :
    corootTuple δ c =
      ∏ k : Fin 7, corootTuple (q2FrameRoot k) (c ^ (2 * iform δ (q2FrameRoot k))) := by
  funext i
  rw [Finset.prod_apply]
  simp only [corootTuple, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  have hsum : ∑ k : Fin 7, 2 * iform δ (q2FrameRoot k) * iform (q2FrameRoot k) (Pi.single i 1) =
      iform δ (Pi.single i 1) + 3 * iform δ (Pi.single i 1) := by
    have h := sum_iform_q2FrameRoot δ i
    rw [hδ, zero_mul, sub_zero] at h
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, h]
    ring
  have hc3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc
  rw [hsum, zpow_add, zpow_mul, hc3, one_zpow, mul_one]

theorem conj_eq_of_forall_mem_centralizer_q2Frame
    [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ 2)
    {g : ModGL .E8 K₂}
    (hg : ∀ (k : Fin 7) (c : K₂ˣ),
      g ∈ centralizer ({(rootDiagUnit .E8 (corootTuple (q2FrameRoot k) c))} : Set (ModGL .E8 K₂))) :
    ∀ a ∈ corootTupleSet (⊤ : Subgroup K₂ˣ) {0},
      rootDiagUnit .E8 a * g * (rootDiagUnit .E8 a)⁻¹ = g := by
  rintro a ⟨δ, -, hδJ, c, -, rfl⟩
  have hδ0 : iform δ (Pi.single 0 1) = 0 := hδJ 0 (Finset.mem_singleton_self 0)
  rw [corootTuple_eq_prod_q2Frame hδ0 (pow_three_eq_one_of_natCard_eq_four hK₂ c)]
  have hmem : (∏ k : Fin 7,
      corootTuple (q2FrameRoot k) (c ^ (2 * iform δ (q2FrameRoot k)))) ∈
        (centralizer ({g} : Set (ModGL .E8 K₂))).comap (rootDiagUnitHom .E8 K₂) := by
    refine Subgroup.prod_mem _ fun k _ => ?_
    have h := mem_centralizer_singleton_iff.1 (hg k (c ^ (2 * iform δ (q2FrameRoot k))))
    exact mem_centralizer_singleton_iff.2 h.symm
  have h2 := mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hmem)
  change rootDiagUnitHom .E8 K₂ _ * g * (rootDiagUnitHom .E8 K₂ _)⁻¹ = g
  rw [h2, mul_inv_cancel_right]

end Coroot

section Levi

variable {K : Type} [Field K] {K₂ : Type} [Field K₂]

theorem baseChangeGL_mem_highRootSL2 (ι : K →+* K₂) {x : ModGL .E8 K}
    (hx : x ∈ EPilot.highRootSL2 .E8 K) : baseChangeGL ι x ∈ EPilot.highRootSL2 .E8 K₂ := by
  have hU : ∀ α : Fin (Tag.rank .E8) → ℤ,
      (rootSubgroup .E8 K α).map (baseChangeGL ι) ≤ rootSubgroup .E8 K₂ α := by
    intro α
    rw [rootSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    rw [baseChangeGL_pinnedX]
    exact subset_closure ⟨ι c, rfl⟩
  have h : (EPilot.highRootSL2 .E8 K).map (baseChangeGL ι) ≤ EPilot.highRootSL2 .E8 K₂ := by
    rw [EPilot.highRootSL2, Subgroup.map_sup]
    exact sup_le_sup (hU _) (hU _)
  exact h ⟨x, hx, rfl⟩

theorem rootSubgroup_le_centralizer_of_iform_eq_zero {F : Type} [Field F]
    {γ δ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) (hδ : IsRoot .E8 δ) (h0 : iform γ δ = 0) :
    rootSubgroup .E8 F γ ≤ centralizer (rootSubgroup .E8 F δ : Set (ModGL .E8 F)) :=
  fun _ hx => mem_centralizer_iff.2 fun _ hy =>
    (EPilot.commute_of_iform_eq_zero (Or.inr (Or.inr rfl)) hγ hδ h0 hx hy).eq.symm

theorem rootSpan_amalgamRoots_zero_le_centralizer_rootSL2 {F : Type} [Field F] (k : Fin 7) :
    rootSpan .E8 F (amalgamRoots {0}) ≤ centralizer
      ((rootSubgroup .E8 F (q2FrameRoot k) ⊔ rootSubgroup .E8 F (-q2FrameRoot k) :
        Subgroup (ModGL .E8 F)) : Set (ModGL .E8 F)) := by
  refine iSup₂_le fun γ hγ => ?_
  have hγr := isRoot_of_mem_amalgamRoots hγ
  have h1 : iform (q2FrameRoot k) γ = 0 := by
    obtain ⟨j, hj, rfl | rfl⟩ := hγ <;> rw [Finset.mem_singleton] at hj <;> subst hj
    · exact iform_q2FrameRoot_single_zero k
    · rw [iform_neg_right_E8, iform_q2FrameRoot_single_zero, neg_zero]
  have h2 : iform (-q2FrameRoot k) γ = 0 := by
    rw [iform_comm, iform_neg_right_E8, iform_comm, h1, neg_zero]
  rw [le_centralizer_iff]
  exact sup_le (rootSubgroup_le_centralizer_of_iform_eq_zero (isRoot_q2FrameRoot k) hγr h1)
    (rootSubgroup_le_centralizer_of_iform_eq_zero (IsRoot.neg (isRoot_q2FrameRoot k)) hγr h2)

theorem perfectCore_levi_inf_q2Frame_eq [Finite K] [Finite K₂] [CharP K₂ 2]
    (hK : Nat.card K = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : K →+* K₂) {x : ModGL .E8 K}
    (hxJ : x ∈ EPilot.highRootSL2 .E8 K) (hx : orderOf x = 3) (N : E8Neighbour) :
    perfectCore ((N.levi K₂).map (adjointGroup .E8 K₂).subtype ⊓
      ⨅ (k : Fin 7) (_ : k ≠ N.frameIdx), centralizer
        ({baseChangeGL ι (wordElt K (q2FrameWord k) * x * (wordElt K (q2FrameWord k))⁻¹)} :
          Set (ModGL .E8 K₂))) =
      rootSpan .E8 K₂ (amalgamRoots {0}) := by
  have : Finite (ModGL .E8 K₂) := finite_modGL
  have hA3 : 3 ≤ Nat.card (⊤ : Subgroup K₂ˣ) :=
    F4Pilot.three_le_natCard_top_units (by rw [hK₂]; norm_num)
  refine le_antisymm ?_ ?_
  · set H := (N.levi K₂).map (adjointGroup .E8 K₂).subtype ⊓
      ⨅ (k : Fin 7) (_ : k ≠ N.frameIdx), centralizer
        ({baseChangeGL ι (wordElt K (q2FrameWord k) * x * (wordElt K (q2FrameWord k))⁻¹)} :
          Set (ModGL .E8 K₂)) with hH
    set P := perfectCore H with hPdef
    have hPperf : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect H
    have hPH : P ≤ H := perfectCore_le H
    have hPlevi : P ≤ rootSpan .E8 K₂ (orthRoots N.root) := by
      rw [← map_subtype_levi]
      exact hPH.trans inf_le_left
    have hPC : P ≤ adjointGroup .E8 K₂ := hPlevi.trans (rootSpan_le_adjointGroup_E8 _)
    have hcent : ∀ g ∈ P, ∀ (k : Fin 7) (c : K₂ˣ), g ∈ centralizer
        ({(rootDiagUnit .E8 (corootTuple (q2FrameRoot k) c))} : Set (ModGL .E8 K₂)) := by
      intro g hg k c
      by_cases hk : k = N.frameIdx
      · subst hk
        rw [E8Neighbour.q2FrameRoot_frameIdx]
        refine rootSpan_le_centralizer (corootTuple N.root c) (fun γ hγ => ⟨hγ.1, ?_⟩)
          (hPlevi hg)
        rw [rootChar_corootTuple, hγ.2, zpow_zero]
      · have hPk : P ≤ centralizer
            ({baseChangeGL ι (wordElt K (q2FrameWord k) * x * (wordElt K (q2FrameWord k))⁻¹)} :
              Set (ModGL .E8 K₂)) :=
          hPH.trans (inf_le_right.trans (iInf₂_le k hk))
        have h := mem_centralizer_corootTuple_of_perfect_of_le_centralizer_word hK hK₂ ι hxJ hx
          (q2FrameWord k) hPperf hPC hPk hg c
        rwa [q2FrameWord_smul_highRoot] at h
    have h := perfectCore_le_rootSpan_amalgamRoots_of_forall_conj_eq hA3 (J := {0}) (by decide)
      (H := P) fun g hg => ⟨hPC hg, conj_eq_of_forall_mem_centralizer_q2Frame hK₂ (hcent g hg)⟩
    rwa [CFSG.Quasithin.perfectCore_eq_self_of_perfect hPperf] at h
  · refine le_perfectCore_of_perfect (le_inf ?_ (le_iInf₂ fun k _ => ?_))
      (commutator_rootSpan_amalgamRoots_eq_E8 hA3 {0})
    · rw [map_subtype_levi]
      exact rootSpan_mono (amalgamRoots_subset_orthRoots_iff_subset_nodes.2 (by cases N <;> decide))
    · intro u hu
      rw [mem_centralizer_singleton_iff]
      have hy : baseChangeGL ι (wordElt K (q2FrameWord k) * x * (wordElt K (q2FrameWord k))⁻¹) ∈
          rootSubgroup .E8 K₂ (q2FrameRoot k) ⊔ rootSubgroup .E8 K₂ (-q2FrameRoot k) := by
        rw [map_mul, map_mul, map_inv, baseChangeGL_wordElt, ← q2FrameWord_smul_highRoot]
        exact conj_wordElt_mem_rootSL2 (q2FrameWord k) (baseChangeGL_mem_highRootSL2 ι hxJ)
      exact (mem_centralizer_iff.1 (rootSpan_amalgamRoots_zero_le_centralizer_rootSL2 k hu) _
        hy).symm

end Levi

end CFSG.SeitzReduction.E8Pilot
