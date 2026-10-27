module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def e7CentPred (k : Fin 5) (β : Fin Tag.E7.rank → ℤ) : Prop :=
  0 < height β ∧ ∀ ρ ∈ e7ASFrame k, 0 ≤ iform β ρ

instance (k : Fin 5) : DecidablePred (e7CentPred k) := fun β => by
  unfold e7CentPred
  infer_instance

@[expose] def e7CentRoots (k : Fin 5) : Set (Fin Tag.E7.rank → ℤ) :=
  {β | IsRoot .E7 β ∧ e7CentPred k β}


theorem e7CentRoots_ncard (k : Fin 5) : 33 ≤ (e7CentRoots k).ncard := by
  rw [e7CentRoots, CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and]
  revert k
  decide +kernel

theorem e7ASFrame_height_pos (k : Fin 5) : ∀ ρ ∈ e7ASFrame k, 0 < height ρ := by
  revert k
  decide +kernel

theorem e7CentRoots_pos (k : Fin 5) : ∀ β ∈ e7CentRoots k, IsRoot .E7 β ∧ 0 < height β :=
  fun _ hβ => ⟨hβ.1, hβ.2.1⟩

theorem e7CentRoots_closed (k : Fin 5) : ∀ α ∈ e7CentRoots k, ∀ β ∈ e7CentRoots k, ∀ a b : ℕ,
    1 ≤ a → 1 ≤ b → IsRoot .E7 (a • α + b • β) → a • α + b • β ∈ e7CentRoots k := by
  rintro α ⟨-, hαh, hαρ⟩ β ⟨-, hβh, hβρ⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, fun ρ hρ => ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · rw [iform_add_left, ← Nat.cast_smul_eq_nsmul ℤ a α, ← Nat.cast_smul_eq_nsmul ℤ b β,
      iform_smul_left, iform_smul_left]
    nlinarith [hαρ ρ hρ, hβρ ρ hρ]

theorem not_isRoot_add_of_iform_nonneg {α β : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hβ : IsRoot .E7 β) (h : 0 ≤ iform α β) : ¬ IsRoot .E7 (α + β) := by
  intro hab
  have hsym : ∀ i, Tag.E7.symmetrizer i i = 1 := by decide
  have h1 := SimplyLacedCover.iform_self_eq_two hsym hab
  have h2 := SimplyLacedCover.iform_self_eq_two hsym hα
  have h3 := SimplyLacedCover.iform_self_eq_two hsym hβ
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm β α, h2, h3] at h1
  omega

section Lower


variable {K : Type} [Field K]

theorem rootSpan_e7CentRoots_le_centralizer (k : Fin 5) :
    rootSpan .E7 K (e7CentRoots k) ≤
      Subgroup.centralizer {(e7ASRep K k : ModGL .E7 K)} := by
  refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨hβr, hβh, hβρ⟩ := hβ
  have hcomm : Commute (pinnedX .E7 K β c)
      (((e7ASFrame k).map fun σ => pinnedX .E7 K σ 1).prod) := by
    refine Commute.list_prod_right _ _ fun y hy => ?_
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hy
    have hρr : IsRoot .E7 ρ := e7ASFrame_isRoot k ρ hρ
    have hρh : 0 < height ρ := e7ASFrame_height_pos k ρ hρ
    by_cases hβe : β = ρ
    · subst hβe
      show pinnedX .E7 K β c * pinnedX .E7 K β 1 = pinnedX .E7 K β 1 * pinnedX .E7 K β c
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · have hne' : β ≠ -ρ := by
        intro h
        rw [h, height_neg] at hβh
        omega
      exact (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl))) hβr hρr hβe
        hne').2 (not_isRoot_add_of_iform_nonneg hβr hρr (hβρ ρ hρ)) K _
        (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨1, rfl⟩)
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, coe_e7ASRep]
  exact hcomm.eq

theorem natCard_rootSpan_e7CentRoots [Finite K] (k : Fin 5) :
    Nat.card K ^ 33 ≤ Nat.card (rootSpan .E7 K (e7CentRoots k)) := by
  rw [card_rootSpan (e7CentRoots_pos k) (e7CentRoots_closed k)]
  exact Nat.pow_le_pow_right Nat.card_pos (e7CentRoots_ncard k)

theorem exists_isPGroup_le_centralizer_E7 [Finite K] [CharP K 2] {y : adjointGroup .E7 K}
    (hy : orderOf y = 2) :
    ∃ P : Subgroup (adjointGroup .E7 K), IsPGroup 2 P ∧
      P ≤ centralizer ({y} : Set (adjointGroup .E7 K)) ∧ Nat.card K ^ 33 ≤ Nat.card P := by
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by decide)
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE7 hy2 hy1
  obtain ⟨k, hk⟩ := mem_innerRepsE7_iff.1 hg
  obtain ⟨f, -, hK⟩ := exists_card_eq_two_pow_eClasses K
  set U := rootSpan .E7 K (e7CentRoots k) with hUdef
  have hUC : U ≤ adjointGroup .E7 K := iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  set P₀ : Subgroup (adjointGroup .E7 K) := U.subgroupOf (adjointGroup .E7 K) with hP₀
  have hP₀card : Nat.card P₀ = Nat.card U := Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv
  refine ⟨P₀.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · have hcard : Nat.card (P₀.map (MulAut.conj g⁻¹).toMonoidHom) =
        2 ^ (f * (e7CentRoots k).ncard) := by
      rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hP₀card, hUdef,
        card_rootSpan (e7CentRoots_pos k) (e7CentRoots_closed k), hK, ← pow_mul]
    exact IsPGroup.of_card hcard
  · rintro _ ⟨a, ha, rfl⟩
    have ha' : (a : ModGL .E7 K) ∈ U := mem_subgroupOf.1 ha
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_e7CentRoots_le_centralizer k ha')
    have hc' : a * e7ASRep K k = e7ASRep K k * a := Subtype.ext hc
    rw [← hk] at hc'
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * a * g * y = g⁻¹ * (a * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * a) * g := by rw [hc']
      _ = y * (g⁻¹ * a * g) := by group
  · rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hP₀card]
    exact natCard_rootSpan_e7CentRoots k

end Lower

section Upper


variable {K : Type} [Field K]

theorem natCard_le_of_isPGroup_E7 [Finite K] [CharP K 2]
    {P : Subgroup (adjointGroup .E7 K)} (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card K ^ 63 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have h1 : Nat.card P ≤ Nat.card S := Subgroup.card_le_of_le hPS
  have h2 : Nat.card S = Nat.card (E8Pilot.posUnipotentSylowE .E7 K) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h3 : Nat.card (E8Pilot.posUnipotentSylowE .E7 K) = Nat.card (posUnipotent .E7 K) := by
    have he : ((E8Pilot.posUnipotentSylowE .E7 K : Subgroup (adjointGroup .E7 K))) =
        (posUnipotent .E7 K).subgroupOf (adjointGroup .E7 K) := by
      ext x
      rw [E8Pilot.mem_posUnipotentSylowE, mem_subgroupOf]
    rw [he]
    exact Nat.card_congr (subgroupOfEquivOfLe posUnipotent_le_adjointGroup).toEquiv
  rw [h2, h3, card_posUnipotent, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E7] at h1
  exact h1

end Upper

end CFSG.SeitzReduction.E7Pilot
