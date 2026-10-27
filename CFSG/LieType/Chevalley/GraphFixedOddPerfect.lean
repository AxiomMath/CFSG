module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.GraphFixedIntrinsicPairs
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem cartanChar_neg_one_zpow {τ : Tag} {K : Type} [Field K] (e : Fin τ.rank → ℤ)
    (l : Fin τ.rank) :
    cartanChar (fun j => (-1 : Kˣ) ^ e j) l = (-1) ^ (∑ j, e j * τ.cartan j l) := by
  rw [cartanChar, ← prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm

@[expose] def oddPartner : (t : TwistTag) → Fin t.foldedTag.rank → Fin t.foldedTag.rank
  | .E6 => (![1, 0, 3, 2] : Fin 4 → Fin 4)
  | .D4 => (![1, 0] : Fin 2 → Fin 2)

theorem odd_sum_cartan_oddPartner (t : TwistTag) (a : Fin t.foldedTag.rank) :
    Odd (∑ j, (if t.orbitIndex j = oddPartner t a then (1 : ℤ) else 0) *
      t.tag.cartan j (t.orbitMin a)) := by
  revert a
  cases t <;> decide

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem compatDiag_indicator (b : Fin t.foldedTag.rank) :
    compatDiag t σ (fun a => if a = b then -1 else 1) =
      fun j => (-1 : Kˣ) ^ (if t.orbitIndex j = b then (1 : ℤ) else 0) := by
  funext j
  obtain ⟨k, hk, hi⟩ := t.exists_eq_perm_pow_orbitMin (t.mem_orbit_orbitIndex j)
  rw [← hi, compatDiag_pow _ _ hk]
  have hj : t.orbitIndex ((t.perm ^ k) (t.orbitMin (t.orbitIndex j))) = t.orbitIndex j :=
    (t.mem_orbit_iff).1 (t.perm_pow_mem_orbit (t.orbitMin_mem _) k)
  rw [hj]
  refine Units.ext ?_
  by_cases h : t.orbitIndex j = b
  · simp [h, coe_orbitFieldUnit]
  · simp [h, coe_orbitFieldUnit]

theorem exists_mem_conj_orbitX_neg
    (a : Fin t.foldedTag.rank) :
    ∃ h ∈ graphFixedRootGroup t K σ, ∀ c : orbitField t K σ a,
      h * orbitX t K σ a c * h⁻¹ = orbitX t K σ a (-c) := by
  set w : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ :=
    fun a' => if a' = oddPartner t a then -1 else 1 with hw
  obtain ⟨v, -, hv, hX, -⟩ := exists_list_prod_orbitH_conj w
  refine ⟨((List.finRange t.foldedTag.rank).map fun a' =>
    (orbitH t K σ a' (w a') : ModGL t.tag K)).prod, Subgroup.list_prod_mem _ fun x hx => ?_,
    fun c => ?_⟩
  · obtain ⟨a', -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup t σ a' (w a')
  · rw [hX]
    have hva : v a = -1 := by
      have h1 := hv a
      rw [hw, compatDiag_indicator, cartanChar_neg_one_zpow,
        (odd_sum_cartan_oddPartner t a).neg_one_zpow] at h1
      exact Units.ext (Subtype.ext (congrArg Units.val h1))
    rw [hva, Units.val_neg, Units.val_one, neg_one_mul]

theorem orbitX_mem_commutator_of_two_ne_zero
    (hK : (2 : K) ≠ 0) (a : Fin t.foldedTag.rank)
    (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈
      ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ := by
  obtain ⟨h, hh, hconj⟩ := exists_mem_conj_orbitX_neg (K := K) (σ := σ) a
  have h2 : (2 : orbitField t K σ a) ≠ 0 := fun h0 => hK (by
    rw [← map_ofNat (orbitField t K σ a).subtype 2, h0, map_zero])
  have : NeZero (2 : orbitField t K σ a) := ⟨h2⟩
  have e : ⁅h, (orbitX t K σ a (-(c / 2)) : ModGL t.tag K)⁆ = orbitX t K σ a c := by
    rw [commutatorElement_def, hconj, neg_neg, ← Subgroup.coe_inv, ← orbitX_neg, neg_neg,
      ← Subgroup.coe_mul, ← orbitX_add, add_halves]
  rw [← e]
  exact Subgroup.commutator_mem_commutator hh
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a _))

theorem commutator_graphFixedRootGroup_of_two_ne_zero
    (hK : (2 : K) ≠ 0)
    (hσ : Function.Surjective σ) :
    ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ = graphFixedRootGroup t K σ := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  conv_lhs => rw [graphFixedRootGroup_eq_iSup_orbitRankOneGroup hσ]
  refine iSup_le fun a => (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact orbitX_mem_commutator_of_two_ne_zero hK a c
  · exact orbitY_mem_commutator t σ (fun c => orbitX_mem_commutator_of_two_ne_zero hK a c) c

theorem odd_diagram_fixed_root_group_perfect
    (t : TwistTag) (K : Type) [Field K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) :
    ⁅graphFixedRootGroup t K σ.toRingHom, graphFixedRootGroup t K σ.toRingHom⁆ =
      graphFixedRootGroup t K σ.toRingHom ∧
    (∃ x ∈ graphFixedRootGroup t K σ.toRingHom, ∃ y ∈ graphFixedRootGroup t K σ.toRingHom,
      ¬ Commute x y) ∧
    ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ =
      graphFixedRootGroup t K σ.toRingHom := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hperf := commutator_graphFixedRootGroup_of_two_ne_zero (t := t) (σ := σ.toRingHom) h2
    σ.surjective
  have hr : 0 < t.foldedTag.rank := by cases t <;> decide
  refine ⟨hperf, ⟨_, graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom
      (orbitX_mem_graphFixedPosUnipotent t σ.toRingHom ⟨0, hr⟩ 1), _,
    graphFixedNegUnipotent_le_graphFixedRootGroup t K σ.toRingHom
      (orbitY_mem_graphFixedNegUnipotent t σ.toRingHom ⟨0, hr⟩ 1),
    not_commute_orbitX_orbitY ⟨0, hr⟩⟩,
    (fixed_root_generated_normal_subgroup t K σ).2.2.2.2 hperf⟩

end CFSG.LieType.Chevalley
