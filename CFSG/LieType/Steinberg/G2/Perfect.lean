module

public import CFSG.LieType.Steinberg.G2.Extras

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.TitsSimplicity
open scoped commutatorElement

variable
    {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]

theorem commutator_torusElement_xPar_single
    (l i : Fin τ.rank) (t : Kˣ) (c : K) :
    ⁅torusElement τ K l t, xPar F (Pi.single i 1) c⁆ =
      xPar F (Pi.single i 1) ((((t ^ τ.cartan l i : Kˣ) : K) - 1) * c) := by
  have hs : ∑ j, τ.cartan l j * (simpleRoot τ i).1 j = τ.cartan l i := by
    simp [simpleRoot, Pi.single_apply]
  rw [commutatorElement_def, xPar_simple, xPar_simple, F.torusElement_mul_eltElement_mul_inv,
    eltElement_neg, ← F.eltElement_add, hs]
  congr 1
  ring

theorem rootGroup_single_le_commutator_of_torus
    {l i : Fin τ.rank} (t : Kˣ)
    (ht : ((t ^ τ.cartan l i : Kˣ) : K) ≠ 1) :
    rootGroup F K (Pi.single i 1) ≤ commutator ↥(adjointGroup τ K) := by
  intro g hg
  obtain ⟨d, rfl⟩ := (mem_rootGroup_iff (isRoot_single τ i) g).1 hg
  have hs : ((t ^ τ.cartan l i : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.2 ht
  have h := commutator_torusElement_xPar_single (F := F) l i t
    (d / (((t ^ τ.cartan l i : Kˣ) : K) - 1))
  rw [mul_div_cancel₀ _ hs] at h
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem zpow_eq_self_of_sq_eq_one {G : Type*} [Group G] {u : G} (hu : u ^ 2 = 1) {n : ℤ}
    (hn : Odd n) : u ^ n = u := by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add, zpow_mul, zpow_one, zpow_ofNat, hu, one_zpow, one_mul]

theorem exists_ne_zero_ne_one_of_three_le_card (hK : 3 ≤ Nat.card K) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  by_contra! h
  have hs : Function.Surjective fun b : Bool => if b then (1 : K) else 0 := fun t => by
    by_cases ht : t = 0
    · exact ⟨false, by simp [ht]⟩
    · exact ⟨true, by simp [h t ht]⟩
  have := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem exists_odd_cartan_G2 (i : Fin (Tag.rank .G2)) : ∃ l, Odd (Tag.cartan .G2 l i) := by
  fin_cases i
  · exact ⟨⟨1, by decide⟩, -2, by decide⟩
  · exact ⟨⟨0, by decide⟩, -1, by decide⟩

theorem isIndecomposable_cartan_G2 : IsIndecomposable (Tag.cartan .G2) := by
  decide +kernel

variable (K)

theorem isPerfect_g2
    (hK : ∃ t : K, t ≠ 0 ∧ t ≠ 1) : Group.IsPerfect ↥(adjointGroup .G2 K) := by
  obtain ⟨t, ht0, ht1⟩ := hK
  refine CurtisTits.isPerfect_of_rootGroup_single_le_commutator (g2_isCTGroupDatum K)
    (fun γ _ h2 => absurd (eq_one_of_isRoot_nsmul (mem_adjDatum_roots.1 h2)) (by norm_num))
    fun i => ?_
  by_cases h2 : t ^ 2 = 1
  ·
    have hu : Units.mk0 t ht0 ^ 2 = 1 := Units.ext (by simp [h2])
    obtain ⟨l, hl⟩ := exists_odd_cartan_G2 i
    refine rootGroup_single_le_commutator_of_torus (l := l) (Units.mk0 t ht0) ?_
    rw [zpow_eq_self_of_sq_eq_one hu hl, Units.val_mk0]
    exact ht1
  ·
    refine rootGroup_single_le_commutator_of_torus (l := i) (Units.mk0 t ht0) ?_
    rw [Tag.cartan_self, zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact h2

theorem nontrivial_g2
    : Nontrivial ↥(adjointGroup .G2 K) := by
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (rootGroup_ne_bot (F := rootOperatorFamily .G2) (K := K) (isRoot_single .G2 ⟨0, by decide⟩))
  exact nontrivial_of_ne (x : ↥(adjointGroup .G2 K)) 1 fun h => hx (Subtype.ext h)

theorem isQuasisimple_g2
    (hK : ∃ t : K, t ≠ 0 ∧ t ≠ 1) : IsQuasisimple ↥(adjointGroup .G2 K) := by
  have := nontrivial_g2 K
  exact TitsSimplicity.isQuasisimple (g2_isCTGroupDatum K) (g2_steinbergExtras K)
    (g2_bruhatExtras K) (g2_rootGroupCommutators K) isIndecomposable_cartan_G2
    (isPerfect_g2 K hK)

theorem isPerfect_g2_of_three_le_card
    (hK : 3 ≤ Nat.card K) :
    Group.IsPerfect ↥(adjointGroup .G2 K) :=
  isPerfect_g2 K (exists_ne_zero_ne_one_of_three_le_card hK)

theorem isQuasisimple_g2_of_three_le_card
    (hK : 3 ≤ Nat.card K) :
    IsQuasisimple ↥(adjointGroup .G2 K) :=
  isQuasisimple_g2 K (exists_ne_zero_ne_one_of_three_le_card hK)

end CFSG.LieType.Steinberg.Adjoint
