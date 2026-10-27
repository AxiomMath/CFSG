module

public import CFSG.ClassicalInvolution.Q3.Q3ZCheck
public import CFSG.ClassicalInvolution.Q3.Q3ZGen
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.CosetTable CFSG.Assembly.LowTwoRank

theorem natCard_statedSp_three : Nat.card (StatedSp 3 (ZMod 3)) = 9170703360 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
    show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide)]
  norm_num

theorem natCard_statedSp_two_three : Nat.card (StatedSp 2 (ZMod 3)) = 51840 :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two_zmod_three

theorem card_v6_le (h : V6Check) :
    Finite (PG 12 v6Words) ∧ Nat.card (PG 12 v6Words) ≤ 9170703360 := by
  obtain ⟨hL, hI⟩ := h
  obtain ⟨hfin, hle⟩ := card_le_of_subsetCheck_nil _ hL
  have := hfin
  obtain ⟨hfin', hle'⟩ := card_le_of_subsetCheck v6Words c2Subset hI
  refine ⟨hfin', hle'.trans ?_⟩
  calc 176904 * _ ≤ 176904 * 51840 := Nat.mul_le_mul_left _ hle
    _ = 9170703360 := by norm_num

@[expose] def V6Collapse : Prop :=
  ∀ k : Fin 24, gluingComplete k = false → ∀ {G : Type} [Group G] (g : Fin 12 → G),
    RelsHold g (v6aWords k) → ∀ i, g i = 1

theorem v6Collapse_of_check (h : V6CollapseCheck) : V6Collapse := by
  intro k hk G _ g hg i
  have hall := List.all_eq_true.mp h k (List.mem_finRange k)
  rw [hk, Bool.false_or] at hall
  obtain ⟨hfin, hle⟩ := card_le_of_subsetCheck_nil (v6aWords k) hall
  have hsub : Subsingleton (PG 12 (v6aWords k)) := Finite.card_le_one_iff_subsingleton.mp hle
  obtain ⟨f, hf⟩ := exists_hom_of_relsHold (v6aWords k) g hg
  rw [← hf i, Subsingleton.elim (PresentedGroup.of i) 1, map_one]

theorem exists_mulEquiv_v6 (h : V6Check) :
    ∃ e : PG 12 v6Words ≃* StatedSp 3 (ZMod 3), ∀ i, e (PresentedGroup.of i) = v6Mat i := by
  obtain ⟨hfin, hle⟩ := card_v6_le h
  have := hfin
  obtain ⟨ev, hev⟩ := exists_hom_of_relsHold v6Words v6Mat v6_relsHold
  have hsurj : Function.Surjective ev := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← v6_closure_eq_top, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hev i⟩
  exact ⟨MulEquiv.ofBijective ev
    (hsurj.bijective_of_nat_card_le (hle.trans natCard_statedSp_three.ge)), hev⟩

@[expose] def V6Universal : Prop :=
  ∀ {G : Type} [Group G] (g : Fin 12 → G), RelsHold g v6Words →
    ∃ ψ : StatedSp 3 (ZMod 3) →* G, ∀ i, ψ (v6Mat i) = g i

theorem v6Universal_of_check (h : V6Check) : V6Universal := by
  intro G _ g hg
  obtain ⟨e, he⟩ := exists_mulEquiv_v6 h
  obtain ⟨f, hf⟩ := exists_hom_of_relsHold v6Words g hg
  refine ⟨f.comp e.symm.toMonoidHom, fun i => ?_⟩
  have hi : e.symm (v6Mat i) = PresentedGroup.of i := by
    rw [MulEquiv.symm_apply_eq]
    exact (he i).symm
  simp [hi, hf]

end CFSG.ClassicalInvolution.Q3.Q3Z
