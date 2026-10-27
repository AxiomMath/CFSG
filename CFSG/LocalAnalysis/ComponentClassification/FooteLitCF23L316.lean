module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L4
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Assembly.LowTwoRank LocalAnalysis.ComponentInitial.LinearFlag

theorem card_of_lieModel_L316 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSL 3 2 4) :
    Nat.card Y = 1425715200 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_sixteen (h.statedClassicalModel (by decide))

theorem isEmpty_alt_of_card_L316 {Y : Type} [Group Y] (hY : Nat.card Y = 1425715200) (m : ℕ)
    (hm : 5 ≤ m) : IsEmpty (Y ≃* alternatingGroup (Fin m)) := by
  refine ⟨fun e => ?_⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h1 := two_mul_card_alternatingGroup (α := Fin m)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr e.toEquiv, hY] at h1
  rcases Nat.lt_or_ge m 13 with h13 | h13
  · have := Nat.factorial_le (Nat.le_of_lt_succ h13)
    rw [← h1] at this
    exact absurd this (by decide)
  · have := Nat.factorial_le h13
    rw [← h1] at this
    exact absurd this (by decide)

theorem l316 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSL 3 2 4 := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall _ _
  exfalso
  have := hN
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := RestrictedStd.statedClassicalModel_of_lieModel_PSL hY
  let φ' : ↥N ≃* projectiveSL 3 K := φ.trans (SymmetricLocal.statedProjEquivProjectiveSL 3 K)
  have : IsSimpleGroup (projectiveSL 3 K) :=
    OutcomeLocal.isSimpleGroup_projectiveSL (k := K) (by norm_num)
  have hs : IsSimpleGroup ↥N := φ'.isSimpleGroup
  have hnab : ∃ x y : ↥N, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ :=
      exists_ne_comm_of_center_eq_bot (OddSelector.center_projectiveSL_eq_bot (k := K)
        (by norm_num : 3 ≤ 3))
    exact ⟨φ'.symm a, φ'.symm b, fun h => hab (by simpa using congrArg φ' h)⟩
  have hJc : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  have hWalt := isEmpty_alt_of_card_L316 (card_of_lieModel_L316 hY)
  obtain ⟨p', f', hp', hp'2, hf', hsrc⟩ : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 p f ∨
        Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∨
        StatedClassicalModel (↥J ⧸ center ↥J) .PSL 3 2 2) := by
    rcases hsmall with ⟨p', f', hp', hp'2, hf', -, hm'⟩ | h7
    · exact ⟨p', f', hp', hp'2, hf',
        Or.inl (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm')⟩
    · exact ⟨3, 1, Nat.prime_three, by decide, le_rfl, Or.inr (Or.inl h7)⟩
  obtain ⟨ρ, -, -, -, -, -, -, c, hrows⟩ :=
    OutcomeLocal.faithful_even_higher_linear_socle_small_source_involution_selector hs hnab hC hα
      hJN hJc hp' hp'2 hf' hsrc hWalt (by norm_num : 3 ≤ 3) (by norm_num : 1 ≤ 4) hK φ'
  rcases hrows with ⟨σ, hF, -⟩ | hG
  · rcases hF with ⟨-, he2, -⟩ | ⟨-, -, hm34, -⟩
    · omega
    · exact not_small_of_card_20160 (card_of_lieModel_L34 (Or.inl ⟨by decide, hm34⟩)) hsmall
  · obtain ⟨-, -, -, -, -, -, hG59⟩ := hG
    rcases hG59 with ⟨-, he2, -⟩ | ⟨hn5, -⟩
    · omega
    · omega

end CFSG.ComponentClassification.GSThmB.CF23I
