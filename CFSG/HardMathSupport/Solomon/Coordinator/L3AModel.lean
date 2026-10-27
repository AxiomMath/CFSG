module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInner
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

@[expose] def CoverModel (Y : Type) [Group Y] : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
    (π = false → p ^ f ≠ 8) ∧ 2 < p ^ f ∧ Nonempty (Y ≃* ↥(slPi π 3 (p ^ f) K))

@[expose] def ProjModel (Y : Type) [Group Y] : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
    (π = false → p ^ f ≠ 8) ∧ 2 < p ^ f ∧
    Nonempty (Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))

theorem exists_piField_true (K : Type) [Field K] [Finite K] : ∃ p f : ℕ, PiField true p f K := by
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ : ∃ p, CharP K p := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card] at hn
  exact ⟨p, n, hpp, n.pos, by rw [hn]; rfl⟩

theorem false_of_quasisimple_of_solvable {Y : Type*} [Group Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hs : Group.IsSolvable Y) : False := by
  have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hq.1
  have : Nontrivial Y := by
    have := hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  exact Group.IsPerfect.not_isSolvable Y hs

theorem isSolvable_slPi_false_two {p f : ℕ} {K : Type} [Field K] (hK : PiField false p f K)
    (h2 : p ^ f = 2) :
    Group.IsSolvable ↥(slPi false 3 (p ^ f) K) ∧
      Group.IsSolvable (↥(slPi false 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi false 3 (p ^ f) K)) := by
  have hq : ModThree false (p ^ f) := by rw [h2]; rfl
  have hsol : Group.IsSolvable
      (↥(slPi false 3 (p ^ f) K) ⧸ (StatedScalars (Fin 3) K).subgroupOf (slPi false 3 (p ^ f) K)) :=
    isSolvable_statedProj_of_pow_eq_two hK.unitary h2
  have e := QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hq)
  have hQ : Group.IsSolvable
      (↥(slPi false 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi false 3 (p ^ f) K)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  refine ⟨?_, hQ⟩
  exact CFSG.Quasithin.isSolvable_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center ↥(slPi false 3 (p ^ f) K))) (by rw [QuotientGroup.ker_mk'])

theorem exists_true_data (K : Type) [Field K] [Finite K] (hc : Nat.card K % 3 = 1) :
    ∃ p f : ℕ, PiField true p f K ∧ ModThree true (p ^ f) ∧ 2 < p ^ f := by
  obtain ⟨p, f, hK⟩ := exists_piField_true K
  have hcK : Nat.card K = p ^ f := hK.card
  have hmod : ModThree true (p ^ f) := by rw [← hcK]; exact hc
  refine ⟨p, f, hK, hmod, ?_⟩
  have h1 := hK.prime.two_le
  have h2 : p ≤ p ^ f := Nat.le_self_pow (by have := hK.one_le; omega) p
  change p ^ f % 3 = 1 at hmod
  omega

theorem model_of_type {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hT : IsExtremalType Y ∨ IsSLThreeEps Y) : CoverModel Y ∨ ProjModel Y := by
  rcases hT with (⟨K, hKf, hFin, hc, ⟨e⟩⟩ | ⟨K, hKf, hFin, q, hcard, hq3, hq8, ⟨e⟩⟩) |
      (⟨K, hKf, hFin, hc, ⟨e⟩⟩ | ⟨K, hKf, hFin, q, hcard, hq3, hq8, ⟨e⟩⟩)
  · obtain ⟨p, f, hK, hmod, h2⟩ := exists_true_data K hc
    exact Or.inr ⟨true, p, f, K, hKf, hK, hmod, fun h => absurd h (by simp), h2,
      ⟨e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm⟩⟩
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hK : PiField false p f K := ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
    have hmod : ModThree false (p ^ f) := hq3
    have h2 : 2 < p ^ f := by
      by_contra hle
      have hs := isSolvable_statedProj_of_pow_eq_two hF (pow_eq_two_of_not_two_lt hF hle)
      exact false_of_quasisimple_of_solvable hq
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    exact Or.inr ⟨false, p, f, K, hKf, hK, hmod, fun _ => hq8, h2,
      ⟨e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm⟩⟩
  · obtain ⟨p, f, hK, hmod, h2⟩ := exists_true_data K hc
    exact Or.inl ⟨true, p, f, K, hKf, hK, hmod, fun h => absurd h (by simp), h2, ⟨e⟩⟩
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hK : PiField false p f K := ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
    have hmod : ModThree false (p ^ f) := hq3
    have h2 : 2 < p ^ f := by
      by_contra hle
      have hs : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (p ^ f) K) :=
        (isSolvable_slPi_false_two hK (pow_eq_two_of_not_two_lt hF hle)).1
      exact false_of_quasisimple_of_solvable hq
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    exact Or.inl ⟨false, p, f, K, hKf, hK, hmod, fun _ => hq8, h2, ⟨e⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator
