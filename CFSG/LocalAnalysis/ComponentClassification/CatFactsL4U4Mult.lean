module

public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCover
import CFSG.Models.Blueprint

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cover82

open CFSG Subgroup

namespace Mult

theorem models_lieModel {X : Type} [Group X] {τ : Assembly.LowTwoRank.StatedLieTag} {p f : ℕ}
    (hm : Blueprint.LieModel X τ 4 p f) : Models.LieModel X τ 4 p f :=
  CFSG.Models.LieModel.of_blueprint_of_ne_zero (by decide) hm

theorem card_table_dvd_four {t : Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (hp2 : p ≠ 2)
    (ht : t = .PSL ∨ (t = .PSU ∧ p ^ f ≠ 3)) :
    Nat.card (Blueprint.Multiplier.generic t 4 p f ×
      Blueprint.Multiplier.exceptional t 4 p f) ∣ 4 := by
  have he : Blueprint.Multiplier.exceptionalOrders t 4 p f = (1, 1) := by
    rcases ht with rfl | ⟨rfl, h3⟩ <;> unfold Blueprint.Multiplier.exceptionalOrders <;>
      split <;> simp_all
  have hg : (Blueprint.Multiplier.genericOrders t 4 p f).1 ∣ 4 ∧
      (Blueprint.Multiplier.genericOrders t 4 p f).2 = 1 := by
    rcases ht with rfl | ⟨rfl, -⟩
    · exact ⟨Nat.gcd_dvd_left _ _, rfl⟩
    · exact ⟨Nat.gcd_dvd_left _ _, rfl⟩
  simp only [Blueprint.Multiplier.generic, Blueprint.Multiplier.exceptional, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, he, hg.2]
  simpa using hg.1

theorem card_center_dvd_hopfMultiplier {S : Type} [Group S] {Q : Type} [Group Q]
    [Group.IsPerfect Q] (e : Q ⧸ center Q ≃* S) :
    Nat.card (center Q) ∣ Nat.card (Open.griessHopfMultiplier S) := by
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq hker.le)

end Mult

theorem multiplierL4U4 :
    MultiplierL4U4 := by
  intro Y _ _ hY p f hp hp2 hf hm
  have : Group.IsPerfect Y := hY.1
  have hM : Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y)) ∣ 4 := by
    rcases hm with hm | ⟨hm, hq⟩
    · obtain ⟨-, ⟨e⟩⟩ := LieType.Steinberg.CentralExt.GriessClassical.griess_classical_of_large
        .PSL (Mult.models_lieModel hm) (Or.inl rfl)
      rw [Nat.card_congr e.toEquiv]
      exact Mult.card_table_dvd_four hp2 (Or.inl rfl)
    · have h3 : 3 ≤ p ^ f :=
        le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
      obtain ⟨-, ⟨e⟩⟩ := LieType.Steinberg.CentralExt.GriessClassical.griess_classical_of_large
        .PSU (Mult.models_lieModel hm) (Or.inr (Or.inl ⟨rfl, ⟨2, rfl⟩, Or.inl (by omega)⟩))
      rw [Nat.card_congr e.toEquiv]
      exact Mult.card_table_dvd_four hp2 (Or.inr ⟨rfl, hq⟩)
  have hdvd := Mult.card_center_dvd_hopfMultiplier (MulEquiv.refl (Y ⧸ center Y))
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hdvd.trans (hM.trans (by norm_num : 4 ∣ 2 ^ 2)))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card hk

end Cover82

end CFSG.ComponentClassification.CatFactsL4U4
