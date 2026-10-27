module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial

namespace Lemma41aL3

variable {F : Type} [Field F]

theorem ker_statedProjMk_eq_bot_of_not_dvd (h3 : ¬ 3 ∣ Nat.card F - 1) :
    (statedProjMk (StatedSL 3 F)).ker = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet := (linConj_mem_statedSL (z : GL (Fin 3) F)).mp z.2
  rw [← hc] at hdet
  have hc3 : (c : F) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_smul] using hdet
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using hc3))
    have h2 : orderOf c ∣ Nat.card F - 1 := Nat.card_units F ▸ orderOf_dvd_natCard c
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h2) h3
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem statedProjMk_injective_of_not_dvd (h3 : ¬ 3 ∣ Nat.card F - 1) :
    Function.Injective (statedProjMk (StatedSL 3 F)) :=
  (MonoidHom.ker_eq_bot_iff _).mp (ker_statedProjMk_eq_bot_of_not_dvd h3)

theorem nonempty_centralizer_equiv_GL_of_not_dvd [Finite F] (hodd : Odd (Nat.card F))
    (h3 : ¬ 3 ∣ Nat.card F - 1) {w : StatedProj (StatedSL 3 F)} (hw : orderOf w = 2) :
    Nonempty (↥(centralizer ({w} : Set (StatedProj (StatedSL 3 F)))) ≃* GL (Fin 2) F) := by
  have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (fun z hz => linConj_ker_pow_three z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  obtain ⟨φ, hφ, hrange⟩ :=
    exists_phi h2 (StatedSL 3 F) (fun A => linConj_mem_statedSL A) ha ha1
  obtain ⟨N, hN, hcard, ⟨e⟩⟩ := exists_normal_quotient_equiv (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (ker_statedProjMk_le_center _)
    (fun z hz => linConj_ker_pow_three z hz) ha φ hφ hrange
  rw [ker_statedProjMk_eq_bot_of_not_dvd h3, Subgroup.card_bot] at hcard
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq (Subgroup.eq_bot_of_card_eq N hcard)).trans
    QuotientGroup.quotientBot)⟩

end Lemma41aL3

namespace Lemma41aU3

variable {p n : ℕ} {F : Type} [Field F]

theorem ker_statedProjMk_eq_bot_of_not_dvd (h : UnitaryFieldData p n F) (h3 : ¬ 3 ∣ p ^ n + 1) :
    (statedProjMk (StatedSU 3 (p ^ n) F)).ker = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rw [card_ker h]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3

theorem statedProjMk_injective_of_not_dvd (h : UnitaryFieldData p n F) (h3 : ¬ 3 ∣ p ^ n + 1) :
    Function.Injective (statedProjMk (StatedSU 3 (p ^ n) F)) :=
  (MonoidHom.ker_eq_bot_iff _).mp (ker_statedProjMk_eq_bot_of_not_dvd h h3)

theorem nonempty_centralizer_equiv_GU2_of_not_dvd (h : UnitaryFieldData p n F) (hp2 : p ≠ 2)
    (h3 : ¬ 3 ∣ p ^ n + 1) {w : StatedProj (StatedSU 3 (p ^ n) F)} (hw : orderOf w = 2) :
    Nonempty (↥(centralizer ({w} : Set (StatedProj (StatedSU 3 (p ^ n) F)))) ≃*
      ↥(GU2Stated (p ^ n) F)) := by
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSU 3 (p ^ n) F))
    (statedProjMk_surjective _) (fun z hz => ker_pow_three h z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  obtain ⟨N, hN, hcard, ⟨e⟩⟩ := Lemma41aL3.exists_normal_quotient_equiv
    (statedProjMk (StatedSU 3 (p ^ n) F)) (statedProjMk_surjective _)
    (ker_statedProjMk_le_center _) (fun z hz => ker_pow_three h z hz) ha
    (phi h c) (phi_injective h c) (by rw [phi_range h hp2 c, hc])
  rw [ker_statedProjMk_eq_bot_of_not_dvd h h3, Subgroup.card_bot] at hcard
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq (Subgroup.eq_bot_of_card_eq N hcard)).trans
    QuotientGroup.quotientBot)⟩

end Lemma41aU3

end CFSG.GH74.GLS.IVK.Proofs2
