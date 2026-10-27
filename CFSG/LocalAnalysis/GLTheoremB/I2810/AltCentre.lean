module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief
import CFSG.Alternating.Multipliers.Main
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCover

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltCentre

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem card_ker_dvd_multiplier {E : Type} [Group E] [Finite E] [Group.IsPerfect E] {n : ℕ}
    (q : E →* ↥(alternatingGroup (Fin n))) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) :
    Nat.card q.ker ∣ Nat.card (hopfMultiplier (alternatingGroup (Fin n))) := by
  have hsurj := hopfMultiplierToKer_surjective q hq hker
  have key := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (hopfMultiplierToKer q hq hker).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv] at key
  exact Dvd.intro _ key.symm

theorem center_bot_of_hyp28Two (h : Setup28 W K S)
    (h2 : Hyp28Two W K S) : Subgroup.center ↥(bar W K) = ⊥ := by
  obtain ⟨⟨hq, n, hn5, ⟨e⟩⟩, hnA6, hnHat6, hnHat7, -⟩ := h2
  haveI : Group.IsPerfect ↥(bar W K) := hq.1
  set Zc := Subgroup.center ↥(bar W K) with hZc
  let q : ↥(bar W K) →* ↥(alternatingGroup (Fin n)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' Zc)
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Zc := by
    ext x
    simp [q, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hdvd := card_ker_dvd_multiplier q hqs hker.le
  rw [hker] at hdvd
  have hodd : Odd (Nat.card Zc) := BlocksChief.centre_odd_aux h
  have hcenter_iso : Nat.card Zc = 1 → Nonempty (↥(bar W K) ≃* ↥(alternatingGroup (Fin n))) := by
    intro h1
    have hZ : Zc = ⊥ := Subgroup.card_eq_one.1 h1
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot (G := ↥(bar W K)))).symm.trans e⟩
  rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n) with rfl | rfl | rfl | h8
  · rw [hopfMultiplier_alternatingGroup_five.2] at hdvd
    have hle : Nat.card Zc ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨c, hc⟩ : ∃ c, Nat.card Zc = c := ⟨_, rfl⟩
    rw [hc] at hdvd hodd hle
    interval_cases c
    · exact absurd hodd (by decide)
    · exact Subgroup.card_eq_one.1 hc
    · exact absurd hodd (by decide)
  · exfalso
    rw [hopfMultiplier_alternatingGroup_six.2] at hdvd
    have hle : Nat.card Zc ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨c, hc⟩ : ∃ c, Nat.card Zc = c := ⟨_, rfl⟩
    rw [hc] at hdvd hodd hle
    interval_cases c <;> first | exact absurd hodd (by decide) | exact absurd hdvd (by decide) | skip
    · exact hnA6 (hcenter_iso hc)
    · exact hnHat6 ⟨hq.1.commutator_eq_top, hc, ⟨e⟩⟩
  · rw [hopfMultiplier_alternatingGroup_seven.2] at hdvd
    have hle : Nat.card Zc ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨c, hc⟩ : ∃ c, Nat.card Zc = c := ⟨_, rfl⟩
    rw [hc] at hdvd hodd hle
    interval_cases c <;> first | exact absurd hodd (by decide) | exact absurd hdvd (by decide) | skip
    · exact Subgroup.card_eq_one.1 hc
    · exact absurd ⟨hq.1.commutator_eq_top, hc, ⟨e⟩⟩ hnHat7
  · rw [card_hopfMultiplier_alternatingGroup h8] at hdvd
    have hle : Nat.card Zc ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨c, hc⟩ : ∃ c, Nat.card Zc = c := ⟨_, rfl⟩
    rw [hc] at hdvd hodd hle
    interval_cases c
    · exact absurd hodd (by decide)
    · exact Subgroup.card_eq_one.1 hc
    · exact absurd hodd (by decide)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltCentre
