module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourDefs
public import CFSG.Sporadic.Recognition.SuzMultiplier

public section

namespace CFSG.ComponentClassification.RankTwoL3Four

open Subgroup CFSG.Open CFSG.CosetTable CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.Recognition.SuzMultiplier CFSG.Sporadic.Recognition.CoverTransfer

theorem suzMultiplierSix_of_checks
    (hTab : suzTabCheck = true) (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1) (hL1 : SuzIndexP2) (hL2 : SuzCardP2) :
    SuzMultiplierSix := by
  intro E _ _ hE π hπ hker
  obtain ⟨hfin, -⟩ := card_suzCover_le hL0 hL1 hL2
  have f := suzEquivM
  have e : E ⧸ π.ker ≃* suzM := (QuotientGroup.quotientKerEquivOfSurjective π hπ).trans f
  obtain ⟨q, hq⟩ : ∃ q : E →* suzM, ∀ x, q x = e (QuotientGroup.mk x) :=
    ⟨MonoidHom.comp (MulEquiv.toMonoidHom e) (QuotientGroup.mk' π.ker), fun _ => rfl⟩
  have hqs : Function.Surjective q := fun y => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm y)
    exact ⟨x, by rw [hq, hx, MulEquiv.apply_symm_apply]⟩
  have hqker : q.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, hq, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨φ, hφ, -⟩ := exists_surjective_lift (isPresentation_suzGen hTab)
    suzCommW_mem_commutator (lift_suzCommW hTab) q hqs (hqker ▸ hker)
  have hP : Nat.card SuzCover = Nat.card φ.ker * Nat.card E := by
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hφ).toEquiv, mul_comm]
  have hE' : Nat.card E = Nat.card q.ker * 448345497600 := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hqs).toEquiv,
      suzM_card_chain, mul_comm]
  have hm : Nat.card φ.ker * Nat.card q.ker = Nat.card (griessHopfMultiplier suzM) := by
    have h1 : 448345497600 * (Nat.card φ.ker * Nat.card q.ker) =
        448345497600 * Nat.card (griessHopfMultiplier suzM) := by
      rw [← card_suzCover hTab, hP, hE']
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have h2 : Nat.card q.ker ∣ Nat.card (griessHopfMultiplier suzM) := Dvd.intro_left _ hm
  rw [← hqker]
  rcases card_griessHopfMultiplier_M hTab hRho0 hL0 hL1 hL2 with h36 | h36 <;> rw [h36] at h2
  · exact h2.trans (by norm_num)
  · exact h2

end CFSG.ComponentClassification.RankTwoL3Four
