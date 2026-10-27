module

public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.ClassicalInvolution.Q3.Q3TWInputs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.WeakCT.SU4 CFSG.ClassicalInvolution.Q3.Q3Z CFSG.Timmesfeld
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

theorem map_autXp_eq_tv (e : ZMod 3 ≃+* GaloisField 3 1) :
    (Matrix.SpecialLinearGroup.map e.toRingHom : SL(2, ZMod 3) →* SL(2, GaloisField 3 1)) autXp =
      tv 0 1 1 := by
  rw [CFSG.Timmesfeld.LevisExtras.tv01_eq_sl2Upper]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [autXp, CFSG.LieType.Steinberg.sl2Upper]

theorem map_autXm_eq_tv (e : ZMod 3 ≃+* GaloisField 3 1) :
    (Matrix.SpecialLinearGroup.map e.toRingHom : SL(2, ZMod 3) →* SL(2, GaloisField 3 1)) autXm =
      tv 1 0 1 := by
  rw [CFSG.Timmesfeld.LevisExtras.tv10_eq_sl2Lower]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [autXm, CFSG.LieType.Steinberg.sl2Lower]

theorem exists_twistedLayer_three {b c : GaloisField 3 1}
    [Fact (∀ r : GaloisField 3 1, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : GaloisField 3 1, s ^ 2 + b * s + c ≠ 0) (e : ZMod 3 ≃+* GaloisField 3 1) :
    ∃ L : TwistedLayer (spinGroup (quadMinus 3 (GaloisField 3 1) b c)),
      L.lbZ = (minusLongBlock b c).comp (Matrix.SpecialLinearGroup.map e.toRingHom) ∧
      L.S = (shortBlock hirr 3 finOne).range := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := by
    intro h
    have : (3 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField 3 1) 3 2).mp (by exact_mod_cast h)
    omega
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinData_free (p := 3) (f := 1) (by norm_num) (by norm_num) hirr
  have hcardK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hσ : ∀ x, unitaryInvolution (GaloisField 3 (2 * 1)) 3 1 x = x ^ 3 := fun x => by
    rw [unitaryInvolution_apply]
    norm_num
  have hdisc := disc_eq_neg_one e hirr
  have hsurj : Function.Surjective (D.PhiSU hirr h2) :=
    MonoidHom.range_eq_top.1 (D.range_PhiSU_eq_top hcardK hirr h2)
  exact exists_twistedLayer_of D hirr h2 hσ (kleinEps_sq D hdisc) (kleinDelta_eq_neg_eps D hdisc)
    hsurj _ (by simp only [MonoidHom.comp_apply, map_autXp_eq_tv])
    (by simp only [MonoidHom.comp_apply, map_autXm_eq_tv])

theorem weakCT3MinusMap_of_collapse (hC : TD4Collapse) {N : ℕ} (hN : 4 ≤ N) :
    WeakCT3MinusMap N := by
  intro G _ U hcomm hpair htw
  obtain ⟨e⟩ := nonempty_ringEquiv_galoisField_three
  have hirr := minusCoeffs_irr 3 1
  have := fact_shortField hirr
  have hF : Nat.card (GaloisField 3 1) = 3 ^ 1 :=
    natCard_galoisField_three.trans (pow_one 3).symm
  have hadm : StatedLieAdmissible .POmegaMinus N 3 1 := ⟨Nat.prime_three, le_rfl, hN⟩
  have hcomm' : ∀ i j : Fin (N - 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a :=
    fun i j hij a ha b hb => hcomm i j hij a ha b hb
  obtain ⟨L, hL1, hL2⟩ := exists_twistedLayer_three hirr e
  obtain ⟨W, θ0, hθW, -, hθl, hθU, hθV⟩ :=
    htw ⟨N - 3, by omega⟩ ⟨N - 2, by omega⟩ (by simp only; omega) (by simp only; omega)
  obtain ⟨θ', ρ', hS', hlast, hρU, hψ⟩ := exists_minusFrame e hirr L hL1 hL2 hN U hcomm' hC hpair
    θ0 hθl hθU hθV
  obtain ⟨Ψ, hker, hrk⟩ := weakCT_minus_of_frame hadm hN (by norm_num) hF hirr U hcomm' θ' hS'
    ρ' hlast hρU hψ
  exact ⟨Ψ, hker, hrk⟩

end CFSG.ClassicalInvolution.Q3.Q3TW
