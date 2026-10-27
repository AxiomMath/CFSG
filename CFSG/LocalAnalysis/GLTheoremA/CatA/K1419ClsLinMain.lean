module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinDichot
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA Matrix
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

theorem k1419ClsLinFact_of_labels (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hJL : K1419ClsL3U3LabelFact) : K1419ClsLinFact := by
  intro S _ _ α J labK hFam hcen hα3 hα1 hin hJc hcat hZ
  obtain ⟨K, hK, hKf, d, A, u, J', h2, hd, ⟨k, hk⟩, hu, hpow, hAns, hJ', ⟨ePQ⟩⟩ :=
    k1419ClsLinData hcen hFam hα3 hα1 hin hJc
  obtain ⟨M, hM, ⟨ePS⟩, hz⟩ := k1419ClsLinLift h2 hd A u hu hpow J' hJ'
  obtain ⟨c, hc⟩ := Y10GInnLin.isScalar_of_pow_trivial h2 A 3 u hu hpow
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eM⟩, hdich⟩ :=
    k1419ClsLinDichot h2 hd A ⟨c, hc⟩ hAns M hM
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJc
  obtain ⟨n, hlab⟩ := hJL (PQuot 3 J) hQ hcat
  have e1 : PSimple 3 J ≃* StatedProj (StatedSL a E) :=
    (QuotientGroup.congr _ _ ePQ (Subgroup.map_center_eq ePQ)).trans (ePS.trans eM)
  have hZ' : Subgroup.center (PQuot 3 J') = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h2' : ePQ.symm x ∈ Subgroup.center (PQuot 3 J) := by
      rw [← Subgroup.map_center_eq ePQ.symm]
      exact Subgroup.mem_map_of_mem _ hx
    rw [hZ, Subgroup.mem_bot] at h2'
    exact ePQ.symm.injective (by rw [h2', map_one])
  have hEcard : Nat.card E = 2 ^ (k * Module.finrank K E) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hk, ← pow_mul]
  rcases hlab with ⟨hl, hn⟩ | ⟨hl, hn⟩
  · have hdict := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.A, 2, n⟩ a
      (k * Module.finrank K E) E ha hEcard hl ⟨e1⟩
    have hdict' : (⟨.A, 2, n⟩ : GLALabel) = ⟨.A, a - 1, k * Module.finrank K E⟩ := hdict
    injection hdict' with _ h1 h2n
    have hn3 : ¬ 3 ∣ Module.finrank K E := by
      intro h3
      have : 3 ∣ n := by
        rw [h2n]
        exact Dvd.dvd.mul_left h3 k
      omega
    have h3a : 3 ∣ a := by omega
    have h3E : 3 ∣ Nat.card E - 1 := by
      rw [hEcard, ← h2n]
      obtain ⟨t, ht⟩ : ∃ t, n = 2 * t := ⟨n / 2, by omega⟩
      have h4 : (4 : ℕ) ^ t % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have h5 : (2 : ℕ) ^ n = 4 ^ t := by
        rw [ht, pow_mul]
        norm_num
      rw [h5]
      omega
    obtain ⟨z, hzM, hz1, hz3, hzc, hzs⟩ := (hdich.resolve_left hn3) ⟨h3a, h3E⟩
    obtain ⟨j, hjJ, hjc, hj3, hj1⟩ := hz z hzM hzc hz3 hzs
    exact hj1 (k1419ClsCentre_eq_one hZ' hjJ hjc hj3)
  · have hdict := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.twA, 2, n⟩ a
      (k * Module.finrank K E) E ha hEcard hl ⟨e1⟩
    have hdict' : (⟨.twA, 2, n⟩ : GLALabel) = ⟨.A, a - 1, k * Module.finrank K E⟩ := hdict
    injection hdict' with h1
    cases h1

end CFSG.LocalAnalysis.GLTheoremA.K1419
