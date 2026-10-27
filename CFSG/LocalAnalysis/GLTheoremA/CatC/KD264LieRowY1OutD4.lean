module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutD4Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsSOBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem kd264Y1OutD4_holds : KD264Y1OutD4 := by
  intro d hfin hP hns hk2 hk3 hpR a ha ha3
  rcases d with ⟨e, hv⟩
  obtain ⟨q, rfl⟩ := hP
  have hq3 : q.p ≠ 3 := by
    simpa [TauCeti.LieTypeIndex.characteristic_D] using characteristic_ne_three_of_not_chev ⟨_, hv⟩ hns
  obtain ⟨-, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D 4 q hv (MulEquiv.refl _)
  · exfalso
    obtain ⟨hadm, K, hfield, hfinite, hK, ⟨eM⟩⟩ := hSC
    letI := hfield
    have hchar : ringChar K = q.p :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
    have h3 : (3 : K) ≠ 0 := by
      intro h
      have hdvd : ringChar K ∣ 3 := by
        rw [← CharP.cast_eq_zero_iff K (ringChar K) 3]
        exact_mod_cast h
      rw [hchar] at hdvd
      exact hq3 ((Nat.prime_dvd_prime_iff_eq hadm.1 Nat.prime_three).mp hdvd)
    obtain ⟨E, hE, hcard⟩ := d4Model_exists_card81 K h3
    have hE' := isElemAbelian_three_map eM.symm hE
    have hc : Nat.card (E.map eM.symm.toMonoidHom) = 3 ^ 4 := by
      rw [← hcard]
      exact Nat.card_congr (MulEquiv.subgroupMap eM.symm E).toEquiv.symm
    have hrank := le_pRank_of_elemAbelian_card (by norm_num) le_top hE' hc
    omega
  · omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
