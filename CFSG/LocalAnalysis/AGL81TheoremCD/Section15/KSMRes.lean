module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1512Facts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Blueprint.Multiplier CFSG.Models CFSG.LocalAnalysis.RankThreeUC.S15

theorem KSMRes_of_griess (hG : CFSG.Open.GriessAllModelsStatement) : KSMRes := by
  intro K _ _ hq d l Q hQ2 hpar e hodd
  obtain ⟨d1, hv⟩ := d
  rcases hpar with ⟨hdA, hoddn⟩ | ⟨hdT, hevenn⟩
  · subst hdA
    obtain ⟨e⟩ := e
    have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hQ2] at hm
    have hLM : LieModel (K ⧸ Subgroup.center K) .PSL (l + 1) 2 Q.exponent :=
      ⟨hm.1, Or.inl hm⟩
    obtain ⟨k, hk⟩ := ksm_exc_two .PSL (l + 1) Q.exponent
    have hz := ksm_dvd_of_values hG hq hLM
      (a := Nat.gcd (l + 1) (2 ^ Q.exponent - 1))
      (by
        show Nat.gcd (l + 1) (2 ^ Q.exponent - 1) * 1 =
          Nat.gcd (l + 1) (2 ^ Q.exponent - 1)
        rw [mul_one]) hk hodd
    intro h3z
    have h3d : 3 ∣ Nat.gcd (l + 1) (2 ^ Q.exponent - 1) := h3z.trans hz
    have h3s : 3 ∣ 2 ^ Q.exponent - 1 := h3d.trans (Nat.gcd_dvd_right _ _)
    have h3g : 3 ∣ Nat.gcd 3 (2 ^ Q.exponent - 1) := Nat.dvd_gcd (dvd_refl 3) h3s
    rw [ksm_gcd_three_two_pow_odd hoddn] at h3g
    exact Nat.Prime.not_dvd_one Nat.prime_three h3g
  · subst hdT
    obtain ⟨e⟩ := e
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA l Q hv e
    rw [hQ2] at hm
    have hLM : LieModel (K ⧸ Subgroup.center K) .PSU (l + 1) 2 Q.exponent :=
      ⟨hm.1, Or.inl hm⟩
    obtain ⟨k, hk⟩ := ksm_exc_two .PSU (l + 1) Q.exponent
    have hz := ksm_dvd_of_values hG hq hLM
      (a := Nat.gcd (l + 1) (2 ^ Q.exponent + 1))
      (by
        show Nat.gcd (l + 1) (2 ^ Q.exponent + 1) * 1 =
          Nat.gcd (l + 1) (2 ^ Q.exponent + 1)
        rw [mul_one]) hk hodd
    intro h3z
    have h3d : 3 ∣ Nat.gcd (l + 1) (2 ^ Q.exponent + 1) := h3z.trans hz
    exact CFSG.StandardType.UnitaryCenter.not_three_dvd_two_pow_add_one_of_even hevenn
      (h3d.trans (Nat.gcd_dvd_right _ _))

section CertifiedKSMRes


theorem KSMRes_holds : KSMRes :=
  KSMRes_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CertifiedKSMRes

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
