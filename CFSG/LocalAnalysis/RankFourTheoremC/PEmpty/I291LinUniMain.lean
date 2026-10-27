module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniFam
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniUni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCY
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Comp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (exists_char_pow_card)

theorem kd29LinUni_of_tables (hGA : CFSG.Open.GriessAllModelsStatement) : KD29LinUni := by
  intro Y _ _ P x z hpl L hL hLu hlu
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hYD := I291.yData_of_plane63 hpl
  have hLn : L.Normal := I291.normal_of_unique hL hLu
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hZp : IsPGroup 5 (center ↥L) := I291.isPGroup_center hYD.cfg.core hL
  have hx1 : (x : Y ⧸ primeComplementCore (G := Y) 5) ≠ 1 := by
    intro h
    have h2 := hYD.rank_cent
    have h3 : centralizer ({(x : Y ⧸ primeComplementCore (G := Y) 5)} :
        Set (Y ⧸ primeComplementCore (G := Y) 5)) = ⊤ := by
      rw [h]
      simp
    rw [h3] at h2
    have h4 := hYD.four_le
    omega
  have hxord : orderOf (x : Y ⧸ primeComplementCore (G := Y) 5) = 5 :=
    orderOf_eq_prime hYD.cfg.x_pow hx1
  rcases hlu with ⟨n, K, _, _, hpn, hpK, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, hpn, hpq, ⟨e⟩⟩
  · exact I291LinUni.linear_case hGA L hq hZp hYD.perf hxord hYD.rank_cent hpn hpK e
  · obtain ⟨r, m, hr, hchar, -, hKr⟩ := exists_char_pow_card K
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
      refine (Nat.dvd_prime_pow hr).1 ?_
      rw [← hKr, hKq]
      exact dvd_pow_self q two_ne_zero
    subst hqf
    exact I291LinUni.unitary_case hGA L hq hZp hYD.perf hxord hYD.rank_cent hpn hKq hpq e

section CertificateInstances


theorem kd29LinUni_holds : KD29LinUni :=
  kd29LinUni_of_tables CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65
