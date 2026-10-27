module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Uni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Comp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (exists_char_pow_card)

theorem kd291LinUniModel_of_tables (hGA : CFSG.Open.GriessAllModelsStatement) :
    KD291LinUniModel := by
  intro p Y _ _ P x z L hcfg
  have hYD := hcfg.data
  have hprime := hYD.cfg.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp5 := hYD.cfg.five_le
  have hLn : L.Normal := I291.normal_of_unique hcfg.comp hcfg.uniq
  have hq : CFSG.Open.IsQuasisimple ↥L := hcfg.comp.2.2
  have hZp : IsPGroup p (center ↥L) := I291.isPGroup_center hYD.cfg.core hcfg.comp
  have hx1 : x ≠ 1 := by
    intro h
    have h2 := hYD.rank_cent
    have h3 : centralizer ({x} : Set Y) = ⊤ := by
      rw [h]
      simp
    rw [h3] at h2
    have h4 := hYD.four_le
    omega
  have hxord : orderOf x = p := orderOf_eq_prime hYD.cfg.x_pow hx1
  rcases hcfg.linuni with ⟨n, K, _, _, hpn, hpK, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, hpn, hpq, ⟨e⟩⟩
  · exact Or.inl (L6KD291.linear_model hGA hp5 L hq hZp hYD.perf hxord hYD.rank_cent hpn hpK e)
  · obtain ⟨r, m, hr, hchar, -, hKr⟩ := exists_char_pow_card K
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
      refine (Nat.dvd_prime_pow hr).1 ?_
      rw [← hKr, hKq]
      exact dvd_pow_self q two_ne_zero
    subst hqf
    exact Or.inr (L6KD291.unitary_model hGA hp5 L hq hZp hYD.perf hxord hYD.rank_cent hpn hKq hpq e)

section CertificateInstances


theorem kd291LinUniModel_holds : KD291LinUniModel :=
  kd291LinUniModel_of_tables CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
