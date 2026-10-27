module

public import CFSG.Dihedral.OriginalPSL2PrimeNormalizer
public import CFSG.Dihedral.OriginalASevenPrimeMaximality
public import CFSG.Blueprint.DihedralRefinements
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem canonicalNormalizers_of_psl2_model [IsSimpleGroup G]
    (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) : d.CanonicalNormalizers := by
  constructor
  · intro p hp P hP hPS
    have hHPne := d.HP_ne_top_of_prime_sylow p hp P hP
    have hHP := d.HP_eq_C_of_psl2_model K hK e p hp P hP
    have hJP := d.JP_eq_R_of_psl2_model K hK e p hp P hP
    have hambient := d.prime_sylow_ambient_of_psl2_model K hK e p hp P hP
    have hmax : IsMaxNormalized p (d.S : Subgroup G) P :=
      ⟨hambient.2.1, hPS, fun Q hQ _hQS hPQ => hambient.2.2 Q le_top hQ hPQ⟩
    have hnoalt : ¬ HasAlternatingQuotient (d.HP P) := by
      rw [hHP]
      exact not_hasAlternatingQuotient_of_two_quotient d.C d.centralizer_oddCore_two_quotient
    have hgw := d.proper_quotients (d.HP P) hHPne
    have halt : HasCoordinates (d.HP P) ∨ HasSylowTwoQuotient (d.HP P) := by
      rcases hgw with hc | ha | ht
      · exact Or.inl hc
      · exact (hnoalt ha).elim
      · exact Or.inr ht
    refine ⟨hmax, ?_, hHPne, d.sylow_le_HP P hPS, d.normalizer_le_HP P,
      ?_, hgw, ?_, ?_, ?_, ?_⟩
    · intro D hD hPD
      exact hmax.2.2 D hD.1 hD.2.1 hPD
    · rw [hJP, inf_eq_left.mpr hP.1]
      exact hP
    · intro _hfirst
      exact ⟨hambient, hnoalt, halt⟩
    · intro hsecond
      rw [d.sigma_one_eq_empty_of_psl2_model K hK e] at hsecond
      exact hsecond.elim
    · intro ha
      exact (hnoalt ha).elim
    · intro hcent
      exact (d.prime_not_centralized_by_sylow_of_psl2_model K hK e p hp P hP hcent).elim
  · intro p hp
    rw [d.sigma_one_eq_empty_of_psl2_model K hK e] at hp
    exact hp.elim

theorem canonicalNormalizers_of_aSeven_model [IsSimpleGroup G]
    (e : G ≃* alternatingGroup (Fin 7)) (hs : d.Stationarity) : d.CanonicalNormalizers := by
  constructor
  · intro p hp P hP hPS
    have hPeq := d.prime_sylow_eq_R_of_aSeven_model e p hp P hP
    have hHPne := d.HP_ne_top_of_prime_sylow p hp P hP
    have hJP := d.JP_eq_R_of_aSeven_model e p hp P hP
    have hcard := d.HP_quotient_card_of_aSeven_model e p hp P hP
    have hnoalt := not_hasAlternatingQuotient_of_card_twentyFour (d.HP P) hcard
    have hnottwo := not_hasSylowTwoQuotient_of_card_twentyFour (d.HP P) hcard
    have hgw := d.proper_quotients (d.HP P) hHPne
    have hcoord : HasCoordinates (d.HP P) := by
      rcases hgw with hc | ha | ht
      · exact hc
      · exact (hnoalt ha).elim
      · exact (hnottwo ht).elim
    have hmax := d.prime_isMaxNormalized_of_aSeven_model e p hp P hP hPS
    refine ⟨hmax, ?_, hHPne, d.sylow_le_HP P hPS, d.normalizer_le_HP P,
      ?_, hgw, ?_, ?_, ?_, ?_⟩
    · intro D hD hPD
      exact hmax.2.2 D hD.1 hD.2.1 hPD
    · rw [hJP, inf_eq_left.mpr hP.1]
      exact hP
    · intro hfirst
      rw [d.sigma_zero_eq_empty_of_aSeven_model e] at hfirst
      exact hfirst.elim
    · intro _hsecond
      refine ⟨d.exists_prime_fixed_fourgroup_of_aSeven_model e p hp P hP,
        ?_, hnottwo, Or.inl hcoord, fun _ => hcoord⟩
      intro V hV _hVS hcent
      have haction := d.prime_normalizer_fullAction_of_aSeven_model e p hp P hP V hV hcent
      have hJPR : d.JP P ≤ d.R := hJP.le
      have hRcent : d.R ≤ Subgroup.centralizer (V : Set G) := hPeq ▸ hcent
      exact ⟨haction.1, haction.2,
        le_inf (le_inf hJPR (hJPR.trans hRcent)) (oddCoreOf_le (d.HP P))⟩
    · intro ha
      exact (hnoalt ha).elim
    · intro hcent
      exact (d.prime_not_centralized_by_sylow_of_aSeven_model e p hp P hP hcent).elim
  · intro p hp q hq P Q hP hQ hPS _hQS hP0 hQ1
    have hpR := ((mem_sigma_iff 1 p d.R).mp hp).1
    have hqR := ((mem_sigma_iff 1 q d.R).mp hq).1
    have hPeq := d.prime_sylow_eq_R_of_aSeven_model e p hpR P hP
    have hQeq := d.prime_sylow_eq_R_of_aSeven_model e q hqR Q hQ
    have hP1 : P ≤ Subgroup.centralizer (d.V 1 : Set G) := by
      rw [hPeq]
      exact hQeq ▸ hQ1
    have hcycle0 := (d.prime_normalizer_fullAction_of_aSeven_model e p hpR P hP (d.V 0)
      (isFourGroup_of_isKleinFour _ (d.V_isKleinFour_general 0)) hP0).2
    have hcycle1 := (d.prime_normalizer_fullAction_of_aSeven_model e p hpR P hP (d.V 1)
      (isFourGroup_of_isKleinFour _ (d.V_isKleinFour_general 1)) hP1).2
    obtain ⟨_, _, _, _, _, _, htwo, _⟩ := hs
    have hcent := (htwo (d.HP P) (d.HP_ne_top_of_prime_sylow p hpR P hP)
      (d.sylow_le_HP P hPS)).2 hcycle0 hcycle1
    exact le_inf (inf_le_left.trans (d.JP_eq_R_of_aSeven_model e p hpR P hP).le)
      (inf_le_left.trans hcent.1)

theorem canonicalNormalizers [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hs : d.Stationarity) : d.CanonicalNormalizers := by
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hL
  · exact d.canonicalNormalizers_of_aSeven_model hA.some hs
  · obtain ⟨r, k, hr, hrodd, hsize, ⟨e⟩⟩ := hL
    let _ : Fact r.Prime := hr
    have hk : k ≠ 0 := by
      intro h
      simp [h] at hsize
    have hK : IsOddPrimePower (Nat.card (GaloisField r k)) :=
      ⟨r, k, hr.out, hrodd, by omega, GaloisField.card r k hk⟩
    exact d.canonicalNormalizers_of_psl2_model (GaloisField r k) hK e

theorem prime_not_hasAlternatingQuotient [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    ¬ HasAlternatingQuotient (d.HP P) := by
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hL
  · exact not_hasAlternatingQuotient_of_card_twentyFour (d.HP P)
      (d.HP_quotient_card_of_aSeven_model hA.some p hp P hP)
  · obtain ⟨r, k, hr, hrodd, hsize, ⟨e⟩⟩ := hL
    let _ : Fact r.Prime := hr
    have hk : k ≠ 0 := by
      intro h
      simp [h] at hsize
    have hK : IsOddPrimePower (Nat.card (GaloisField r k)) :=
      ⟨r, k, hr.out, hrodd, by omega, GaloisField.card r k hk⟩
    rw [d.HP_eq_C_of_psl2_model (GaloisField r k) hK e p hp P hP]
    exact not_hasAlternatingQuotient_of_two_quotient d.C d.centralizer_oddCore_two_quotient

theorem alternatingQPrimary [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : d.AlternatingQPrimary := by
  intro p hp P hP _hPS ha
  exact (d.prime_not_hasAlternatingQuotient hnonab p hp P hP ha).elim

theorem canonicalNormalizersFull [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hs : d.Stationarity) : d.CanonicalNormalizersFull :=
  ⟨d.canonicalNormalizers hnonab hs, d.alternatingQPrimary hnonab⟩

end CFSG.DihedralBlueprint.OriginalData
