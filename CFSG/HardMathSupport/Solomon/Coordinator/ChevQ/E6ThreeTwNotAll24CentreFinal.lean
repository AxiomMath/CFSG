module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Class
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section Main


theorem strongModel_of_d5_component (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    (h3q : 3 ∣ q + 1) (h : twistedE6InndiagGL K σ) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    (hdim : twE6MatFixDim K σ h = 46)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    ∃ r e : ℕ, ringChar K = r ∧ DStrongModel J 5 r e := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [← hqf]; exact hKq
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := by intro c; rw [← hqf]; exact hσ c
  have hpℓ : 3 ≠ ringChar K := fun h' => hK3 h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp hf Nat.prime_three (by norm_num) hpℓ
  have hh3' : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  have hh1' : (h : ModGL TwistTag.E6.tag K) ≠ 1 := fun h' => hh1 (Subtype.ext h')
  obtain ⟨S, a, ι, hDq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconj, hg0⟩ :=
    exists_langSetup_conj_of_inndiag_twE6_phi hp hf hK' σ hσ' Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      monomialToralAt_E6_three (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) hh3' hh1'
  have hker := twE6MatFixDim_eq_of_conj σ h S.D.g0 a hg0
  have hk : (kernelRoots (rootCharHom a)).ncard = 40 := by omega
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hL3 (fun h => absurd h (by decide)) hT
    hap h1
  rw [← fixSubgroup_eq_fixedPoints] at hJ
  obtain ⟨i, hQS, hi⟩ := components_of_langSetup S Nat.prime_three ι hinj hrange
    (twistedE6InndiagConj K σ h) hconj hT hap h1 hTame hJ
  have e : J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hi)
  have h3q' : 3 ∣ S.D.q + 1 := by rw [hDq, ← hqf]; exact h3q
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hDq]; exact hFr c
  obtain ⟨r, e', hr, -, hmodel⟩ := d5_class_strongModel S hFr' hΦ hL3 hT hap h3q' hk i
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  refine ⟨r, e', ?_, DStrongModel.of_equiv e hmodel⟩
  rw [← hr, ringChar.eq (AlgebraicClosure K) (ringChar K)]

theorem twE6ConnCentreD5 : TwE6ConnCentreD5 := by
  intro K _ _ σ q E hcube f hfE hf1 hdim J hJ
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hcube.three_dvd
    omega
  have hf3 : f ^ 3 = 1 := hcube.elemAbelian.2 f hfE
  obtain ⟨h, hh, hd⟩ := hdim
  have hinj := twE6_conj_injective K σ q hcube.frob hcube.card_field hq2
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  have hh3 : h ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hh, map_one]
    exact hf3
  obtain ⟨r, e, -, hmodel⟩ := strongModel_of_d5_component K σ q hcube.char_ne_three hcube.frob
    hcube.card_field hq2 hcube.three_dvd h hh1 hh3 hd (hh ▸ hJ)
  exact not_three_dvd_card_center_of_pow (n := 4) (by omega) hmodel.2.2

end Main

end KSConn

section Export

open KSConn


theorem twE6ConnCentre : TwE6ConnCentre := twE6ConnCentre_of_d5 twE6ConnCentreD5

end Export

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
