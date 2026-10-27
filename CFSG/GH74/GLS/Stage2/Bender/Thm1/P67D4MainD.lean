module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Bypass
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Inner
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Par

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2.Ivk47

theorem cf67CoreFull_D4_core'' (hleaf : G2D4InnerPlaneGen) (hA2m : D4OuterThreeA2Minus)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    CF67CoreFull (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  intro hs hn r V Z h2 h3
  obtain ⟨hr, hrodd, hVe, hVc, -⟩ := id h2
  have := hVe
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hchar : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  by_cases hrp : r = p
  · subst hrp
    exact d4_false_of_rp hp2 hf K hK σ hσ h2 h3
  · by_cases hinn : ∀ v ∈ V, v ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
    · exact d4_false_of_inner hleaf hp hp2 hf K hK σ hσ hr hrodd hrp hn h2 h3 hinn
    · push Not at hinn
      obtain ⟨φ, hφV, hφout⟩ := hinn
      by_cases hr3 : r = 3
      · subst hr3
        have hp3 : p ≠ 3 := fun h => hrp h.symm
        have hq3 : ¬ 3 ∣ p ^ f := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm
        have hq12 : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by omega
        rcases hq12 with hq | hq
        · exact d4_false_of_outer_three_q1 d4OuterThreeA2Toral_thm hp hp2 hp3 hf hq K hK σ hσ h2
            h3 ⟨φ, hφV, hφout⟩
        · exact d4_false_of_outer_three_q2 hA2m hp hp2 hp3 hf hq K hK σ hσ h2 h3
            ⟨φ, hφV, hφout⟩
      · have hr3' : 3 < r := by
          have := hr.two_le
          have h2' : r ≠ 2 := by
            rintro rfl
            exact absurd hrodd (by decide)
          have h4 : r ≠ 4 := by
            rintro rfl
            exact absurd hr (by decide)
          omega
        exact d4_false_of_field_large hp hp2 hf K hK σ hσ hr hr3' h2 h3 ⟨φ, hφV, hφout⟩

theorem cf67CoreFull_D4'' (hleaf : G2D4InnerPlaneGen) (hA2m : D4OuterThreeA2Minus) (Y : Type)
    [Group Y] [Finite Y] (hY : FD4 Y) : CF67CoreFull Y := by
  obtain ⟨p, f, hp, hf, hp2, hM⟩ := hY
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf (twisted_of_lieModel_D4 hM)
  exact CF67CoreFull.of_mulEquiv e (cf67CoreFull_D4_core'' hleaf hA2m hp hp2 hf K hK σ hσ)

theorem cf67D4_thm_of_a2Minus (hleaf : G2D4InnerPlaneGen) (hA2m : D4OuterThreeA2Minus) :
    CF67D4 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_D4'' hleaf hA2m Y hY)
    (fun J _ _ hJ hY r hr _ hd => cf67CoreDeriv_D4_cover J hJ hY r hr hd)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
