module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Main
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3MinusIn
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3MinusOut

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8


theorem d4_ord3Alt_minus {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (b : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hb : orderOf b = 3) :
    Ord3Alt p b := by
  by_cases hin : b ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
  · obtain ⟨g, rfl⟩ := hin
    exact d4_ord3Alt_inner_minus σ hp hp2 hf hK hσ hq g (by rw [← hb]; exact pow_orderOf_eq_one _)
  · exact d4_ord3Alt_outer_minus σ hp hp2 hp3 hf hK hσ hq b hb hin

theorem d4Ord3 : D4Ord3 := by
  intro r Y _ _ hr hr2 hr3 hY b hb
  obtain ⟨f, hf, hm⟩ := hY
  refine d4_ord3_of_alt hr hr2 hf hm (fun K _ _ hK σ hσ b hb => ?_) b hb
  have h3 : ¬ 3 ∣ r ^ f := fun h =>
    hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  rcases (by omega : r ^ f % 3 = 1 ∨ r ^ f % 3 = 2) with h | h
  · exact d4_ord3Alt_plus σ hr hr2 hr3 hf hK hσ h b hb
  · exact d4_ord3Alt_minus σ hr hr2 hr3 hf hK hσ h b hb

end CFSG.OddStandard.GH71.S55
