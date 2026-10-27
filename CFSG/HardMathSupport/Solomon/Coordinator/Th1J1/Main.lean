module

public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.StepC
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.LemmaZ
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.KeyLemma
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Reduced

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_centralizer {X : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.centralizer (X : Set G)) : k ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : x * k = k * x := Subgroup.mem_centralizer_iff.1 hk x hx
    have h1 : k * x * k⁻¹ = x := by rw [← this]; group
    rw [h1]; exact hx
  · intro hx
    have hk' : k⁻¹ ∈ Subgroup.centralizer (X : Set G) := inv_mem hk
    have : (k * x * k⁻¹) * k⁻¹ = k⁻¹ * (k * x * k⁻¹) :=
      Subgroup.mem_centralizer_iff.1 hk' _ hx
    have h1 : x = k⁻¹ * (k * x * k⁻¹) * k := by group
    rw [h1, ← this]
    simpa [mul_assoc] using hx

theorem le_normalizer_jOf (S : Subgroup G) : S ≤ Subgroup.normalizer (jOf S : Set G) := by
  simpa [Sec7.tripleOf_zero] using Sec7.le_normalizer_tripleOf (Subgroup.le_normalizer (H := S)) 0

theorem le_normalizer_omegaOneZ_jOneOf (S : Subgroup G) :
    S ≤ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) := by
  simpa [Sec7.tripleOf_one] using Sec7.le_normalizer_tripleOf (Subgroup.le_normalizer (H := S)) 1

theorem le_normalizer_omegaOneZ (S : Subgroup G) :
    S ≤ Subgroup.normalizer (omegaOneZ S : Set G) := by
  simpa [Sec7.tripleOf_two] using Sec7.le_normalizer_tripleOf (Subgroup.le_normalizer (H := S)) 2

theorem fac_two_one {R S : Subgroup G} (h : Hyp R S) :
    Fac R (omegaOneZ S) (omegaOneZ (jOneOf S)) := by
  refine fac_of_local (le_normalizer_omegaOneZ S) (le_normalizer_omegaOneZ_jOneOf S) ?_ R h
  intro R L H hR _ hLR hLn hH hHn _ hHc hLodd hRLS
  have hHS : H ≤ S := hH ▸ inf_le_left
  obtain ⟨U, hUR, hUn, hU, hZU, hUH, hHU, hUred⟩ :=
    exists_reduced hR.le hR.two hR.syl hHS hHn hHc
  have hJ := jOneOf_le_centralizer_of_reduced hR.not3 hR.not5 hR.le hR.two hLR hLn hH hLodd
    hRLS hUR hUn hU hUH hHU hUred
  set K := Subgroup.centralizer (U : Set G) ⊓ R with hK
  have hKR : K ≤ R := inf_le_right
  have hKn : R ≤ Subgroup.normalizer (K : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hrU : r ∈ Subgroup.normalizer (U : Set G) := hUn hr
    have hrU' : r⁻¹ ∈ Subgroup.normalizer (U : Set G) := inv_mem hrU
    constructor
    · rintro ⟨hxc, hxR⟩
      refine ⟨Subgroup.mem_centralizer_iff.2 fun u hu => ?_, R.mul_mem (R.mul_mem hr hxR)
        (R.inv_mem hr)⟩
      have hu' : r⁻¹ * u * r ∈ U := by
        simpa using (Subgroup.mem_normalizer_iff.1 hrU' u).1 hu
      have := Subgroup.mem_centralizer_iff.1 hxc _ hu'
      calc u * (r * x * r⁻¹) = r * ((r⁻¹ * u * r) * x) * r⁻¹ := by group
        _ = r * (x * (r⁻¹ * u * r)) * r⁻¹ := by rw [this]
        _ = r * x * r⁻¹ * u := by group
    · rintro ⟨hxc, hxR⟩
      have hxR' : x ∈ R := by
        have := R.mul_mem (R.mul_mem (R.inv_mem hr) hxR) hr
        simpa [mul_assoc] using this
      refine ⟨Subgroup.mem_centralizer_iff.2 fun u hu => ?_, hxR'⟩
      have hu' : r * u * r⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hrU u).1 hu
      have := Subgroup.mem_centralizer_iff.1 hxc _ hu'
      have h2 : (r * u * r⁻¹) * (r * x * r⁻¹) = (r * x * r⁻¹) * (r * u * r⁻¹) := this
      have h3 : r * (u * x) * r⁻¹ = r * (x * u) * r⁻¹ := by
        calc r * (u * x) * r⁻¹ = (r * u * r⁻¹) * (r * x * r⁻¹) := by group
          _ = (r * x * r⁻¹) * (r * u * r⁻¹) := h2
          _ = r * (x * u) * r⁻¹ := by group
      simpa using h3
  have hJK : jOneOf S ≤ S ⊓ K :=
    le_inf (Sec7.jOneOf_le S) (le_inf hJ ((Sec7.jOneOf_le S).trans hR.le))
  have hJeq : jOneOf (S ⊓ K) = jOneOf S := jOneOf_eq_of_le inf_le_left hJK
  ext r
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact R.mul_mem ha.2 hb.2
  · intro hr
    obtain ⟨k, hk, n, hn, rfl⟩ := exists_mul_mem_normalizer hR.le hR.two hR.syl hKR hKn r hr
    refine ⟨k, ⟨?_, hk.2⟩, n, ⟨?_, hn.2⟩, rfl⟩
    · have hkZ : k ∈ Subgroup.centralizer (omegaOneZ S : Set G) :=
        Subgroup.centralizer_le (s := (omegaOneZ S : Set G)) hZU hk.1
      exact mem_normalizer_of_mem_centralizer hkZ
    · have := Sec7.normalizer_le_normalizer_tripleOf (S ⊓ K) 1 hn.1
      rw [Sec7.tripleOf_one, hJeq] at this
      exact this

theorem fac_zero_one {R S : Subgroup G} (h : Hyp R S) :
    Fac R (jOf S) (omegaOneZ (jOneOf S)) := by
  refine fac_of_local (le_normalizer_jOf S) (le_normalizer_omegaOneZ_jOneOf S) ?_ R h
  intro R L H hR _ hLR hLn hH hHn hHmax hHc hLodd hRLS
  have hZ := omegaOneZ_jOneOf_le_of_local hR.solv hR.le hR.two hLR hLn hH hHn hHmax hHc hLodd
    hRLS
  exact fac_zero_one_of_local hR.not3 hR.le hR.two hLR hLn hH hHn hLodd hRLS hZ

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8

theorem th1J1Factorization : Th1J1Factorization := by
  intro G _ _ R S hRs h3 h5 hO hSR hS2 hSidx i hi
  have h : Th1J1.Hyp R S := ⟨hRs, h3, h5, hO, hSR, hS2, hSidx⟩
  rcases UniquenessMaximal.Sec7.fin_three_cases i with rfl | rfl | rfl
  · exact Th1J1.fac_zero_one h
  · exact absurd rfl hi
  · exact Th1J1.fac_two_one h

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8
