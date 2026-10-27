module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.LinBar
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinAux

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.AGLEmbedding Matrix
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le)
open CFSG.AGLEmbedding.ToralCensus CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb (exists_sl2_centralizer)

theorem torusFourCell_proof : TorusFourCell := by
  intro K _ _ _ n I p hn hp hp5 hK hpK hI hne hnb hcyc t ht htp htc
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpK0 : (p : K) ≠ 0 := natCast_ne_zero_of_odd_charTwo hpodd
  obtain ⟨i₀, hi₀1, hi₀n, hi₀⟩ := hnb
  have huniq : ∀ k, 0 < k → k < n → k ∉ I → k = i₀ := fun k hk0 hkn hk =>
    eq_of_not_mem_of_cyc hI hne hp hK hpK hcyc (by omega) hi₀n hi₀ hk0 hkn hk
  obtain ⟨k, k', hkk', hk'n, hk1, hk0, hk'1, hk'0⟩ : ∃ k k', k < k' ∧ k' < n ∧ k + 1 ≠ i₀ ∧
      k ≠ i₀ ∧ k' + 1 ≠ i₀ ∧ k' ≠ i₀ := by
    rcases (show i₀ = 1 ∨ i₀ = 2 ∨ 3 ≤ i₀ by omega) with h | h | h
    · exact ⟨2, 3, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 3, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hk := isConsecutiveCut_unit huniq (by omega : k < n) hk1 hk0
  have hk' := isConsecutiveCut_unit huniq hk'n hk'1 hk'0
  have hxI : t ∈ flagStabilizer n K I := perfectJoin_le _ ht
  have hxk := (gradedPerfectSL_holds K n I t ht k (k + 1) hk).2 (Or.inl (by omega))
  have hxk' := (gradedPerfectSL_holds K n I t ht k' (k' + 1) hk').2 (Or.inl (by omega))
  have hxp1 : t ^ p = 1 := by
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp htp
    have h1 := pow_apply_self_eq_one hxI hk (by omega) hxk p
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hr, scalar_apply, diagonal_apply_eq] at h1
    refine Subtype.ext ?_
    rw [← hr, h1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hkn : k < n := by omega
  set X := (t : Matrix (Fin n) (Fin n) K) with hX
  have hXp : X ^ p = 1 := LinearThreeKit.coe_pow_eq_one hxp1
  set j : Fin n := ⟨k, hkn⟩ with hj
  set j' : Fin n := ⟨k', hk'n⟩ with hj'
  set v := unitFixedVec p X j with hv
  set v' := unitFixedVec p X j' with hv'
  have hcoord : ∀ {m : ℕ} (hm : IsConsecutiveCut n I m (m + 1)) (hmn : m < n),
      cutBlock X m (m + 1) hm.2.1 = 1 → unitFixedVec p X ⟨m, hmn⟩ ⟨m, hmn⟩ = p := by
    intro m hm hmn hxm
    rw [unitFixedVec_apply_self, Finset.sum_congr rfl fun i _ =>
      pow_apply_self_eq_one hxI hm hmn hxm i, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hvj : v j = p := hcoord hk hkn hxk
  have hvj' : v' j' = p := hcoord hk' hk'n hxk'
  have hk'I : k' ∈ I := hk'.2.2.1.resolve_left (by omega)
  have hvF : v ∈ flagSpace n K k' := unitFixedVec_mem_flagSpace hxI hk'I p hkk'
  have hv0 : v ≠ 0 := fun h => hpK0 (by rw [← hvj, h, Pi.zero_apply])
  have hv'F : v' ∉ flagSpace n K k' := fun h =>
    hpK0 (by rw [← hvj', mem_flagSpace.mp h j' le_rfl])
  have hli := LinearThreeKit.linearIndependent_pair_of_notMem hvF hv0 hv'F
  exact exists_sl2_centralizer hpK0 hK (by omega) hxp1
    (LinearThreeKit.mulVec_fixedSum hXp _) (LinearThreeKit.mulVec_fixedSum hXp _) hli

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
