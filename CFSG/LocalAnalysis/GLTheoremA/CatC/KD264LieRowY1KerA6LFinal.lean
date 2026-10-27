module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

theorem galois_no_quad_root_L6 (q : TauCeti.PrimePower) (h3 : 3 ∣ q.card + 1) :
    ∀ x : GaloisField q.p q.exponent, x ^ 2 + x + 1 ≠ 0 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [CFSG.Models.card_galoisField q, TauCeti.PrimePower.card_def q]
  have hQpos : 0 < q.card := by
    rw [TauCeti.PrimePower.card_def q]
    exact pow_pos q.prime_p.pos _
  have hnd3 : ¬ 3 ∣ q.card := by
    intro hd
    omega
  have hnd3' : ¬ 3 ∣ q.card - 1 := by
    intro hd
    omega
  have h3K : (3 : GaloisField q.p q.exponent) ≠ 0 := by
    intro h
    have hcast : ((3 : ℕ) : GaloisField q.p q.exponent) = 0 := by exact_mod_cast h
    have hpd : q.p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p 3).mp hcast
    have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp hpd
    apply hnd3
    rw [TauCeti.PrimePower.card_def q, hp3]
    exact dvd_pow_self 3 q.exponent_pos.ne'
  intro x hx
  have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  haveI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
  have hfc : Fintype.card (GaloisField q.p q.exponent) = q.card := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have hferm : x ^ (q.card - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one x hx0
    rwa [hfc] at h
  have hg : x ^ (Nat.gcd 3 (q.card - 1)) = 1 := pow_gcd_eq_one.mpr ⟨hx3, hferm⟩
  have hcop : Nat.gcd 3 (q.card - 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd3'
  rw [hcop, pow_one] at hg
  apply h3K
  rw [hg] at hx
  linear_combination hx

theorem KD264Y1KerA6_holds : KD264Y1KerA6 := by
  unfold KD264Y1KerA6 KD264Y1Kernel
  intro d _hfin _hns _hk2 _hk3 hP E hE hc
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl, h3⟩ := hP
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 5 q hd1
  apply kerConcl_of_equiv e E
  apply KA6L.kerConcl_PSL6 (GaloisField q.p q.exponent) (galois_no_quad_root_L6 q h3)
  · exact isElemAbelian_map e hE
  · rw [Subgroup.card_map_of_injective e.injective, hc]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
