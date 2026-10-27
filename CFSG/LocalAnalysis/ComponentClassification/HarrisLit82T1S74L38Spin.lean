module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74L38Quat
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74L38Four
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74L38Sylow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU2

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74.L38

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
open CFSG.OddStandard.Solomon75
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

omit h5 in
theorem spinZ_mem_of_isSylowIn {T : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))) :
    spinZ K ∈ T ∧ tSeven K ∈ T := by
  obtain ⟨hzz, hz1, hzc, htt, ht1, -, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  have hzo : orderOf (spinZ K) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hto : orderOf (tSeven K) = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  refine ⟨mem_of_isSylowIn hT ?_ hzo fun x _ => ?_, mem_of_isSylowIn hT ?_ hto fun x hx => ?_⟩
  · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc _).symm
  · exact (mem_center_iff.mp hzc x).symm
  · exact mem_centralizer_singleton_iff.mpr rfl
  · exact (mem_centralizer_singleton_iff.mp (hT.1 hx)).symm

omit h5 in
theorem spinZ_mul_tSeven_ne_one : spinZ K * tSeven K ≠ 1 := by
  obtain ⟨hzz, -, hzc, -, -, htc, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  intro h
  apply htc
  rw [(eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzz)]
  exact hzc

omit h5 in
theorem spinZ_mul_tSeven_mul_self : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
  obtain ⟨hzz, -, hzc, htt, -, -, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  rw [mul_assoc, ← mul_assoc (tSeven K), mem_center_iff.mp hzc (tSeven K), mul_assoc, htt,
    mul_one, hzz]

theorem conj_tSeven_eq {T P : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
    (hP : IsPGroup 2 P) (hTP : T ≤ P) (hnorm : ∀ x ∈ P, ∀ y ∈ T, x * y * x⁻¹ ∈ T)
    {x : spinGroup (quadOdd 3 K)} (hxP : x ∈ P) (hxT : x ∉ T) :
    x * tSeven K * x⁻¹ = spinZ K * tSeven K := by
  obtain ⟨-, -, hzc, -, ht1, htc, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  have htT := (spinZ_mem_of_isSylowIn hp hp2 hK hT).2
  have hyT : x * tSeven K * x⁻¹ ∈ T := hnorm x hxP _ htT
  have hyc : ∀ s ∈ T, x * tSeven K * x⁻¹ * s = s * (x * tSeven K * x⁻¹) := by
    intro s hs
    have hs' : x⁻¹ * s * x⁻¹⁻¹ ∈ T := hnorm x⁻¹ (inv_mem hxP) s hs
    rw [inv_inv] at hs'
    have hc : x⁻¹ * s * x * tSeven K = tSeven K * (x⁻¹ * s * x) :=
      mem_centralizer_singleton_iff.mp (hT.1 hs')
    calc x * tSeven K * x⁻¹ * s = x * (tSeven K * (x⁻¹ * s * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * s * x * tSeven K) * x⁻¹ := by rw [hc]
      _ = s * (x * tSeven K * x⁻¹) := by group
  rcases mem_center_sylow_centralizer hp hp2 hK h5 hT hyT hyc with h | h | h | h
  · exfalso
    apply ht1
    calc tSeven K = x⁻¹ * (x * tSeven K * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply htc
    have ht : tSeven K = spinZ K := by
      calc tSeven K = x⁻¹ * (x * tSeven K * x⁻¹) * x := by group
        _ = x⁻¹ * (spinZ K * x) := by rw [h, mul_assoc]
        _ = spinZ K := by rw [← mem_center_iff.mp hzc x, inv_mul_cancel_left]
    rw [ht]
    exact hzc
  · exfalso
    apply hxT
    refine mem_of_isSylowIn_of_le hT hP hTP hxP (mem_centralizer_singleton_iff.mpr ?_)
    calc x * tSeven K = x * tSeven K * x⁻¹ * x := by group
      _ = tSeven K * x := by rw [h]
  · exact h

theorem conj_spinJ {x : spinGroup (quadOdd 3 K)} (hxt : x * tSeven K * x⁻¹ = spinZ K * tSeven K) :
    (∀ a ∈ spinJ₁ K, x * a * x⁻¹ ∈ spinJ₁ K) ∧ (∀ b ∈ spinJ₂ K, x * b * x⁻¹ ∈ spinJ₃ K) := by
  obtain ⟨-, hz1, hzc, -, -, -, hzJ₁, htJ₂, hztJ₃, -⟩ := spinZ_facts hp hp2 hK
  have hzt1 := spinZ_mul_tSeven_ne_one hp hp2 hK
  have hC : (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map
      (MulAut.conj x).toMonoidHom = centralizer {tSeven K} := by
    rw [map_centralizer_singleton_mulEquiv (MulAut.conj x) (tSeven K), MulAut.conj_apply, hxt,
      centralizer_mul_of_mem_center hzc]
  have hcomp : ∀ J : Subgroup (spinGroup (quadOdd 3 K)),
      (J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) →
        IsTwoComponentIn (J.map (MulAut.conj x).toMonoidHom) (centralizer {tSeven K}) := by
    intro J hJ
    have h := L35.isTwoComponentIn_map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective (isTwoComponentIn_spinJ hp hp2 hK h5 hJ)
    rwa [hC] at h
  have hmem : ∀ (J : Subgroup (spinGroup (quadOdd 3 K))) (a : spinGroup (quadOdd 3 K)), a ∈ J →
      x * a * x⁻¹ ∈ J.map (MulAut.conj x).toMonoidHom :=
    fun J a ha => ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have hzx : x * spinZ K * x⁻¹ = spinZ K := by
    rw [mem_center_iff.mp hzc x, mul_inv_cancel_right]
  have hz' : spinZ K ∈ (spinJ₁ K).map (MulAut.conj x).toMonoidHom := by
    rw [← hzx]
    exact hmem _ _ hzJ₁
  have hJ1 : (spinJ₁ K).map (MulAut.conj x).toMonoidHom = spinJ₁ K := by
    rcases eq_spinJ_of_isTwoComponentIn hp hp2 hK h5 (hcomp _ (Or.inl rfl)) with h | h | h
    · exact h
    · exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₂ hp hp2 hK h5 hzJ₁ (h ▸ hz')) hz1
    · exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₃ hp hp2 hK h5 hzJ₁ (h ▸ hz')) hz1
  have hzt' : spinZ K * tSeven K ∈ (spinJ₂ K).map (MulAut.conj x).toMonoidHom := by
    rw [← hxt]
    exact hmem _ _ htJ₂
  have hJ2 : (spinJ₂ K).map (MulAut.conj x).toMonoidHom = spinJ₃ K := by
    rcases eq_spinJ_of_isTwoComponentIn hp hp2 hK h5 (hcomp _ (Or.inr (Or.inl rfl))) with
      h | h | h
    · exact absurd (eq_one_of_mem_spinJ₁_of_mem_spinJ₃ hp hp2 hK h5 (h ▸ hzt') hztJ₃) hzt1
    · exact absurd (eq_one_of_mem_spinJ₂_of_mem_spinJ₃ hp hp2 hK h5 (h ▸ hzt') hztJ₃) hzt1
    · exact h
  exact ⟨fun a ha => hJ1 ▸ hmem _ _ ha, fun b hb => hJ2 ▸ hmem _ _ hb⟩

theorem spinW_facts {T : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
    {u y v : spinGroup (quadOdd 3 K)} (hu : u ∈ T ⊓ spinJ₁ K) (huu : u * u = spinZ K)
    (hy : y ∈ spinJ₂ K) (hyy : y * y = tSeven K) (hv : v ∈ spinJ₃ K)
    (hvv : v * v = spinZ K * tSeven K) :
    u * y * v * (u * y * v) = 1 ∧ u * y * v ≠ 1 ∧ u * y * v ≠ spinZ K ∧ u * y * v ≠ tSeven K ∧
      u * y * v ≠ spinZ K * tSeven K := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 := four_le_card_spin hK h5
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  obtain ⟨hzz, hz1, hzc, -, -, -, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨l1, -, -⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, -, -⟩ := normal_spinJ (K := K) hp hp2 hK h5
  have hQ1 := isSylowIn_inf_of_normal hT l1 n1
  have huy : u * y = y * u := commute_spinJ₁_spinJ₂ hu.2 hy
  have huv : u * v = v * u := commute_spinJ₁_spinJ₃ hu.2 hv
  have hyv : y * v = v * y := commute_spinJ₂_spinJ₃ h4 hy hv
  refine ⟨?_, ?_⟩
  · rw [mul_mul_mul_mul_mul_of_commute huy huv hyv, huu, hyy, hvv]
    exact spinZ_mul_tSeven_mul_self hp hp2 hK
  have hne : ∀ e : spinGroup (quadOdd 3 K), (∀ q ∈ T ⊓ spinJ₁ K, q * e = e * q) →
      u * y * v ≠ e := by
    intro e he h
    have hcu : ∀ q ∈ T ⊓ spinJ₁ K, u * q = q * u := by
      intro q hq
      have h1 : q * (u * y * v) = u * y * v * q := by rw [h]; exact he q hq
      have hqy : q * y = y * q := commute_spinJ₁_spinJ₂ hq.2 hy
      have hqv : q * v = v * q := commute_spinJ₁_spinJ₃ hq.2 hv
      symm
      calc q * u = q * (u * y * v) * (y * v)⁻¹ := by group
        _ = u * y * v * q * (y * v)⁻¹ := by rw [h1]
        _ = u * y * (v * q) * (y * v)⁻¹ := by group
        _ = u * y * (q * v) * (y * v)⁻¹ := by rw [hqv]
        _ = u * (y * q) * v * (y * v)⁻¹ := by group
        _ = u * (q * y) * v * (y * v)⁻¹ := by rw [hqy]
        _ = u * q := by group
    obtain ⟨-, hcen⟩ := sylow_range_sl2_facts hodd (shortSeven K) injective_shortSeven hQ1
    rcases hcen u hu.2 hcu with h1 | h1
    · rw [h1, mul_one] at huu
      exact hz1 huu.symm
    · rw [h1, shortSeven_neg_one hQ] at huu
      exact hz1 (huu.symm.trans hzz)
  have htc : ∀ q ∈ T ⊓ spinJ₁ K, q * tSeven K = tSeven K * q := fun q hq =>
    mem_centralizer_singleton_iff.mp (hT.1 hq.1)
  have hzc' : ∀ q ∈ T ⊓ spinJ₁ K, q * spinZ K = spinZ K * q := fun q _ =>
    mem_center_iff.mp hzc q
  refine ⟨hne 1 fun q _ => by rw [mul_one, one_mul], hne _ hzc', hne _ htc, hne _ fun q hq => ?_⟩
  rw [← mul_assoc, hzc' q hq, mul_assoc, htc q hq, mul_assoc]

theorem exists_spinW {T : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
    {x : spinGroup (quadOdd 3 K)} (hxx : x * x = 1)
    (hxt : x * tSeven K * x⁻¹ = spinZ K * tSeven K) (hxT : ∀ y ∈ T, x * y * x⁻¹ ∈ T) :
    ∃ w ∈ T, w * w = 1 ∧ w * x = x * w ∧ w ≠ 1 ∧ w ≠ spinZ K ∧ w ≠ tSeven K ∧
      w ≠ spinZ K * tSeven K := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 := four_le_card_spin hK h5
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  obtain ⟨-, -, hzc, -, -, -, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨l1, l2, -⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, -⟩ := normal_spinJ (K := K) hp hp2 hK h5
  have hQ1 := isSylowIn_inf_of_normal hT l1 n1
  have hQ2 := isSylowIn_inf_of_normal hT l2 n2
  obtain ⟨hJ1x, hJ2x⟩ := conj_spinJ hp hp2 hK h5 hxt
  have hxQ1 : ∀ q ∈ T ⊓ spinJ₁ K, x * q * x⁻¹ ∈ T ⊓ spinJ₁ K := fun q hq =>
    ⟨hxT q hq.1, hJ1x q hq.2⟩
  have hxz : x * shortSeven K (-1) * x⁻¹ = shortSeven K (-1) := by
    rw [shortSeven_neg_one hQ, mem_center_iff.mp hzc x, mul_inv_cancel_right]
  obtain ⟨u, hu, huu, hux⟩ := exists_mul_self_conj_eq_or_inv hodd (shortSeven K)
    injective_shortSeven hQ1 hxx hxQ1 hxz
  rw [shortSeven_neg_one hQ] at huu
  obtain ⟨hprod2, -⟩ := sylow_range_sl2_facts hodd _
    (longSL2_injective _ fin3_zero_ne_one true true) hQ2
  obtain ⟨y, hy, -, -, hyy, -, -⟩ := hprod2 1 (one_mem _)
  have hv : x * y * x⁻¹ ∈ spinJ₃ K := hJ2x y hy.2
  have hvT : x * y * x⁻¹ ∈ T := hxT y hy.1
  have hvv : x * y * x⁻¹ * (x * y * x⁻¹) = spinZ K * tSeven K := by
    calc x * y * x⁻¹ * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
      _ = spinZ K * tSeven K := by rw [hyy]; exact hxt
  have hxv : x * (x * y * x⁻¹) * x⁻¹ = y := by
    calc x * (x * y * x⁻¹) * x⁻¹ = x * x * y * (x * x)⁻¹ := by group
      _ = y := by rw [hxx, one_mul, inv_one, mul_one]
  have hyv : y * (x * y * x⁻¹) = x * y * x⁻¹ * y := commute_spinJ₂_spinJ₃ h4 hy.2 hv
  rcases hux with hux | hux
  ·
    obtain ⟨hww, hw1, hwz, hwt, hwzt⟩ := spinW_facts hp hp2 hK h5 hT hu huu hy.2 hyy hv hvv
    refine ⟨u * y * (x * y * x⁻¹), mul_mem (mul_mem hu.1 hy.1) hvT, hww, ?_, hw1, hwz, hwt,
      hwzt⟩
    have hconj : x * (u * y * (x * y * x⁻¹)) * x⁻¹ = u * y * (x * y * x⁻¹) := by
      calc x * (u * y * (x * y * x⁻¹)) * x⁻¹ =
          x * u * x⁻¹ * (x * y * x⁻¹) * (x * (x * y * x⁻¹) * x⁻¹) := by group
        _ = u * (x * y * x⁻¹) * y := by rw [hux, hxv]
        _ = u * y * (x * y * x⁻¹) := by rw [mul_assoc, ← hyv, ← mul_assoc]
    calc u * y * (x * y * x⁻¹) * x = x * (u * y * (x * y * x⁻¹)) * x⁻¹ * x := by rw [hconj]
      _ = x * (u * y * (x * y * x⁻¹)) := by group
  ·
    have hv' : (x * y * x⁻¹)⁻¹ ∈ spinJ₃ K := inv_mem hv
    have hvv' : (x * y * x⁻¹)⁻¹ * (x * y * x⁻¹)⁻¹ = spinZ K * tSeven K := by
      rw [← _root_.mul_inv_rev, hvv]
      exact inv_eq_of_mul_eq_one_right (spinZ_mul_tSeven_mul_self hp hp2 hK)
    obtain ⟨hww, hw1, hwz, hwt, hwzt⟩ := spinW_facts hp hp2 hK h5 hT hu huu hy.2 hyy hv' hvv'
    refine ⟨u * y * (x * y * x⁻¹)⁻¹, mul_mem (mul_mem hu.1 hy.1) (inv_mem hvT), hww, ?_, hw1,
      hwz, hwt, hwzt⟩
    have huv : Commute u (x * y * x⁻¹) := commute_spinJ₁_spinJ₃ hu.2 hv
    have huy : Commute u y := commute_spinJ₁_spinJ₂ hu.2 hy.2
    have hconj : x * (u * y * (x * y * x⁻¹)⁻¹) * x⁻¹ = u * y * (x * y * x⁻¹)⁻¹ := by
      calc x * (u * y * (x * y * x⁻¹)⁻¹) * x⁻¹ =
          x * u * x⁻¹ * (x * y * x⁻¹) * (x * (x * y * x⁻¹) * x⁻¹)⁻¹ := by group
        _ = u⁻¹ * (x * y * x⁻¹) * y⁻¹ := by rw [hux, hxv]
        _ = (x * y * x⁻¹) * u⁻¹ * y⁻¹ := by rw [huv.inv_left.eq]
        _ = (x * y * x⁻¹) * (y⁻¹ * u⁻¹) := by rw [mul_assoc, huy.inv_inv.eq]
        _ = (u * y * (x * y * x⁻¹)⁻¹)⁻¹ := by
          rw [_root_.mul_inv_rev, inv_inv, _root_.mul_inv_rev]
        _ = u * y * (x * y * x⁻¹)⁻¹ := inv_eq_of_mul_eq_one_right hww
    calc u * y * (x * y * x⁻¹)⁻¹ * x = x * (u * y * (x * y * x⁻¹)⁻¹) * x⁻¹ * x := by rw [hconj]
      _ = x * (u * y * (x * y * x⁻¹)⁻¹) := by group

theorem exists_eight_le {T : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))) :
    ∃ E : Subgroup (spinGroup (quadOdd 3 K)), E ≤ T ∧ Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ 3 := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 := two_ne_zero_spin hp hp2 hK
  have := finite_spinSeven h2
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ (K := K) hp hp2 hK h5
  obtain ⟨hzT, htT⟩ := spinZ_mem_of_isSylowIn hp hp2 hK hT
  obtain ⟨hprod1, -⟩ := sylow_range_sl2_facts hodd (shortSeven K) injective_shortSeven
    (isSylowIn_inf_of_normal hT l1 n1)
  obtain ⟨u, hu, -, -, huu, -, -⟩ := hprod1 1 (one_mem _)
  rw [shortSeven_neg_one hQ] at huu
  obtain ⟨hprod2, -⟩ := sylow_range_sl2_facts hodd _
    (longSL2_injective _ fin3_zero_ne_one true true) (isSylowIn_inf_of_normal hT l2 n2)
  obtain ⟨y, hy, -, -, hyy, -, -⟩ := hprod2 1 (one_mem _)
  obtain ⟨hprod3, -⟩ := sylow_range_sl2_facts hodd _
    (longSL2_injective _ fin3_zero_ne_one true false) (isSylowIn_inf_of_normal hT l3 n3)
  obtain ⟨v, hv, -, -, hvv, -, -⟩ := hprod3 1 (one_mem _)
  rw [h3eq] at hvv
  obtain ⟨hww, hw1, hwz, hwt, hwzt⟩ := spinW_facts hp hp2 hK h5 hT hu huu hy.2 hyy hv.2 hvv
  have hwT : u * y * v ∈ T := mul_mem (mul_mem hu.1 hy.1) hv.1
  have hzt : Commute (spinZ K) (tSeven K) := (mem_center_iff.mp hzc (tSeven K)).symm
  have hzt1 : spinZ K ≠ tSeven K := fun h => htc (h ▸ hzc)
  have hwV : u * y * v ∉ four (spinZ K) (tSeven K) hzz htt hzt := by
    intro h
    rcases mem_four.mp h with h | h | h | h
    · exact hwzt h
    · exact hwz h
    · exact hwt h
    · exact hw1 h
  have hcomm : ∀ c ∈ four (spinZ K) (tSeven K) hzz htt hzt, Commute c (u * y * v) := by
    intro c hc
    refine (commute_of_mem_four (c := u * y * v) ?_ ?_ hc).symm
    · exact (mem_center_iff.mp hzc (u * y * v))
    · exact (mem_centralizer_singleton_iff.mp (hT.1 hwT))
  obtain ⟨hE, hEcard⟩ := isElemAbelian_sup_zpowers (isElemAbelian_four _ _ hzz htt hzt) hww hwV
    hcomm
  refine ⟨four (spinZ K) (tSeven K) hzz htt hzt ⊔ zpowers (u * y * v),
    sup_le (four_le hzT htT) (zpowers_le.mpr hwT), hE, ?_⟩
  rw [hEcard, card_four hzz htt hzt hz1 ht1 hzt1]
  norm_num

end CFSG.ComponentClassification.HarrisLit.T1.S74.L38
