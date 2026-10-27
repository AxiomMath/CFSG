module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InvCls
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46R
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G]

theorem eq_one_or_eq_of_isCyclic {Z : Subgroup G} (hZ : IsCyclic ↥Z) {a z : G} (haZ : a ∈ Z)
    (hzZ : z ∈ Z) (haa : a * a = 1) (ha1 : a ≠ 1) (hzz : z * z = 1) : z = 1 ∨ z = a := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hz1, hza⟩ := h
  have := Fintype.ofFinite ↥Z
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥Z) (n := 2) two_pos
  have hsub : ({1, ⟨a, haZ⟩, ⟨z, hzZ⟩} : Finset ↥Z) ⊆
      Finset.univ.filter (fun y : ↥Z => y ^ 2 = 1) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact haa)
    · exact Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hzz)
  have hne1 : (1 : ↥Z) ≠ ⟨a, haZ⟩ := fun h => ha1 (congrArg Subtype.val h).symm
  have hne2 : (1 : ↥Z) ≠ ⟨z, hzZ⟩ := fun h => hz1 (congrArg Subtype.val h).symm
  have hne3 : (⟨a, haZ⟩ : ↥Z) ≠ ⟨z, hzZ⟩ := fun h => hza (congrArg Subtype.val h).symm
  have hcard : ({1, ⟨a, haZ⟩, ⟨z, hzZ⟩} : Finset ↥Z).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]),
      Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]
  have h3 := Finset.card_le_card hsub
  omega

omit [Finite G] in
theorem exists_transvection {E H : Subgroup G} (hE : IsElemTwo E) (hHE : H ≤ E) {a w : G}
    (haH : a ∈ H) (hwE : w ∈ E) (hwH : w ∉ H) (hEH : E ≤ H ⊔ zpowers w) :
    ∃ τ : ↥E ≃* ↥E, (∀ y : ↥E, (y : G)⁻¹ * (τ y : G) ∈ zpowers a) ∧
      (τ ⟨w, hwE⟩ : G) = w * a := by
  classical
  have haE : a ∈ E := hHE haH
  have haa : a * a = 1 := hE.2 a haE
  have hw2 : w * w = 1 := hE.2 w hwE
  have hcw : ∀ e ∈ H, e * w = w * e := fun e he => hE.1 e (hHE he) w hwE
  have hoff : ∀ y : ↥E, (y : G) ∉ H → ∃ e ∈ H, (y : G) = e * w := fun y hy =>
    (mem_or_mul_of_mem_sup_zpowers hw2 hcw (hEH y.2)).resolve_left hy
  have hprod : ∀ y y' : ↥E, (y : G) ∉ H → (y' : G) ∉ H → (y : G) * y' ∈ H := by
    intro y y' hy hy'
    obtain ⟨e, he, hye⟩ := hoff y hy
    obtain ⟨e', he', hye'⟩ := hoff y' hy'
    rw [hye, hye', show e * w * (e' * w) = e * (w * e') * w by group, ← hcw e' he',
      show e * (e' * w) * w = e * e' * (w * w) by group, hw2, mul_one]
    exact mul_mem he he'
  have hmulH : ∀ y y' : ↥E, (y : G) ∈ H → (y' : G) ∉ H → (y : G) * y' ∉ H := fun y y' hy hy' h =>
    hy' (by have := mul_mem (inv_mem hy) h; rwa [inv_mul_cancel_left] at this)
  have hmulH' : ∀ y y' : ↥E, (y : G) ∉ H → (y' : G) ∈ H → (y : G) * y' ∉ H := fun y y' hy hy' h =>
    hy (by have := mul_mem h (inv_mem hy'); rwa [mul_inv_cancel_right] at this)
  let ae : ↥E := ⟨a, haE⟩
  have hcomm : ∀ u v : ↥E, u * v = v * u := fun u v => Subtype.ext (hE.1 _ u.2 _ v.2)
  let f : ↥E → ↥E := fun y => if (y : G) ∈ H then y else y * ae
  have hmul : ∀ y y' : ↥E, f (y * y') = f y * f y' := by
    intro y y'
    simp only [f, Subgroup.coe_mul]
    by_cases hy : (y : G) ∈ H <;> by_cases hy' : (y' : G) ∈ H
    · simp only [hy, hy', mul_mem hy hy', ↓reduceIte]
    · simp only [hy, hy', hmulH y y' hy hy', ↓reduceIte, mul_assoc]
    · simp only [hy, hy', hmulH' y y' hy hy', ↓reduceIte]
      rw [mul_assoc, mul_assoc, hcomm y' ae]
    · simp only [hy, hy', hprod y y' hy hy', ↓reduceIte]
      rw [show y * ae * (y' * ae) = y * y' * (ae * ae) by
          rw [mul_assoc y ae, ← mul_assoc ae y', hcomm ae y']; group,
        show ae * ae = 1 from Subtype.ext haa, mul_one]
  let φ : ↥E →* ↥E :=
    { toFun := f
      map_one' := by simp only [f, OneMemClass.coe_one, one_mem, ↓reduceIte]
      map_mul' := hmul }
  have hφφ : ∀ y, φ (φ y) = y := by
    intro y
    show f (f y) = y
    by_cases hy : (y : G) ∈ H
    · simp only [f, hy, ↓reduceIte]
    · have hya : ((y * ae : ↥E) : G) ∉ H := hmulH' y ae hy haH
      simp only [f, hy, ↓reduceIte]
      simp only [hya, ↓reduceIte]
      rw [mul_assoc, show ae * ae = 1 from Subtype.ext haa, mul_one]
  refine ⟨MulEquiv.ofBijective φ ⟨fun y y' h => by rw [← hφφ y, h, hφφ],
    fun y => ⟨φ y, hφφ y⟩⟩, fun y => ?_, ?_⟩
  · show (y : G)⁻¹ * (f y : G) ∈ zpowers a
    by_cases hy : (y : G) ∈ H
    · simp only [f, hy, ↓reduceIte, inv_mul_cancel]
      exact one_mem _
    · simp only [f, hy, ↓reduceIte, Subgroup.coe_mul]
      rw [inv_mul_cancel_left]
      exact mem_zpowers a
  · show (f ⟨w, hwE⟩ : G) = w * a
    simp only [f, hwH, ↓reduceIte, Subgroup.coe_mul]
    rfl

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem l34CyclicInvolutionClassFact_of_facts
    (hCE : L34CyclicCentralEightFact) (hTr : L34EightTransvectionFact) :
    L34CyclicInvolutionClassFact := by
  intro G _ _ J P hJ hL hP hcyc hc4 u huJ v hvJ huu hvv huZ hvZ
  have hP2 : IsPGroup 2 P := GrS4.isPGroup_of_isSylowTwoIn hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P ⊓ zStarIn J)) 2
    (by rw [hc4]; norm_num)
  set a : G := (a' : G) with ha
  have haZ : a ∈ P ⊓ zStarIn J := a'.2
  have haa : a * a = 1 := by
    have h := pow_orderOf_eq_one a'
    rw [ha', pow_two] at h
    exact congrArg Subtype.val h
  have ha1 : a ≠ 1 := fun h => by
    have : a' = 1 := Subtype.ext h
    rw [this, orderOf_one] at ha'
    exact absurd ha' (by norm_num)
  obtain ⟨B, hBP, hB8, hBZ, -, -, -⟩ := hCE G J P a hJ hL hP hcyc hc4 haZ haa ha1
  have haB : a ∈ B := (show zpowers a ≤ B from hBZ ▸ inf_le_left) (mem_zpowers a)
  have hcard2 : Nat.card ↥(zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
  obtain ⟨w, hwB, hwa⟩ : ∃ w ∈ B, w ∉ zpowers a := by
    by_contra hno
    push Not at hno
    have h1 := card_le_of_le (show B ≤ zpowers a from hno)
    rw [hB8.2, hcard2] at h1
    omega
  have hwZ : w ∉ zStarIn J := fun h => hwa (hBZ ▸ mem_inf.mpr ⟨hwB, h⟩)
  have hww : w * w = 1 := hB8.1.2 w hwB
  have hcza : ∀ e ∈ zpowers a, e * w = w * e := fun e he =>
    hB8.1.1 e ((zpowers_le.mpr haB) he) w hwB
  obtain ⟨hV, hVc⟩ := GrS4.isElemTwo_sup_zpowers (isElemTwo_zpowers haa) hww hwa hcza
  obtain ⟨w', hw'B, hw'V⟩ : ∃ w' ∈ B, w' ∉ zpowers a ⊔ zpowers w := by
    by_contra hno
    push Not at hno
    have h1 := card_le_of_le (show B ≤ zpowers a ⊔ zpowers w from hno)
    rw [hB8.2, hVc, hcard2] at h1
    omega
  have hw'w' : w' * w' = 1 := hB8.1.2 w' hw'B
  have hw'a : w' ∉ zpowers a := fun h => hw'V (mem_sup_left h)
  obtain ⟨hH, hHc⟩ := GrS4.isElemTwo_sup_zpowers (isElemTwo_zpowers haa) hw'w' hw'a
    fun e he => hB8.1.1 e ((zpowers_le.mpr haB) he) w' hw'B
  set H : Subgroup G := zpowers a ⊔ zpowers w' with hHdef
  have hHB : H ≤ B := sup_le (zpowers_le.mpr haB) (zpowers_le.mpr hw'B)
  have hwH : w ∉ H := by
    intro h
    rcases GrS4.mem_or_mul_of_mem_sup_zpowers hw'w'
      (fun e he => hB8.1.1 e ((zpowers_le.mpr haB) he) w' hw'B) h with h' | ⟨e, he, hwe⟩
    · exact hwa h'
    · apply hw'V
      have : w' = e⁻¹ * w := by rw [hwe]; group
      rw [this]
      exact mul_mem (mem_sup_left (inv_mem he)) (mem_sup_right (mem_zpowers w))
  have hEH : B ≤ H ⊔ zpowers w := by
    obtain ⟨hHw, hHwc⟩ := GrS4.isElemTwo_sup_zpowers hH hww hwH
      fun e he => hB8.1.1 e (hHB he) w hwB
    have hle : H ⊔ zpowers w ≤ B := sup_le hHB (zpowers_le.mpr hwB)
    have heq := eq_of_le_of_card_ge hle (by rw [hB8.2, hHwc, hHc, hcard2])
    rw [heq]
  obtain ⟨τ, hτ, hτw⟩ := GrS4.exists_transvection hB8.1 hHB (mem_sup_left (mem_zpowers a)) hwB
    hwH hEH
  obtain ⟨p, hp, hpw⟩ := hTr G J P B a hJ hL hP hcyc hc4 hBP hB8 hBZ τ hτ
  have hwwa : p⁻¹ * w * p = w * a := by rw [← hτw]; exact hpw ⟨w, hwB⟩
  have hpJ : p ∈ J := hP.1 (mem_inf.mp hp).1
  have hwP : w ∈ P := hBP hwB
  have hwJ : w ∈ J := hP.1 hwP
  have key : ∀ t ∈ J, t * t = 1 → t ∉ zStarIn J → ∃ m ∈ J, m⁻¹ * t * m = w := by
    intro t htJ htt htZ
    obtain ⟨j, hj⟩ := GrS4.exists_conj_jq_mem_center hL htJ hwJ htt hww htZ hwZ
    obtain ⟨z, hzP, hzJ, hzj⟩ := exists_mem_of_mem_center hP hj
    have hzZ : z ∈ P ⊓ zStarIn J := mem_inf.mpr ⟨hzP, (mem_zStarIn_iff hzJ).mpr (hzj ▸ hj)⟩
    set t' : G := (j : G)⁻¹ * t * j with ht'
    have ht'J : t' ∈ J := mul_mem (mul_mem (inv_mem j.2) htJ) j.2
    have hwzP : w * z ∈ P := mul_mem hwP hzP
    have hjq : jq J ⟨t', ht'J⟩ = jq J ⟨w * z, hP.1 hwzP⟩ := by
      have e1 : (⟨w * z, hP.1 hwzP⟩ : J) = ⟨w, hwJ⟩ * ⟨z, hzJ⟩ := rfl
      have e2 : (⟨t', ht'J⟩ : J) = j⁻¹ * ⟨t, htJ⟩ * j := rfl
      rw [e1, map_mul, hzj, e2, mul_inv_cancel_left]
    have hzK : z ∈ coreActionKernel J := by
      have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
      have := (mem_inf.mp hzZ).2
      rw [h] at this
      exact (mem_inf.mp this).2
    have hwz : w * z = z * w :=
      (GrS4.mul_comm_of_mem_coreActionKernel hP2 hzP hzK hwP hwJ).symm
    have ht't' : t' * t' = 1 := by
      rw [ht', show (j : G)⁻¹ * t * j * ((j : G)⁻¹ * t * j) = (j : G)⁻¹ * (t * t) * j by group,
        htt]
      group
    have hwzwz : w * z * (w * z) = 1 := by
      refine eq_one_of_jq_eq_one hP.1 hP2 (mul_mem hwzP hwzP) ?_
      have e1 : (⟨w * z * (w * z), hP.1 (mul_mem hwzP hwzP)⟩ : J) =
          ⟨w * z, hP.1 hwzP⟩ * ⟨w * z, hP.1 hwzP⟩ := rfl
      have e2 : (⟨t', ht'J⟩ : J) * ⟨t', ht'J⟩ = 1 := Subtype.ext ht't'
      rw [e1, map_mul, ← hjq, ← map_mul, e2, map_one]
    have hzz : z * z = 1 := by
      calc z * z = w * w * (z * z) := by rw [hww, one_mul]
        _ = w * z * (w * z) := by rw [mul_assoc w z, ← mul_assoc z w z, ← hwz]; group
        _ = 1 := hwzwz
    have hO : w * z * t' ∈ oddIn J := by
      have hdi : (w * z)⁻¹ = w * z := inv_eq_of_mul_eq_one_right hwzwz
      have h1 : jq J ⟨w * z * t', mul_mem (hP.1 hwzP) ht'J⟩ = 1 := by
        have e1 : (⟨w * z * t', mul_mem (hP.1 hwzP) ht'J⟩ : J) =
            (⟨w * z, hP.1 hwzP⟩ : J)⁻¹ * ⟨t', ht'J⟩ := Subtype.ext (by
          show w * z * t' = (w * z)⁻¹ * t'
          rw [hdi])
        rw [e1, map_mul, map_inv, hjq, inv_mul_cancel]
      exact (mem_oddIn_iff _).mpr h1
    obtain ⟨k, hk⟩ := CFSG.ClassicalInvolution.Asc77.T3Core.exists_conj_of_mul_mem_odd hwzwz ht't'
      ((odd_card_map_pPrimeCore J).of_dvd_nat ((oddIn J).orderOf_dvd_natCard hO))
    set o : G := (w * z * t') ^ k with ho
    have hoJ : o ∈ J := map_subtype_le _ (pow_mem hO k)
    have hm : ((j : G) * o)⁻¹ * t * ((j : G) * o) = w * z := by
      calc ((j : G) * o)⁻¹ * t * ((j : G) * o) = o⁻¹ * t' * o := by rw [ht']; group
        _ = o⁻¹ * (o * (w * z) * o⁻¹) * o := by rw [← hk]
        _ = w * z := by group
    have hjoJ : (j : G) * o ∈ J := mul_mem j.2 hoJ
    rcases GrS4.eq_one_or_eq_of_isCyclic hcyc haZ hzZ haa ha1 hzz with rfl | rfl
    · exact ⟨(j : G) * o, hjoJ, by rw [hm, mul_one]⟩
    · refine ⟨(j : G) * o * p⁻¹, mul_mem hjoJ (inv_mem hpJ), ?_⟩
      calc ((j : G) * o * p⁻¹)⁻¹ * t * ((j : G) * o * p⁻¹) =
          p * (((j : G) * o)⁻¹ * t * ((j : G) * o)) * p⁻¹ := by group
        _ = p * (p⁻¹ * w * p) * p⁻¹ := by rw [hm, hwwa]
        _ = w := by group
  obtain ⟨m₁, hm₁J, h1⟩ := key u huJ huu huZ
  obtain ⟨m₂, hm₂J, h2⟩ := key v hvJ hvv hvZ
  refine ⟨m₁ * m₂⁻¹, mul_mem hm₁J (inv_mem hm₂J), ?_⟩
  calc (m₁ * m₂⁻¹)⁻¹ * u * (m₁ * m₂⁻¹) = m₂ * (m₁⁻¹ * u * m₁) * m₂⁻¹ := by group
    _ = m₂ * (m₂⁻¹ * v * m₂) * m₂⁻¹ := by rw [h1, h2]
    _ = v := by group

end CFSG.ComponentClassification.GrSLit
