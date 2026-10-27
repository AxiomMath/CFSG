module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB8
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Fusion
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB7
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem false_of_sq_witness
    {W K T : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K)) (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K)))
    (hTsyl : IsSylowTwoIn T (normalizer (W : Set G))) (hTidx : ¬ 2 ∣ T.index)
    (hTK : IsSylowTwoIn (T ⊓ K) K) (hTZ : T ⊓ zStarIn K = ⊥)
    (hWT : ∀ F : Subgroup G, F ≤ T → IsEightGroup F →
      (∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) → wGroup F = W)
    {t : G} (htT : t ∈ T) (htK : t ∉ normalizer (K : Set G))
    (hr2 : ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t)
    (hnorm : ∀ y ∈ T, y ∉ normalizer (K : Set G) → t * y * t⁻¹ ∉ normalizer (K : Set G))
    {a : G} (haK : a ∈ coreActionKernel K) (haext : IsExtremalIn T a)
    (hE3 : ∀ y ∈ K ⊔ conjugate K t ⊔ oddIn (normalizer (W : Set G)), y * y = 1 → y ≠ 1 →
      ∃ g ∈ normalizer (W : Set G), g⁻¹ * y * g = a ∨
        (g⁻¹ * y * g)⁻¹ * a * (t⁻¹ * a * t) ∈ oddIn (normalizer (W : Set G)))
    (hE4 : ∀ w ∈ T ⊓ normalizer (K : Set G), w * w ∈ K ⊔ conjugate K t)
    (hE5 : ∀ v ∈ T, v ∉ normalizer (K : Set G) → v * v ∉ withKernel K)
    {v g : G} (hvT : v ∈ T) (hvK : v ∉ normalizer (K : Set G)) (hvv : v * v ≠ 1)
    (hvvvv : v * v * (v * v) = 1) (hg : g⁻¹ * v * g ∈ T ⊓ normalizer (K : Set G))
    (hwit : ∃ F ≤ T ⊓ centralizer ({v * v} : Set G), IsEightGroup F ∧
      ∃ w ∈ T ⊓ centralizer ({v * v} : Set G), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧ w ∉ F) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM := hTsyl.1
  have htM := hTM htT
  have hKt : conjugate K t ≠ K := fun e => htK (mem_normalizer_of_conjugate_eq e)
  have hKtK : conjugate K t ≤ coreActionKernel K :=
    HeSN.le_coreActionKernel_of_ne hKM (conjugate_le_of_mem hKM htM) hKc
      (isPComponent_conjugate_subgroupOf htM hKc) (Ne.symm hKt)
  have hKKt : K ≤ coreActionKernel (conjugate K t) :=
    HeSN.le_coreActionKernel_of_ne (conjugate_le_of_mem hKM htM) hKM
      (isPComponent_conjugate_subgroupOf htM hKc) hKc hKt
  have hKper : ⁅K, K⁆ = K := commutator_eq_of_isPComponent hKM hKc
  obtain ⟨F, hFT, hF, w, hwT, hww, hwF, hwn⟩ := hwit
  have hfus : ∀ c : G, IsExtremalIn T (c⁻¹ * (v * v) * c) →
      c⁻¹ * (v * v) * c ∉ withKernel K := by
    intro c hc
    obtain ⟨m, hm, hcm⟩ := exists_conj_of_witness hT2 hWT hc hFT hF hwT hww hwF hwn
    rw [hcm]
    exact conj_sq_not_mem_withKernel htT hr2 hE5 hvT hvK (hnorm v hvT hvK) hm
  set y : G := g⁻¹ * (v * v) * g with hy
  have hyKK : y ∈ K ⊔ conjugate K t := by
    rw [show y = g⁻¹ * v * g * (g⁻¹ * v * g) by rw [hy]; group]
    exact hE4 _ hg
  have hy2 : y * y = 1 := by
    rw [hy, show g⁻¹ * (v * v) * g * (g⁻¹ * (v * v) * g) = g⁻¹ * (v * v * (v * v)) * g by group,
      hvvvv]
    group
  have hy1 : y ≠ 1 := fun h => hvv (by
    rw [show v * v = g * y * g⁻¹ by rw [hy]; group, h]
    group)
  obtain ⟨m, hm, hma | hmb⟩ := hE3 y (mem_sup_left hyKK) hy2 hy1
  ·
    have e : (g * m)⁻¹ * (v * v) * (g * m) = a := by
      rw [← hma, hy]
      group
    exact hfus (g * m) (by rw [e]; exact haext) (by rw [e]; exact mem_sup_right haK)
  ·
    obtain ⟨z₀, hz₀, hz₀2, hz₀c⟩ := GrS4.exists_center_involution_of_normal
      (hT2.to_le inf_le_left : IsPGroup 2 ↥(T ⊓ conjugate K t)) le_rfl le_normalizer
      (inf_conjugate_ne_bot hKM hKc hTsyl htM)
    have hz₀T := (mem_inf.mp hz₀).1
    have hz₀Kt := (mem_inf.mp hz₀).2
    set z₁ : G := t * z₀ * t⁻¹ with hz₁
    have hz₁K : z₁ ∈ K := mem_conjugate_iff.mp hz₀Kt
    have hz₁T : z₁ ∈ T := mul_mem (mul_mem htT hz₀T) (inv_mem htT)
    have hz₁c : ∀ e ∈ T ⊓ K, e * z₁ = z₁ * e := by
      intro e he
      have h1 : t⁻¹ * e * t ∈ T ⊓ conjugate K t := mem_inf.mpr
        ⟨mul_mem (mul_mem (inv_mem htT) (mem_inf.mp he).1) htT, by
          rw [mem_conjugate_iff, show t * (t⁻¹ * e * t) * t⁻¹ = e by group]
          exact (mem_inf.mp he).2⟩
      have h2 := hz₀c _ h1
      calc e * z₁ = t * (t⁻¹ * e * t * z₀) * t⁻¹ := by rw [hz₁]; group
        _ = t * (z₀ * (t⁻¹ * e * t)) * t⁻¹ := by rw [h2]
        _ = z₁ * e := by rw [hz₁]; group
    have hcz₀ : ∀ e ∈ T ⊓ K, e * z₀ = z₀ * e := by
      intro e he
      have h1 := commute_conj_one hKM hKc hT2 hTM he (mem_inf.mpr ⟨hz₁T, hz₁K⟩) htT hKt
      rw [show t⁻¹ * z₁ * t = z₀ by rw [hz₁]; group] at h1
      exact h1.eq
    have hodd1 : ∀ x ∈ T, x ∈ K → x ∈ coreActionKernel K → x = 1 := fun x hxT hxK hxC => by
      have hb := eq_bot_of_le_two_group_of_le_odd hT2 hKC (zpowers_le.mpr hxT)
        (zpowers_le.mpr (mem_inf.mpr ⟨hxK, hxC⟩))
      have h1 : x ∈ zpowers x := mem_zpowers _
      rwa [hb, mem_bot] at h1
    have hz₀1 : z₀ ≠ 1 := fun h => by
      rw [h, orderOf_one] at hz₀2
      exact absurd hz₀2 (by norm_num)
    have hz₁1 : z₁ ≠ 1 := fun h => hz₀1 (by
      rw [show z₀ = t⁻¹ * z₁ * t by rw [hz₁]; group, h]
      group)
    have hz₀z₀ : z₀ * z₀ = 1 := by rw [← pow_two, ← hz₀2, pow_orderOf_eq_one]
    have hz₁z₁ : z₁ * z₁ = 1 := by
      rw [hz₁, show t * z₀ * t⁻¹ * (t * z₀ * t⁻¹) = t * (z₀ * z₀) * t⁻¹ by group, hz₀z₀]
      group
    have hz₀z₁ : z₀ * z₁ = z₁ * z₀ := (hcz₀ z₁ (mem_inf.mpr ⟨hz₁T, hz₁K⟩)).symm
    set y₀ : G := z₀ * z₁ with hy₀
    have hy₀2 : y₀ * y₀ = 1 := by
      rw [hy₀, show z₀ * z₁ * (z₀ * z₁) = z₀ * (z₁ * z₀) * z₁ by group, ← hz₀z₁,
        show z₀ * (z₀ * z₁) * z₁ = z₀ * z₀ * (z₁ * z₁) by group, hz₀z₀, hz₁z₁, one_mul]
    have hy₀1 : y₀ ≠ 1 := fun h => by
      have h1 : z₀ = z₁⁻¹ := eq_inv_of_mul_eq_one_left h
      exact hz₀1 (hodd1 z₀ hz₀T (h1 ▸ inv_mem hz₁K) (hKtK hz₀Kt))
    have hy₀KK : y₀ ∈ K ⊔ conjugate K t := mul_mem (mem_sup_right hz₀Kt) (mem_sup_left hz₁K)
    obtain ⟨m₀, hm₀, hm₀a | hm₀b⟩ := hE3 y₀ (mem_sup_left hy₀KK) hy₀2 hy₀1
    ·
      exfalso
      have h1 : y₀ ∈ coreActionKernel (conjugate K m₀⁻¹) := by
        rw [FooteLit.mem_coreActionKernel_conjugate_iff, inv_inv, hm₀a]
        exact haK
      rcases hr2 m₀⁻¹ (inv_mem hm₀) with h2 | h2
      · rw [h2] at h1
        refine hz₁1 (hodd1 z₁ hz₁T hz₁K ?_)
        rw [show z₁ = z₀⁻¹ * y₀ by rw [hy₀]; group]
        exact mul_mem (inv_mem (hKtK hz₀Kt)) h1
      · rw [h2] at h1
        have h3 : z₀ ∈ coreActionKernel (conjugate K t) := by
          rw [show z₀ = y₀ * z₁⁻¹ by rw [hy₀]; group]
          exact mul_mem h1 (inv_mem (hKKt hz₁K))
        exact hz₁1 (hodd1 z₁ hz₁T hz₁K (FooteLit.mem_coreActionKernel_conjugate_iff.mp h3))
    ·
      set z : G := m⁻¹ * y * m with hz
      set z' : G := m₀⁻¹ * y₀ * m₀ with hz'
      have hzz : z * z = 1 := by
        rw [hz, show m⁻¹ * y * m * (m⁻¹ * y * m) = m⁻¹ * (y * y) * m by group, hy2]
        group
      have hz'z' : z' * z' = 1 := by
        rw [hz', show m₀⁻¹ * y₀ * m₀ * (m₀⁻¹ * y₀ * m₀) = m₀⁻¹ * (y₀ * y₀) * m₀ by group, hy₀2]
        group
      have hd : z⁻¹ * z' ∈ oddIn M := by
        have h1 := mul_mem hmb (inv_mem hm₀b)
        rwa [show z⁻¹ * a * (t⁻¹ * a * t) * (z'⁻¹ * a * (t⁻¹ * a * t))⁻¹ = z⁻¹ * z' by group]
          at h1
      have hdodd : Odd (orderOf (z⁻¹ * z')) :=
        (UnbalancedCorr.odd_card_map_pPrimeCore M).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hd)
      obtain ⟨k, hk⟩ := CatFactsL4U4.exists_conj_of_mul_odd hzz hz'z' hdodd
      set d : G := (z⁻¹ * z') ^ k with hd'
      set c : G := g * m * d⁻¹ * m₀⁻¹ with hc
      have hyc : y₀ = c⁻¹ * (v * v) * c := by
        have e1 : y₀ = m₀ * z' * m₀⁻¹ := by rw [hz']; group
        rw [e1, ← hk, hz, hy, hc]
        group
      have hTKZ : T ⊓ K ⊓ zStarIn K = ⊥ := eq_bot_iff.mpr fun x hx => by
        have h1 : x ∈ T ⊓ zStarIn K :=
          mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).1, (mem_inf.mp hx).2⟩
        rwa [hTZ] at h1
      obtain ⟨E, -, hET, hE, hEc, -⟩ := L34Facts.l34ElementaryCenterFact G K (T ⊓ K) hKper hKL
        hTK fun x hx => by
          rw [hTKZ, mem_bot] at hx
          rw [hx, one_mul]
      rw [hTKZ, card_bot, mul_one] at hEc
      have hEy₀ : E ≤ T ⊓ centralizer ({y₀} : Set G) := fun e he => by
        have heTK := hET he
        refine mem_inf.mpr ⟨(mem_inf.mp heTK).1, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [hy₀]
        calc e * (z₀ * z₁) = z₀ * (e * z₁) := by rw [← mul_assoc, hcz₀ e heTK, mul_assoc]
          _ = z₀ * z₁ * e := by rw [hz₁c e heTK, hz₁]; group
      obtain ⟨E₈, hE₈E, hE₈c⟩ := exists_le_card_eight hE.isPGroup (by omega)
      obtain ⟨e₀, he₀E, he₀n⟩ : ∃ e₀ ∈ E, e₀ ∉ E₈ := by
        by_contra h
        push Not at h
        have := card_le_of_le (h : E ≤ E₈)
        omega
      obtain ⟨c', hc'⟩ := exists_isExtremalIn_conj hT2 hTidx (b := y₀)
        ⟨1, by rw [pow_one]; exact orderOf_eq_prime (by rw [pow_two]; exact hy₀2) hy₀1⟩
      obtain ⟨m₁, hm₁, hm₁e⟩ := exists_conj_of_witness hT2 hWT hc' (hE₈E.trans hEy₀)
        ⟨hE.mono hE₈E, hE₈c⟩ (hEy₀ he₀E) (hE.2 e₀ he₀E) (fun e he => hE.1 e₀ he₀E e (hE₈E he))
        he₀n
      have e2 : (c * c')⁻¹ * (v * v) * (c * c') = c'⁻¹ * y₀ * c' := by
        rw [hyc]
        group
      apply hfus (c * c') (by rw [e2]; exact hc')
      rw [e2, hm₁e]
      exact conj_mem_withKernel_of_mem_sup hr2 htM hKtK hy₀KK hm₁

end CFSG.ComponentClassification.GrSLit.KSw
