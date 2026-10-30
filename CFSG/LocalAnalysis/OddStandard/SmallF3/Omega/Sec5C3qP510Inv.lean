module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510T
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510E2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {Q₁ Q₂ : Subgroup G} {a b : G}

theorem sec5p510_t_not_mem_zpowers (h : Sec510Ctx G t L S z r ρ B A φ) : t ∉ zpowers z := by
  intro ht
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.pocket.1).mp ht with h1 | h1
  · have h2 := h.involution
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · exact h.tnz 1 (by rw [inv_one, one_mul, mul_one, h1])

theorem sec5p510_tz_not_mem_zpowers (h : Sec510Ctx G t L S z r ρ B A φ) :
    t * z ∉ zpowers z := by
  intro hmem
  have ht : t ∈ zpowers z := by
    have := mul_mem hmem (inv_mem (Subgroup.mem_zpowers z))
    rwa [mul_inv_cancel_right] at this
  exact sec5p510_t_not_mem_zpowers h ht

private theorem sec5p510_inv_mul_mem_E {E R : Subgroup G} (hrel : E.relIndex R = 2) {x y : G}
    (hx : x ∈ R) (hy : y ∈ R) (hxE : x ∉ E) (hyE : y ∉ E) : x⁻¹ * y ∈ E := by
  obtain ⟨c, -, hall⟩ := Subgroup.relIndex_eq_two_iff'.mp hrel
  have h1 : c * x ∈ E := (xor_iff_iff_not.mp (hall x hx)).mpr hxE
  have h2 : c * y ∈ E := (xor_iff_iff_not.mp (hall y hy)).mpr hyE
  have h3 := mul_mem (inv_mem h1) h2
  have e : (c * x)⁻¹ * (c * y) = x⁻¹ * y := by group
  rwa [e] at h3

private theorem sec5p510_sq_t_mul {c : G} (htc : t * c = c * t) (htt : t * t = 1) :
    (t * c) * (t * c) = c * c := by
  calc (t * c) * (t * c) = t * (c * t) * c := by simp only [mul_assoc]
    _ = t * (t * c) * c := by rw [htc]
    _ = (t * t) * (c * c) := by simp only [mul_assoc]
    _ = c * c := by rw [htt, one_mul]

theorem sec5p510_exists_d0 {R E : Subgroup G} {x : G} (hxT : x ∈ sec5p510_T t z R)
    (hxE : x ∉ E) :
    ∃ d₀ ∈ conjClassIn (centralizer ({z} : Set G)) t, d₀ ∈ R ∧ d₀ ∉ E := by
  by_contra hcon
  push Not at hcon
  have hTE : sec5p510_T t z R ≤ E := (Subgroup.closure_le _).mpr fun y hy => hcon y hy.1 hy.2
  exact hxE (hTE hxT)

theorem sec5p510_T_invol (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6) (h4 : Asc82FactReflCentQ6)
    (hCS : S ⊓ centralizer (L : Set G) = zpowers t)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) {x : G}
    (hxT : x ∈ sec5p510_T t z (sec5p510_R S Q₁ Q₂)) (hx2 : x * x ∈ zpowers z)
    (hxz : x ∉ zpowers z) :
    ∃ y ∈ conjClassIn (centralizer ({z} : Set G)) t, x = y ∨ x = y * z := by
  obtain ⟨hac, hbc⟩ := sec5p510_ab_mem_conj h hab
  have hzz : z * z = 1 := sec5p510_A_sq h (sec5p510_z_mem_A h)
  by_cases hxE : x ∈ sec5p510_E t a b
  · obtain ⟨y, hy', hxy⟩ := sec5p510_E_eq_mul_z h hab hxE
    rcases hy' with hy' | hy' | hy' | hy'
    · exfalso
      apply hxz
      rcases hxy with h1 | h1
      · rw [h1, hy']
        exact one_mem _
      · rw [h1, hy', one_mul]
        exact Subgroup.mem_zpowers z
    · exact ⟨y, by rw [hy']; exact sec5p510_t_mem_conj t z, hxy⟩
    · exact ⟨y, by rw [hy']; exact hac, hxy⟩
    · exact ⟨y, by rw [hy']; exact hbc, hxy⟩
  · have hxR : x ∈ sec5p510_R S Q₁ Q₂ := sec5p510_T_le_R _ _ _ hxT
    have hrel : (sec5p510_E t a b).relIndex (sec5p510_R S Q₁ Q₂) = 2 := by
      rcases sec5p510_R_cases hy hD h4 hCS h hQ hab with hRE | ⟨-, hrel⟩
      · exact absurd (by rw [← hRE]; exact hxR) hxE
      · exact hrel
    obtain ⟨d₀, hd₀c, hd₀R, hd₀E⟩ := sec5p510_exists_d0 hxT hxE
    have htt : t * t = 1 := sec5p510_A_sq h (sec5p510_t_mem_A h)
    have hd0 : d₀ * d₀ = 1 := by
      obtain ⟨m, -, hm⟩ := hd₀c
      rw [hm]
      calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have hd0inv : d₀⁻¹ = d₀ := inv_eq_of_mul_eq_one_right hd0
    obtain ⟨hswa, hswb⟩ := sec5p510_swap hy hD h4 hCS h hQ hab hrel hd₀R hd₀E
    rw [hd0inv] at hswa hswb
    have hdt : d₀ * t = t * d₀ :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 hd₀R.1)
    have hab' : a * b = b * a := sec5p510_A_comm h (hab.a_mem_A h) (hab.b_mem_A h)
    have hta : t * a = a * t := sec5p510_A_comm h (sec5p510_t_mem_A h) (hab.a_mem_A h)
    have htb : t * b = b * t := sec5p510_A_comm h (sec5p510_t_mem_A h) (hab.b_mem_A h)
    have hy0 : a * d₀ * a⁻¹ = d₀ * (t * z) := by
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (sec5p510_A_sq h (hab.a_mem_A h))
      have had : a * d₀ = d₀ * b := by
        calc a * d₀ = (d₀ * b * d₀) * d₀ := by rw [hswb]
          _ = d₀ * b * (d₀ * d₀) := by simp only [mul_assoc]
          _ = d₀ * b := by rw [hd0, mul_one]
      calc a * d₀ * a⁻¹ = (a * d₀) * a := by rw [hai]
        _ = d₀ * b * a := by rw [had]
        _ = d₀ * (b * a) := by rw [mul_assoc]
        _ = d₀ * (a * b) := by rw [hab']
        _ = d₀ * (t * z) := by rw [hab.ab_eq h]
    have hy0c : a * d₀ * a⁻¹ ∈ conjClassIn (centralizer ({z} : Set G)) t :=
      sec5p510_conj_mem_conj hd₀c (sec5p510_a_mem_H h hab)
    have hca : (d₀ * a) * (d₀ * a) = t * z := by
      calc (d₀ * a) * (d₀ * a) = (d₀ * a * d₀) * a := by simp only [mul_assoc]
        _ = a * b := by rw [hswa, ← hab']
        _ = t * z := hab.ab_eq h
    have hcb : (d₀ * b) * (d₀ * b) = t * z := by
      calc (d₀ * b) * (d₀ * b) = (d₀ * b * d₀) * b := by simp only [mul_assoc]
        _ = a * b := by rw [hswb]
        _ = t * z := hab.ab_eq h
    have htca : t * (d₀ * a) = (d₀ * a) * t := by
      calc t * (d₀ * a) = (t * d₀) * a := by rw [mul_assoc]
        _ = (d₀ * t) * a := by rw [hdt]
        _ = d₀ * (t * a) := by rw [mul_assoc]
        _ = d₀ * (a * t) := by rw [hta]
        _ = (d₀ * a) * t := by rw [mul_assoc]
    have htcb : t * (d₀ * b) = (d₀ * b) * t := by
      calc t * (d₀ * b) = (t * d₀) * b := by rw [mul_assoc]
        _ = (d₀ * t) * b := by rw [hdt]
        _ = d₀ * (t * b) := by rw [mul_assoc]
        _ = d₀ * (b * t) := by rw [htb]
        _ = (d₀ * b) * t := by rw [mul_assoc]
    have hxe : x = d₀ * (d₀ * x) := by rw [← mul_assoc, hd0, one_mul]
    have he : d₀ * x ∈ sec5p510_E t a b := by
      have := sec5p510_inv_mul_mem_E hrel hd₀R hxR hd₀E hxE
      rwa [hd0inv] at this
    rcases (sec5p510_mem_E_iff h hab).mp he with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    ·
      refine ⟨d₀, hd₀c, Or.inl ?_⟩
      rw [hxe, h1, mul_one]
    ·
      refine ⟨a * d₀ * a⁻¹, hy0c, Or.inr ?_⟩
      rw [hy0, hxe, h1]
      simp only [mul_assoc, hzz, mul_one]
    ·
      exfalso
      have hx : x = d₀ * a := by rw [hxe, h1]
      apply sec5p510_tz_not_mem_zpowers h
      rw [← hca, ← hx]
      exact hx2
    · exfalso
      have hx : x = d₀ * b := by rw [hxe, h1]
      apply sec5p510_tz_not_mem_zpowers h
      rw [← hcb, ← hx]
      exact hx2
    · exfalso
      have hx : x = t * (d₀ * a) := by
        rw [hxe, h1]
        calc d₀ * (t * a) = (d₀ * t) * a := by rw [mul_assoc]
          _ = (t * d₀) * a := by rw [hdt]
          _ = t * (d₀ * a) := by rw [mul_assoc]
      apply sec5p510_tz_not_mem_zpowers h
      rw [← hca, ← sec5p510_sq_t_mul htca htt, ← hx]
      exact hx2
    · exfalso
      have hx : x = t * (d₀ * b) := by
        rw [hxe, h1]
        calc d₀ * (t * b) = (d₀ * t) * b := by rw [mul_assoc]
          _ = (t * d₀) * b := by rw [hdt]
          _ = t * (d₀ * b) := by rw [mul_assoc]
      apply sec5p510_tz_not_mem_zpowers h
      rw [← hcb, ← sec5p510_sq_t_mul htcb htt, ← hx]
      exact hx2
    ·
      refine ⟨a * d₀ * a⁻¹, hy0c, Or.inl ?_⟩
      rw [hy0, hxe, h1, hab.ab_eq h]
    ·
      refine ⟨d₀, hd₀c, Or.inr ?_⟩
      rw [hxe, h1, hab.prod]

end CFSG.OddStandard.SmallF3.Omega
