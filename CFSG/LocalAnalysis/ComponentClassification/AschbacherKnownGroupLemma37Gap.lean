module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma37

variable {G : Type*} [Group G]

theorem inv_conj_zpow_of_inverts {x y : G} (hxy : y * x * y⁻¹ = x⁻¹) (k : ℤ) :
    y⁻¹ * x ^ k * y = x ^ (-k) := by
  have h1 : y⁻¹ * x * y = x⁻¹ := by
    have : x = y⁻¹ * x⁻¹ * y := by
      rw [← hxy]
      group
    calc y⁻¹ * x * y = (y⁻¹ * x⁻¹ * y)⁻¹ := by group
      _ = x⁻¹ := by rw [← this]
  have h2 : (y⁻¹ * x * y⁻¹⁻¹) ^ k = y⁻¹ * x ^ k * y⁻¹⁻¹ := conj_zpow
  rw [inv_inv] at h2
  rw [← h2, h1, inv_zpow']

theorem gap_abelian_normal_cyclic [Finite G] {P S : Subgroup G} (hPp : IsPGroup 2 P)
    {t x y : G} (htP : t ∈ P) (ht2 : t ^ 2 = 1)
    (hcent : ∀ s ∈ S, s * t = t * s → s ∈ zpowers x) (hx4 : orderOf x = 4) (hyS : y ∈ S)
    (hy2 : y ^ 2 = x ^ 2) (hyt : t * y * t⁻¹ = y⁻¹) (hxy : y * x * y⁻¹ = x⁻¹)
    (B : Subgroup P) (hBS : B ≤ S.subgroupOf P) (hBn : B.Normal) (hBab : IsMulCommutative B) :
    IsCyclic B := by
  classical
  by_contra hBc
  obtain ⟨b₁, b₂, hb₁, hb₂, ho₁, ho₂, h₁, h₂, hne⟩ :=
    Lemma38.two_involutions_of_not_isCyclic hPp hBab hBc
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, (a : G) * b = b * a := fun a ha b hb =>
    congrArg (fun w : B => ((w : P) : G)) (isMulCommutative_iff.mp hBab ⟨a, ha⟩ ⟨b, hb⟩)
  set t' : P := ⟨t, htP⟩ with ht'
  have hconjB : ∀ b ∈ B, t' * b * t'⁻¹ ∈ B := fun b hb => hBn.conj_mem b hb t'
  have hx4' : x ^ (4 : ℕ) = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have key : ∀ b ∈ B, b ^ 2 = 1 → b ≠ 1 →
      (b : G) = x ^ 2 ∨ t * (b : G) * t⁻¹ = (b : G) * x ^ 2 := by
    intro b hb hb2 hb1
    have hb2G : (b : G) ^ 2 = 1 := by
      have := congrArg (fun w : P => (w : G)) hb2
      simpa using this
    have hbinv : (b : G)⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hb2G]
    set b' : P := t' * b * t'⁻¹ with hb'
    have hb'B : b' ∈ B := hconjB b hb
    have hb'G : (b' : G) = t * (b : G) * t⁻¹ := rfl
    have hbS : (b : G) ∈ S := hBS hb
    have hb'S : (b' : G) ∈ S := hBS hb'B
    set c := (b : G) * (b' : G) with hc
    have hcS : c ∈ S := S.mul_mem hbS hb'S
    have hcomm : (b : G) * b' = b' * b := hBcomm b hb b' hb'B
    have htt : t * t = 1 := by rw [← pow_two, ht2]
    have hct : c * t = t * c := by
      have hcomm' : (b : G) * (t * (b : G) * t) = (t * (b : G) * t) * b := by
        have := hcomm
        rw [hb'G, htinv] at this
        exact this
      have htc : t * c * t⁻¹ = c := by
        rw [hc, hb'G, htinv]
        calc t * ((b : G) * (t * (b : G) * t)) * t
            = (t * (b : G) * t) * ((b : G) * (t * t)) := by group
          _ = (t * (b : G) * t) * (b : G) := by rw [htt, mul_one]
          _ = (b : G) * (t * (b : G) * t) := hcomm'.symm
      calc c * t = (t * c * t⁻¹) * t := by rw [htc]
        _ = t * c := by group
    have hcx : c ∈ zpowers x := hcent c hcS hct
    have hc2 : c ^ 2 = 1 := by
      have hb'2 : (b' : G) ^ 2 = 1 := by
        rw [hb'G, conj_pow, hb2G]
        group
      calc c ^ 2 = (b : G) ^ 2 * (b' : G) ^ 2 := by
            rw [hc, pow_two, pow_two, pow_two]
            calc (b : G) * b' * ((b : G) * b') = (b : G) * ((b' : G) * b) * b' := by group
              _ = (b : G) * ((b : G) * b') * b' := by rw [hcomm]
              _ = (b : G) * b * (b' * b') := by group
        _ = 1 := by rw [hb2G, hb'2, one_mul]
    rcases mem_zpowers_sq_eq_one hx4 hcx hc2 with hc1 | hcr
    ·
      left
      have hbb' : (b' : G) = b := by
        have : (b' : G) = (b : G)⁻¹ := by
          rw [hc] at hc1
          exact eq_inv_of_mul_eq_one_right hc1
        rw [this, hbinv]
      have hbt : (b : G) * t = t * b := by
        calc (b : G) * t = (t * (b : G) * t⁻¹) * t := by rw [← hb'G, hbb']
          _ = t * b := by group
      have hbx := hcent b hbS hbt
      rcases mem_zpowers_sq_eq_one hx4 hbx hb2G with h | h
      · exact absurd (Subtype.ext h) hb1
      · exact h
    · right
      rw [← hb'G]
      calc (b' : G) = (b : G) * ((b : G) * b') := by
            rw [← mul_assoc, ← pow_two, hb2G, one_mul]
        _ = (b : G) * x ^ 2 := by rw [← hc, hcr]
  obtain ⟨e, heB, he2, he1, hex, het⟩ : ∃ e ∈ B, e ^ 2 = 1 ∧ e ≠ 1 ∧ (e : G) ≠ x ^ 2 ∧
      t * (e : G) * t⁻¹ = (e : G) * x ^ 2 := by
    by_cases hb₁x : (b₁ : G) = x ^ 2
    · have hb₂x : (b₂ : G) ≠ x ^ 2 := fun h => hne (Subtype.ext (hb₁x.trans h.symm))
      exact ⟨b₂, hb₂, ho₂, h₂, hb₂x, (key b₂ hb₂ ho₂ h₂).resolve_left hb₂x⟩
    · exact ⟨b₁, hb₁, ho₁, h₁, hb₁x, (key b₁ hb₁ ho₁ h₁).resolve_left hb₁x⟩
  have he2G : (e : G) ^ 2 = 1 := by
    have := congrArg (fun w : P => (w : G)) he2
    simpa using this
  have heS : (e : G) ∈ S := hBS heB
  have hex2 : x ^ 2 * (e : G) = (e : G) * x ^ 2 := by
    have he'B : t' * e * t'⁻¹ ∈ B := hconjB e heB
    have hcomm := hBcomm e heB _ he'B
    have he'G : ((t' * e * t'⁻¹ : P) : G) = (e : G) * x ^ 2 := het
    rw [he'G] at hcomm
    have h2 : x ^ 2 = (e : G) * x ^ 2 * e := by
      calc x ^ 2 = (e : G) * e * x ^ 2 := by rw [← pow_two, he2G, one_mul]
        _ = (e : G) * ((e : G) * x ^ 2) := by group
        _ = ((e : G) * x ^ 2) * e := hcomm
    calc x ^ 2 * (e : G) = ((e : G) * x ^ 2 * e) * e := by rw [← h2]
      _ = (e : G) * x ^ 2 * (e * e) := by group
      _ = (e : G) * x ^ 2 := by rw [← pow_two, he2G, mul_one]
  have hyet : (y * e) * t = t * (y * e) := by
    have : t * (y * (e : G)) * t⁻¹ = y * e := by
      calc t * (y * (e : G)) * t⁻¹ = (t * y * t⁻¹) * (t * (e : G) * t⁻¹) := by group
        _ = y⁻¹ * ((e : G) * x ^ 2) := by rw [hyt, het]
        _ = y⁻¹ * (x ^ 2 * e) := by rw [hex2]
        _ = y⁻¹ * (y ^ 2 * e) := by rw [hy2]
        _ = y * e := by group
    calc (y * e) * t = (t * (y * (e : G)) * t⁻¹) * t := by rw [this]
      _ = t * (y * e) := by group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hcent _ (S.mul_mem hyS heS) hyet)
  have he : (e : G) = y⁻¹ * x ^ k := by rw [hk]; group
  have hsq : (e : G) ^ 2 = x ^ (-2 : ℤ) := by
    rw [he, pow_two]
    have h1 : y⁻¹ * x ^ k * y = x ^ (-k) := inv_conj_zpow_of_inverts hxy k
    have hy2' : y⁻¹ * y⁻¹ = x ^ (-2 : ℤ) := by
      rw [← mul_inv_rev, ← pow_two, hy2, ← zpow_natCast, ← zpow_neg]
      rfl
    calc y⁻¹ * x ^ k * (y⁻¹ * x ^ k) = (y⁻¹ * x ^ k * y) * (y⁻¹ * y⁻¹) * x ^ k := by group
      _ = x ^ (-k) * x ^ (-2 : ℤ) * x ^ k := by rw [h1, hy2']
      _ = x ^ (-2 : ℤ) := by rw [← zpow_add, ← zpow_add]; ring_nf
  rw [he2G] at hsq
  have h2z : x ^ (2 : ℤ) = 1 := by
    have : (x ^ (2 : ℤ))⁻¹ = 1 := by rw [← zpow_neg]; exact hsq.symm
    exact inv_eq_one.1 this
  have : x ^ (2 : ℕ) = 1 := by exact_mod_cast h2z
  have hdvd := orderOf_dvd_of_pow_eq_one this
  rw [hx4] at hdvd
  norm_num at hdvd

end Lemma37

end CFSG.ComponentClassification.AschbacherKnownGroup
