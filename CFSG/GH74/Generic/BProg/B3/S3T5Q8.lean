module

public import CFSG.GH74.Generic.QuaternionCentral
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Quat

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5

namespace W

open CFSG CFSG.GH74 Subgroup
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices (quaternionLift quaternionLift_a
  quaternionLift_xa quaternion_center)

variable {Q Y : Type*} [Group Q] [Group Y]

theorem mul_self_mem_center {ι : Q →* Y} (hι : Function.Injective ι) {d : Y} {ℓ : Q}
    (hd : d * d = 1) (hact : ∀ q, d * ι q * d⁻¹ = ι (ℓ * q * ℓ⁻¹)) : ℓ * ℓ ∈ center Q := by
  rw [Subgroup.mem_center_iff]
  intro q
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have h1 : ι q = ι (ℓ * ℓ * q * (ℓ * ℓ)⁻¹) := by
    calc ι q = d * (d * ι q * d⁻¹) * d⁻¹ := by
          rw [hdinv, show d * (d * ι q * d) * d = (d * d) * ι q * (d * d) by group, hd]
          group
      _ = ι (ℓ * (ℓ * q * ℓ⁻¹) * ℓ⁻¹) := by rw [hact, hact]
      _ = ι (ℓ * ℓ * q * (ℓ * ℓ)⁻¹) := by group
  have h2 := hι h1
  calc q * (ℓ * ℓ) = ℓ * ℓ * q * (ℓ * ℓ)⁻¹ * (ℓ * ℓ) := by rw [← h2]
    _ = ℓ * ℓ * q := by group

theorem commutator_mem_center {ι : Q →* Y} (hι : Function.Injective ι) {d₁ d₂ : Y} {ℓ₁ ℓ₂ : Q}
    (h12 : d₁ * d₂ = d₂ * d₁) (hact₁ : ∀ q, d₁ * ι q * d₁⁻¹ = ι (ℓ₁ * q * ℓ₁⁻¹))
    (hact₂ : ∀ q, d₂ * ι q * d₂⁻¹ = ι (ℓ₂ * q * ℓ₂⁻¹)) :
    (ℓ₂ * ℓ₁)⁻¹ * (ℓ₁ * ℓ₂) ∈ center Q := by
  rw [Subgroup.mem_center_iff]
  intro q
  have h1 : ι (ℓ₁ * ℓ₂ * q * (ℓ₁ * ℓ₂)⁻¹) = ι (ℓ₂ * ℓ₁ * q * (ℓ₂ * ℓ₁)⁻¹) := by
    calc ι (ℓ₁ * ℓ₂ * q * (ℓ₁ * ℓ₂)⁻¹) = ι (ℓ₁ * (ℓ₂ * q * ℓ₂⁻¹) * ℓ₁⁻¹) := by group
      _ = (d₁ * d₂) * ι q * (d₁ * d₂)⁻¹ := by rw [← hact₁, ← hact₂]; group
      _ = (d₂ * d₁) * ι q * (d₂ * d₁)⁻¹ := by rw [h12]
      _ = ι (ℓ₂ * (ℓ₁ * q * ℓ₁⁻¹) * ℓ₂⁻¹) := by rw [← hact₂, ← hact₁]; group
      _ = ι (ℓ₂ * ℓ₁ * q * (ℓ₂ * ℓ₁)⁻¹) := by group
  have h2 := hι h1
  calc q * ((ℓ₂ * ℓ₁)⁻¹ * (ℓ₁ * ℓ₂))
      = (ℓ₂ * ℓ₁)⁻¹ * (ℓ₂ * ℓ₁ * q * (ℓ₂ * ℓ₁)⁻¹) * (ℓ₁ * ℓ₂) := by group
    _ = (ℓ₂ * ℓ₁)⁻¹ * (ℓ₁ * ℓ₂ * q * (ℓ₁ * ℓ₂)⁻¹) * (ℓ₁ * ℓ₂) := by rw [h2]
    _ = (ℓ₂ * ℓ₁)⁻¹ * (ℓ₁ * ℓ₂) * q := by group

theorem mem_center_of_comm {ι : Q →* Y} (hι : Function.Injective ι) {q : Q}
    (h : ∀ q' : Q, ι q' * ι q = ι q * ι q') : q ∈ center Q := by
  rw [Subgroup.mem_center_iff]
  intro q'
  apply hι
  rw [map_mul, map_mul]
  exact h q'

theorem mem_range_of_inner_four [Finite Y] (hY : Gen4 Y) (ι : Q →* Y)
    (hι : Function.Injective ι) {z : Q} (hz1 : z ≠ 1) (hzc : z ∈ center Q)
    (hinv : ∀ q : Q, q * q = 1 → q = 1 ∨ q = z) (hcen : ∀ q ∈ center Q, q = 1 ∨ q = z)
    {d₁ d₂ : Y} (hd₁ : d₁ * d₁ = 1) (hd₂ : d₂ * d₂ = 1) (h12 : d₁ * d₂ = d₂ * d₁) {ℓ₁ ℓ₂ : Q}
    (hact₁ : ∀ q, d₁ * ι q * d₁⁻¹ = ι (ℓ₁ * q * ℓ₁⁻¹))
    (hact₂ : ∀ q, d₂ * ι q * d₂⁻¹ = ι (ℓ₂ * q * ℓ₂⁻¹))
    (hn₁ : ℓ₁ ∉ center Q) (hn₂ : ℓ₂ ∉ center Q) (hn₁₂ : ℓ₁ * ℓ₂ ∉ center Q)
    {β : Y} (hβ : ∀ y : Y, y * β = β * y) (hβ2 : β * β = 1) : β ∈ ι.range := by
  classical
  have hzz : z * z = 1 := by
    rcases hcen (z * z) (mul_mem hzc hzc) with h | h
    · exact h
    · exact absurd (mul_left_cancel (h.trans (mul_one z).symm)) hz1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzcomm : ∀ q : Q, q * z = z * q := Subgroup.mem_center_iff.mp hzc
  have hsq : ∀ {d : Y} {ℓ : Q}, d * d = 1 → (∀ q, d * ι q * d⁻¹ = ι (ℓ * q * ℓ⁻¹)) →
      ℓ ∉ center Q → ℓ * ℓ = z := by
    intro d ℓ hd hact hn
    rcases hcen _ (mul_self_mem_center hι hd hact) with h | h
    · exfalso
      rcases hinv ℓ h with h' | h'
      · exact hn (h' ▸ one_mem _)
      · exact hn (h' ▸ hzc)
    · exact h
  have hs₁ : ℓ₁ * ℓ₁ = z := hsq hd₁ hact₁ hn₁
  have hs₂ : ℓ₂ * ℓ₂ = z := hsq hd₂ hact₂ hn₂
  have hw : ℓ₁ * ℓ₂ = ℓ₂ * ℓ₁ * z := by
    rcases hcen _ (commutator_mem_center hι h12 hact₁ hact₂) with h | h
    · exfalso
      have hc : ℓ₁ * ℓ₂ = ℓ₂ * ℓ₁ := by
        calc ℓ₁ * ℓ₂ = (ℓ₂ * ℓ₁) * ((ℓ₂ * ℓ₁)⁻¹ * (ℓ₁ * ℓ₂)) := by group
          _ = ℓ₂ * ℓ₁ := by rw [h, mul_one]
      have hsq12 : ℓ₁ * ℓ₂ * (ℓ₁ * ℓ₂) = 1 := by
        calc ℓ₁ * ℓ₂ * (ℓ₁ * ℓ₂) = ℓ₁ * (ℓ₂ * ℓ₁) * ℓ₂ := by group
          _ = ℓ₁ * (ℓ₁ * ℓ₂) * ℓ₂ := by rw [hc]
          _ = (ℓ₁ * ℓ₁) * (ℓ₂ * ℓ₂) := by group
          _ = 1 := by rw [hs₁, hs₂, hzz]
      rcases hinv _ hsq12 with h' | h'
      · exact hn₁₂ (h' ▸ one_mem _)
      · exact hn₁₂ (h' ▸ hzc)
    · calc ℓ₁ * ℓ₂ = (ℓ₂ * ℓ₁) * ((ℓ₂ * ℓ₁)⁻¹ * (ℓ₁ * ℓ₂)) := by group
        _ = ℓ₂ * ℓ₁ * z := by rw [h]
  set A : Y := ι ℓ₁ with hA
  set Bq : Y := ι ℓ₂ with hBq
  set Zz : Y := ι z with hZz
  have hAA : A * A = Zz := by rw [hA, hZz, ← map_mul, hs₁]
  have hBB : Bq * Bq = Zz := by rw [hBq, hZz, ← map_mul, hs₂]
  have hZZ : Zz * Zz = 1 := by rw [hZz, ← map_mul, hzz, map_one]
  have hAB : A * Bq = Bq * A * Zz := by rw [hA, hBq, hZz, ← map_mul, ← map_mul, ← map_mul, hw]
  have hZ1 : Zz ≠ 1 := fun h => hz1 (hι (h.trans (map_one ι).symm))
  have hact₁' : ∀ q, d₁ * ι q * d₁⁻¹ = A * ι q * A⁻¹ := fun q => by
    rw [hact₁, map_mul, map_mul, map_inv]
  have hact₂' : ∀ q, d₂ * ι q * d₂⁻¹ = Bq * ι q * Bq⁻¹ := fun q => by
    rw [hact₂, map_mul, map_mul, map_inv]
  have hZc : ∀ q : Q, ι q * Zz = Zz * ι q := fun q => by
    rw [hZz, ← map_mul, ← map_mul, hzcomm q]
  have hdZ : ∀ {d : Y} {y : Y}, (∀ q, d * ι q * d⁻¹ = y * ι q * y⁻¹) → y * Zz = Zz * y →
      d * Zz = Zz * d := by
    intro d y hact hyZ
    have h1 := hact z
    rw [← hZz] at h1
    calc d * Zz = (d * Zz * d⁻¹) * d := by group
      _ = (y * Zz * y⁻¹) * d := by rw [h1]
      _ = Zz * d := by rw [hyZ]; group
  have hAZ : A * Zz = Zz * A := hZc ℓ₁
  have hBZ : Bq * Zz = Zz * Bq := hZc ℓ₂
  have hd₁Z : d₁ * Zz = Zz * d₁ := hdZ hact₁' hAZ
  have hd₂Z : d₂ * Zz = Zz * d₂ := hdZ hact₂' hBZ
  have hZinv : Zz⁻¹ = Zz := inv_eq_of_mul_eq_one_right hZZ
  have hd₁A : d₁ * A = A * d₁ := by
    have h1 := hact₁' ℓ₁
    calc d₁ * A = (d₁ * A * d₁⁻¹) * d₁ := by group
      _ = (A * A * A⁻¹) * d₁ := by rw [hA, h1]
      _ = A * d₁ := by group
  have hd₂B : d₂ * Bq = Bq * d₂ := by
    have h1 := hact₂' ℓ₂
    calc d₂ * Bq = (d₂ * Bq * d₂⁻¹) * d₂ := by group
      _ = (Bq * Bq * Bq⁻¹) * d₂ := by rw [hBq, h1]
      _ = Bq * d₂ := by group
  have hd₁B : d₁ * Bq⁻¹ = A * Bq⁻¹ * A⁻¹ * d₁ := by
    have h1 := hact₁' ℓ₂⁻¹
    rw [map_inv] at h1
    calc d₁ * Bq⁻¹ = (d₁ * Bq⁻¹ * d₁⁻¹) * d₁ := by group
      _ = A * Bq⁻¹ * A⁻¹ * d₁ := by rw [hBq, h1]
  have hd₂A : d₂ * A⁻¹ = Bq * A⁻¹ * Bq⁻¹ * d₂ := by
    have h1 := hact₂' ℓ₁⁻¹
    rw [map_inv] at h1
    calc d₂ * A⁻¹ = (d₂ * A⁻¹ * d₂⁻¹) * d₂ := by group
      _ = Bq * A⁻¹ * Bq⁻¹ * d₂ := by rw [hA, h1]
  have hcq : ∀ {d y : Y}, (∀ q, d * ι q * d⁻¹ = y * ι q * y⁻¹) →
      ∀ q, (y⁻¹ * d) * ι q = ι q * (y⁻¹ * d) := by
    intro d y hact q
    calc y⁻¹ * d * ι q = y⁻¹ * (d * ι q * d⁻¹) * d := by group
      _ = y⁻¹ * (y * ι q * y⁻¹) * d := by rw [hact]
      _ = ι q * (y⁻¹ * d) := by group
  set c₁ : Y := A⁻¹ * d₁ with hc₁
  set c₂ : Y := Bq⁻¹ * d₂ with hc₂
  have hc₁q : ∀ q, c₁ * ι q = ι q * c₁ := hcq hact₁'
  have hc₂q : ∀ q, c₂ * ι q = ι q * c₂ := hcq hact₂'
  have hc₁c₁ : c₁ * c₁ = Zz := by
    calc c₁ * c₁ = A⁻¹ * (d₁ * A⁻¹) * d₁ := by rw [hc₁]; group
      _ = A⁻¹ * (A⁻¹ * d₁) * d₁ := by rw [(show Commute d₁ A from hd₁A).inv_right.eq]
      _ = (A * A)⁻¹ * (d₁ * d₁) := by group
      _ = Zz := by rw [hAA, hd₁, mul_one, hZinv]
  have hc₂c₂ : c₂ * c₂ = Zz := by
    calc c₂ * c₂ = Bq⁻¹ * (d₂ * Bq⁻¹) * d₂ := by rw [hc₂]; group
      _ = Bq⁻¹ * (Bq⁻¹ * d₂) * d₂ := by rw [(show Commute d₂ Bq from hd₂B).inv_right.eq]
      _ = (Bq * Bq)⁻¹ * (d₂ * d₂) := by group
      _ = Zz := by rw [hBB, hd₂, mul_one, hZinv]
  have hc12 : c₁ * c₂ = Bq⁻¹ * A⁻¹ * (d₁ * d₂) := by
    calc c₁ * c₂ = A⁻¹ * (d₁ * Bq⁻¹) * d₂ := by rw [hc₁, hc₂]; group
      _ = A⁻¹ * (A * Bq⁻¹ * A⁻¹ * d₁) * d₂ := by rw [hd₁B]
      _ = Bq⁻¹ * A⁻¹ * (d₁ * d₂) := by group
  have hc21 : c₂ * c₁ = A⁻¹ * Bq⁻¹ * (d₂ * d₁) := by
    calc c₂ * c₁ = Bq⁻¹ * (d₂ * A⁻¹) * d₁ := by rw [hc₁, hc₂]; group
      _ = Bq⁻¹ * (Bq * A⁻¹ * Bq⁻¹ * d₂) * d₁ := by rw [hd₂A]
      _ = A⁻¹ * Bq⁻¹ * (d₂ * d₁) := by group
  have hinvAB : Bq⁻¹ * A⁻¹ = Zz * (A⁻¹ * Bq⁻¹) := by
    calc Bq⁻¹ * A⁻¹ = (A * Bq)⁻¹ := (mul_inv_rev A Bq).symm
      _ = (Bq * A * Zz)⁻¹ := by rw [hAB]
      _ = Zz⁻¹ * (A⁻¹ * Bq⁻¹) := by group
      _ = Zz * (A⁻¹ * Bq⁻¹) := by rw [hZinv]
  have hc2c1 : c₂ * c₁ = Zz * (c₁ * c₂) := by
    rw [hc21, hc12, hinvAB, h12]
    calc A⁻¹ * Bq⁻¹ * (d₂ * d₁) = (Zz * Zz) * (A⁻¹ * Bq⁻¹) * (d₂ * d₁) := by
          rw [hZZ, one_mul]
      _ = Zz * (Zz * (A⁻¹ * Bq⁻¹) * (d₂ * d₁)) := by group
  have hZc₁ : Zz * c₁ = c₁ * Zz := (hc₁q z).symm
  have hc₁inv : c₁⁻¹ = Zz * c₁ := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← hZc₁, mul_assoc, hc₁c₁, hZZ]
  have hA4 : A ^ 4 = 1 := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 by rw [← pow_add], pow_two, hAA, hZZ]
  have hAinv : A⁻¹ = A * Zz := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hAA, hZZ]
  have hBA : Bq * A * Bq⁻¹ = A⁻¹ := by
    have h1 : Bq * A = A * Bq * Zz := by
      calc Bq * A = Bq * A * Zz * Zz := by rw [mul_assoc (Bq * A), hZZ, mul_one]
        _ = A * Bq * Zz := by rw [← hAB]
    rw [h1, hAinv]
    calc A * Bq * Zz * Bq⁻¹ = A * (Bq * Zz) * Bq⁻¹ := by group
      _ = A * (Zz * Bq) * Bq⁻¹ := by rw [hBZ]
      _ = A * Zz := by group
  have hB2 : Bq ^ 2 = A ^ 2 := by rw [pow_two, pow_two, hAA, hBB]
  have hc4 : c₁ ^ 4 = 1 := by
    rw [show c₁ ^ 4 = c₁ ^ 2 * c₁ ^ 2 by rw [← pow_add], pow_two, hc₁c₁, hZZ]
  have hcyx : c₂ * c₁ * c₂⁻¹ = c₁⁻¹ := by
    rw [hc2c1, hc₁inv]
    group
  have hcy2 : c₂ ^ 2 = c₁ ^ 2 := by rw [pow_two, pow_two, hc₁c₁, hc₂c₂]
  set ψ₁ := quaternionLift hA4 hBA hB2 with hψ₁
  set ψ₂ := quaternionLift hc4 hcyx hcy2 with hψ₂
  have ha2 : (2 : ZMod 4).val = 2 := rfl
  have hψ₁a2 : ψ₁ (QuaternionGroup.a 2) = Zz := by
    rw [hψ₁, quaternionLift_a, ha2, pow_two, hAA]
  have hψ₂a2 : ψ₂ (QuaternionGroup.a 2) = Zz := by
    rw [hψ₂, quaternionLift_a, ha2, pow_two, hc₁c₁]
  have hψ₁inj : Function.Injective ψ₁ :=
    CFSG.ComponentClassification.CatLeafProof.injective_of_quaternion_a_two ψ₁
      (by rw [hψ₁a2]; exact hZ1)
  have hψ₂inj : Function.Injective ψ₂ :=
    CFSG.ComponentClassification.CatLeafProof.injective_of_quaternion_a_two ψ₂
      (by rw [hψ₂a2]; exact hZ1)
  have hrange : ∀ g, ψ₁ g ∈ ι.range := by
    rintro (k | k)
    · exact ⟨ℓ₁ ^ k.val, by rw [hψ₁, quaternionLift_a, map_pow]⟩
    · exact ⟨ℓ₂ * ℓ₁ ^ k.val, by rw [hψ₁, quaternionLift_xa, map_mul, map_pow]⟩
  have hcent : ∀ h q, ψ₂ h * ι q = ι q * ψ₂ h := by
    rintro (k | k) q
    · rw [hψ₂, quaternionLift_a]
      exact ((show Commute c₁ (ι q) from hc₁q q).pow_left _).eq
    · rw [hψ₂, quaternionLift_xa]
      exact ((show Commute c₂ (ι q) from hc₂q q).mul_left
        ((show Commute c₁ (ι q) from hc₁q q).pow_left _)).eq
  have hcomm : ∀ g h, Commute (ψ₁ g) (ψ₂ h) := by
    intro g h
    obtain ⟨q, hq⟩ := hrange g
    rw [← hq]
    exact (hcent h q).symm
  set φ := MonoidHom.noncommCoprod ψ₁ ψ₂ hcomm with hφdef
  have hφapp : ∀ g h, φ (g, h) = ψ₁ g * ψ₂ h := fun g h => rfl
  have hφ : ∀ gh, φ gh = 1 → gh = 1 ∨ gh = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
    rintro ⟨g, h⟩ hgh
    rw [hφapp] at hgh
    obtain ⟨q, hq⟩ := hrange g
    have h2 : ψ₂ h = ι q⁻¹ := by
      rw [map_inv, hq]
      exact eq_inv_of_mul_eq_one_right hgh
    have hqc : q⁻¹ ∈ center Q := mem_center_of_comm hι (fun q' => by
      rw [← h2]
      exact (hcent h q').symm)
    rcases hcen _ hqc with h1 | h1
    · have hq1 : q = 1 := inv_eq_one.mp h1
      have hg : g = 1 := hψ₁inj (by rw [← hq, hq1, map_one, map_one])
      have hh : h = 1 := hψ₂inj (by rw [h2, h1, map_one, map_one])
      left
      rw [hg, hh]
      rfl
    · have hqz : q = z := by rw [← inv_inv q, h1, hzinv]
      have hg : g = QuaternionGroup.a 2 := hψ₁inj (by rw [← hq, hqz, hψ₁a2])
      have hh : h = QuaternionGroup.a 2 := hψ₂inj (by rw [h2, h1, hψ₂a2])
      right
      rw [hg, hh]
  have hT : IsPGroup 2 ↥(Subgroup.zpowers β) := by
    have hdvd : orderOf β ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hβ2])
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hcommT : ∀ (a : QuaternionGroup 2 × QuaternionGroup 2) (t : Y),
      t ∈ Subgroup.zpowers β → φ a * t = t * φ a := by
    intro a t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (Commute.zpow_right (hβ (φ a)) k).eq
  obtain ⟨⟨g₁, g₂⟩, hgβ, hgc⟩ := CFSG.GH74.Generic.q8q8_commuting_two_subgroup_le' hY φ hφ
    (Subgroup.zpowers β) hT hcommT β (Subgroup.mem_zpowers β)
  have hg₂ : g₂ = 1 ∨ g₂ = QuaternionGroup.a 2 := by
    refine quaternion_center g₂ (fun x => ?_)
    have := congrArg Prod.snd (hgc (1, x))
    simpa using this
  rw [← hgβ, hφapp]
  refine ι.range.mul_mem (hrange g₁) ?_
  rcases hg₂ with rfl | rfl
  · rw [map_one]
    exact ι.range.one_mem
  · rw [hψ₂a2]
    exact ⟨z, rfl⟩

end W

end S3T5

end CFSG.GH74.Generic.BProg.B3
