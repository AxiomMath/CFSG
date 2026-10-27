module

public import CFSG.ClassicalInvolution.SmallCases.NDBStmt
public import CFSG.ClassicalInvolution.SmallCases.NDB1Model
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootCtx
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.AscE189Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Std
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpPhi

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure AxisSeed (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) (M₂ M₃ : Subgroup G)
    (u₂ u₃ : G) : Prop where
  tq₂ : M₂ ∈ tqMembers Ω z
  tq₃ : M₃ ∈ tqMembers Ω z
  cls₂ : IsClassicalMember p f M₂ u₂
  cls₃ : IsClassicalMember p f M₃ u₃
  comm₁₂ : ∀ a ∈ modOdd z K, ∀ b ∈ modOdd z (exactCore z M₂), a * b = b * a
  comm₁₃ : ∀ a ∈ modOdd z K, ∀ b ∈ modOdd z (exactCore z M₃), a * b = b * a
  comm₂₃ : ∀ a ∈ modOdd z (exactCore z M₂), ∀ b ∈ modOdd z (exactCore z M₃), a * b = b * a
  prod : ∀ (h₁ : z ∈ Subgroup.centralizer ({z} : Set G))
    (h₂ : u₂ ∈ Subgroup.centralizer ({z} : Set G)) (h₃ : u₃ ∈ Subgroup.centralizer ({z} : Set G)),
    oddQuotMk z ⟨z, h₁⟩ * oddQuotMk z ⟨u₂, h₂⟩ = oddQuotMk z ⟨u₃, h₃⟩

namespace Seed

theorem eq_or_eq_of_card_two {n : ℕ} (hn : n = 2) {a b : Fin n} (hab : a ≠ b) (j : Fin n) :
    j = a ∨ j = b := by
  have hj := j.2
  have n01 : a.val ≠ b.val := fun e => hab (Fin.ext e)
  by_contra hcon
  push Not at hcon
  have a1 : j.val ≠ a.val := fun e => hcon.1 (Fin.ext e)
  have a2 : j.val ≠ b.val := fun e => hcon.2 (Fin.ext e)
  omega

theorem exists_central_lift {U X : Type} [Group U] [Group X] [Group.IsPerfect U] (ψ : U →* X)
    (hker : ψ.ker ≤ Subgroup.center U) {x : X} (hx : x ∈ ψ.range)
    (hcomm : ∀ y ∈ ψ.range, x * y = y * x) : ∃ ε ∈ Subgroup.center U, ψ ε = x := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨u, FrameVertex.mem_center_of_commutators_central fun t => hker ?_, rfl⟩
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
    hcomm _ ⟨t, rfl⟩]
  group

end Seed

variable {p f}

theorem exists_axisSeed {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (hsh : PSpShape p f Ω z) :
    ∃ (M₂ M₃ : Subgroup G) (u₂ u₃ : G), AxisSeed p f Ω K z M₂ M₃ u₂ u₃ := by
  obtain ⟨D, hcard, i₀, i₁, hne, -, -, ht₁, hr₁, x, hx1, hx₀, hx₁⟩ := hsh
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz
  let C : XCtx p f Ω z := { K := K, hK := hK, hKz := hKz, hΩ := hΩ, hp := hp, hq := hq, D := D }
  have h4 : 4 ≤ p ^ D.exp i₁ := C.four_le i₁ (by rw [ht₁]; decide)
  obtain ⟨R₂, R₃, τ₂, τ₃, hP⟩ := exists_pspPair_model hp (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁
    hr₁ (D.admissible i₁) h4
  have := hP.perfect
  have hsingle := C.single i₁ (by rw [ht₁]; decide) (by rw [ht₁]; decide)
  obtain ⟨M₂, hM₂, hM₂img⟩ := C.exists_member_of_fund i₁ hsingle hP.mem₂
  obtain ⟨M₃, hM₃, hM₃img⟩ := C.exists_member_of_fund i₁ hsingle hP.mem₃
  obtain ⟨u₂, hu₂⟩ := hΩ.classical M₂ hM₂.1
  obtain ⟨u₃, hu₃⟩ := hΩ.classical M₃ hM₃.1
  obtain ⟨j₀, hj₀, hKimg⟩ := C.exists_A1_of_K
  have hj₀ne : j₀ ≠ i₁ := by
    rintro rfl
    rw [ht₁] at hj₀
    exact absurd hj₀.1 (by decide)
  have hj₀i₀ : j₀ = i₀ := (Seed.eq_or_eq_of_card_two hcard hne j₀).resolve_right hj₀ne
  have hexK : exactCore z K = K := C.exactCore_K
  have hKbar : modOdd z K = (C.psi i₀).range := by
    rw [← hj₀i₀, ← hKimg, hexK]
  have hθinj := sectionQuotientHom_injective C.hs.normalizes
  set x' := sectionQuotientHom C.hs.normalizes x with hx'
  have hx'1 : x' ≠ 1 := fun h => hx1 (hθinj (h.trans (map_one _).symm))
  have hx'₀ : x' ∈ (C.psi i₀).range := by
    obtain ⟨a, ha⟩ := hx₀
    refine ⟨a, ?_⟩
    show sectionQuotientHom C.hs.normalizes (D.hom i₀ a) = x'
    rw [ha]
  have hx'₁ : x' ∈ (C.psi i₁).range := by
    obtain ⟨a, ha⟩ := hx₁
    refine ⟨a, ?_⟩
    show sectionQuotientHom C.hs.normalizes (D.hom i₁ a) = x'
    rw [ha]
  have hcomm : ∀ y ∈ (C.psi i₁).range, x' * y = y * x' := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := hx'₀
    rw [← ha]
    exact C.psi_commute hne a b
  obtain ⟨ε, hε, hεx⟩ := Seed.exists_central_lift (C.psi i₁) (C.psi_ker i₁) hx'₁ hcomm
  have hετ : ε = τ₂ * τ₃ :=
    (hP.center ε hε).resolve_left fun h => hx'1 (by rw [← hεx, h, map_one])
  have hττ : τ₂ * τ₃ = τ₃ * τ₂ := hP.comm τ₂ hP.hτ₂ τ₃ hP.hτ₃
  have hx'sq : x' * x' = 1 := by
    have e : τ₂ * τ₃ * (τ₂ * τ₃) = 1 := by
      calc τ₂ * τ₃ * (τ₂ * τ₃) = τ₂ * (τ₃ * τ₂) * τ₃ := by group
        _ = τ₂ * (τ₂ * τ₃) * τ₃ := by rw [hττ]
        _ = (τ₂ * τ₂) * (τ₃ * τ₃) := by group
        _ = 1 := by rw [hP.sq₂, hP.sq₃, one_mul]
    rw [← hεx, ← map_mul, hετ, e, map_one]
  have hU := C.isUniqueInvolution_modOdd C.K_tq C.K_cl
  have hx'K : x' ∈ modOdd z (exactCore z C.K) := by
    rw [hKimg, hj₀i₀]
    exact hx'₀
  have hxz : x' = oddQuotMk z ⟨z, C.involution_mem_centralizer C.K_tq C.K_cl⟩ :=
    (hU.unique x' hx'K hx'sq).resolve_left hx'1
  have hbar : ∀ {M : Subgroup G} {u : G} {R : Subgroup (compModel C.D i₁).K}
      {τ : (compModel C.D i₁).K} (hM : M ∈ tqMembers Ω z) (hu : IsClassicalMember p f M u),
      modOdd z (exactCore z M) = R.map (C.psi i₁) → τ ∈ R → τ * τ = 1 → C.psi i₁ τ ≠ 1 →
      oddQuotMk z ⟨u, C.involution_mem_centralizer hM hu⟩ = C.psi i₁ τ := by
    intro M u R τ hM hu himg hτ hτ2 hτ1
    have hUM := C.isUniqueInvolution_modOdd hM hu
    have hmem : C.psi i₁ τ ∈ modOdd z (exactCore z M) := by
      rw [himg]
      exact ⟨τ, hτ, rfl⟩
    have hsq : C.psi i₁ τ * C.psi i₁ τ = 1 := by rw [← map_mul, hτ2, map_one]
    exact ((hUM.unique _ hmem hsq).resolve_left hτ1).symm
  have hne₂ : C.psi i₁ τ₂ ≠ 1 := by
    intro h
    rcases hP.center τ₂ (C.psi_ker i₁ (MonoidHom.mem_ker.mpr h)) with h1 | h1
    · exact hP.ne₂ h1
    · exact hP.ne₃ (mul_left_cancel (h1.symm.trans (mul_one τ₂).symm))
  have hne₃ : C.psi i₁ τ₃ ≠ 1 := by
    intro h
    rcases hP.center τ₃ (C.psi_ker i₁ (MonoidHom.mem_ker.mpr h)) with h1 | h1
    · exact hP.ne₃ h1
    · exact hP.ne₂ (mul_right_cancel ((one_mul τ₃).trans h1)).symm
  have hu₂bar := hbar hM₂ hu₂ hM₂img hP.hτ₂ hP.sq₂ hne₂
  have hu₃bar := hbar hM₃ hu₃ hM₃img hP.hτ₃ hP.sq₃ hne₃
  refine ⟨M₂, M₃, u₂, u₃, hM₂, hM₃, hu₂, hu₃, ?_, ?_, ?_, ?_⟩
  · rintro a ha b hb
    rw [hKbar] at ha
    rw [hM₂img] at hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', -, rfl⟩ := hb
    exact C.psi_commute hne a' b'
  · rintro a ha b hb
    rw [hKbar] at ha
    rw [hM₃img] at hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', -, rfl⟩ := hb
    exact C.psi_commute hne a' b'
  · rintro a ha b hb
    rw [hM₂img] at ha
    rw [hM₃img] at hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, hP.comm a' ha' b' hb']
  · intro h₁ h₂ h₃
    have e1 : oddQuotMk z ⟨z, h₁⟩ = C.psi i₁ (τ₂ * τ₃) := by
      rw [← hετ, hεx, hxz]
    rw [e1, hu₂bar, hu₃bar, ← map_mul]
    congr 1
    calc τ₂ * τ₃ * τ₂ = τ₃ * τ₂ * τ₂ := by rw [hττ]
      _ = τ₃ := by rw [mul_assoc, hP.sq₂, mul_one]

end CFSG.ClassicalInvolution.NDB
