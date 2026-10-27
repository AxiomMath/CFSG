module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenCent2
public import CFSG.ClassicalInvolution.Asc77.AscL62C66a

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem eq_of_le_member [Finite G] {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (hpair : ∀ C ∈ Δ, ∀ D ∈ Δ, C ≠ D → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ C ≤ J ∧ D ≤ J')
    (hcyc : ∀ C ∈ Δ, IsCyclic ↥C ∧ 4 ≤ Nat.card ↥C) (h2 : ∀ C ∈ Δ, IsPGroup 2 ↥C)
    {C D : Subgroup G} (hC : C ∈ Δ) (hD : D ∈ Δ) {J : Subgroup G} (hJ : J ∈ Ω) (hCJ : C ≤ J)
    (hDJ : D ≤ J) : C = D := by
  by_contra hne
  obtain ⟨J₁, hJ₁, J₂, hJ₂, hJJ, hCJ₁, hDJ₂⟩ := hpair C hC D hD hne
  have e1 : J₁ = J := eq_of_le_of_le hΩ hJ₁ hJ (h2 C hC) (hcyc C hC).2 hCJ₁ hCJ
  have e2 : J₂ = J := eq_of_le_of_le hΩ hJ₂ hJ (h2 D hD) (hcyc D hD).2 hDJ₂ hDJ
  exact hJJ (e1.trans e2.symm)


structure C66Data (Ω : Set (Subgroup G)) (S : Subgroup G) (Δ : Set (Subgroup G))
    (A B K J : Subgroup G) (z t : G) : Prop where
  hS : IsPGroup 2 ↥S
  hΔS : ∀ C ∈ Δ, C ≤ S
  hΔinv : ∀ C ∈ Δ, ∀ s ∈ S, conjSub s C ∈ Δ
  hcyc : ∀ C ∈ Δ, IsCyclic ↥C ∧ 4 ≤ Nat.card ↥C
  hpair : ∀ C ∈ Δ, ∀ D ∈ Δ, C ≠ D → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ C ≤ J ∧ D ≤ J'
  hA : A ∈ Δ
  hB : B ∈ Δ
  hAorb : ∀ C₁ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s A},
    ∀ C₂ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s A}, C₁ ≠ C₂ → Commutes C₁ C₂
  hBorb : ∀ C₁ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s B},
    ∀ C₂ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s B}, C₁ ≠ C₂ → Commutes C₁ C₂
  hAK : A ≤ K
  hBJ : B ≤ J
  pair : Pair Ω K J z t
  hnc : ¬ Commutes A B

namespace C66Data

variable {S : Subgroup G} {Δ : Set (Subgroup G)} {A B K J : Subgroup G} {z t : G}

theorem h2 (c : C66Data Ω S Δ A B K J z t) : ∀ C ∈ Δ, IsPGroup 2 ↥C := fun C hC =>
  c.hS.to_le (c.hΔS C hC)

theorem hA2 (c : C66Data Ω S Δ A B K J z t) : IsPGroup 2 ↥A := c.h2 A c.hA

theorem hB2 (c : C66Data Ω S Δ A B K J z t) : IsPGroup 2 ↥B := c.h2 B c.hB

theorem hAS (c : C66Data Ω S Δ A B K J z t) : A ≤ S := c.hΔS A c.hA

theorem hBS (c : C66Data Ω S Δ A B K J z t) : B ≤ S := c.hΔS B c.hB

theorem hAc (c : C66Data Ω S Δ A B K J z t) : IsCyclic ↥A := (c.hcyc A c.hA).1

theorem hBc (c : C66Data Ω S Δ A B K J z t) : IsCyclic ↥B := (c.hcyc B c.hB).1

theorem hA4 (c : C66Data Ω S Δ A B K J z t) : 4 ≤ Nat.card A := (c.hcyc A c.hA).2

theorem hB4 (c : C66Data Ω S Δ A B K J z t) : 4 ≤ Nat.card B := (c.hcyc B c.hB).2

end C66Data

variable [Finite G]

theorem Pair.commutes_of_normalizes_right {K J : Subgroup G} {z t : G} (hΩ : HypOmegaGen Ω)
    (h : Pair Ω K J z t) {A B : Subgroup G}
    (hAK : A ≤ K) (hBJ : B ≤ J) (hA : IsCyclic ↥A) (hB : IsCyclic ↥B) (hA2 : IsPGroup 2 ↥A)
    (hB2 : IsPGroup 2 ↥B) (hA4 : 4 ≤ Nat.card A) (hAB : ∀ s ∈ A, conjSub s B = B) :
    Commutes A B := by
  obtain ⟨y, hyA, m, hm, hyo, hAy⟩ := exists_generator_pow hA hA2 hA4
  exact commutes_of_generator hAy fun b hb =>
    h.symm.centralizes_of_normalizes_of_order hΩ (hAK hyA) hm hyo hBJ hB hB2
      (hAB y hyA) b hb

theorem Pair.commutes_of_normalizes_left {K J : Subgroup G} {z t : G} (hΩ : HypOmegaGen Ω)
    (h : Pair Ω K J z t) {A B : Subgroup G}
    (hAK : A ≤ K) (hBJ : B ≤ J) (hA : IsCyclic ↥A) (hB : IsCyclic ↥B) (hA2 : IsPGroup 2 ↥A)
    (hB2 : IsPGroup 2 ↥B) (hB4 : 4 ≤ Nat.card B) (hBA : ∀ s ∈ B, conjSub s A = A) :
    Commutes A B := by
  obtain ⟨y, hyB, m, hm, hyo, hBy⟩ := exists_generator_pow hB hB2 hB4
  have := commutes_of_generator hBy fun a ha =>
    h.centralizes_of_normalizes_of_order hΩ (hBJ hyB) hm hyo hAK hA hA2 (hBA y hyB) a ha
  exact this.symm

namespace C66Data

variable {S : Subgroup G} {Δ : Set (Subgroup G)} {A B K J : Subgroup G} {z t : G}

theorem caseI (hΩ : HypOmegaGen Ω)
    (c : C66Data Ω S Δ A B K J z t) (hAt : conjSub t A = A) : False := by
  apply c.hnc
  by_cases hcomm : ∀ y ∈ A, t * y = y * t
  ·
    have hAc' : A ≤ Subgroup.centralizer ({t} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy).symm
    have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_le_centralizer hΩ c.pair.hJ c.pair.hK c.pair.ne.symm c.pair.ht
        c.hAK c.hA2 (by have := c.hA4; omega) hAc'
    have hAB : ∀ s ∈ A, conjSub s B = B := by
      intro s hs
      have hsJ : conjSub s J = J := mem_normalizer_iff_conjSub_eq.mp (hAJ hs)
      have hmem : conjSub s B ∈ Δ := c.hΔinv B c.hB s (c.hAS hs)
      have hle : conjSub s B ≤ J := by
        have := conjSub_mono (n := s) c.hBJ
        rwa [hsJ] at this
      exact eq_of_le_member hΩ c.hpair c.hcyc c.h2 hmem c.hB c.pair.hJ hle c.hBJ
    exact c.pair.commutes_of_normalizes_right hΩ c.hAK c.hBJ c.hAc c.hBc c.hA2 c.hB2
      c.hA4 hAB
  ·
    push Not at hcomm
    obtain ⟨y, hyA, hty⟩ := hcomm
    have hyS : y ∈ S := c.hAS hyA
    set cy : G := t * y * t⁻¹ * y⁻¹ with hcy
    have hcyA : cy ∈ A := by
      have h1 : t * y * t⁻¹ ∈ conjSub t A := conj_mem_conjSub hyA
      rw [hAt] at h1
      exact A.mul_mem h1 (A.inv_mem hyA)
    have hcy1 : cy ≠ 1 := by
      intro h1
      apply hty
      have h2 : t * y * t⁻¹ = y := mul_inv_eq_one.mp h1
      calc t * y = (t * y * t⁻¹) * t := by group
        _ = y * t := by rw [h2]
    have htB : t ∈ B :=
      mem_of_uniqueInvolution_of_pGroup c.pair.ht c.hBJ c.hB2 (by have := c.hB4; omega)
    have hcyB : ∀ b ∈ B, cy * b = b * cy := by
      intro b hb
      have h1 := orbit_commute c.hBc c.hBorb S.one_mem hyS hb (B.inv_mem htB)
      simp only [one_mul, inv_one, mul_one] at h1
      have htb : t * b = b * t := cyclic_comm c.hBc htB hb
      have hcy' : cy = t * (y * t⁻¹ * y⁻¹) := by rw [hcy]; group
      rw [hcy']
      calc t * (y * t⁻¹ * y⁻¹) * b = t * ((y * t⁻¹ * y⁻¹) * b) := by group
        _ = t * (b * (y * t⁻¹ * y⁻¹)) := by rw [← h1]
        _ = (t * b) * (y * t⁻¹ * y⁻¹) := by group
        _ = (b * t) * (y * t⁻¹ * y⁻¹) := by rw [htb]
        _ = b * (t * (y * t⁻¹ * y⁻¹)) := by group
    obtain ⟨i, hi⟩ := orderOf_eq_two_pow_of_isPGroup c.hA2 hcyA
    obtain ⟨w, hw, hw2, hw1⟩ := exists_involution_pow hcy1 hi
    have hwK : w ∈ K := c.hAK ((Subgroup.zpowers_le.mpr hcyA) hw)
    have hwz : w = z := (c.pair.hz.unique w hwK hw2).resolve_left hw1
    have hzB : ∀ b ∈ B, b * z = z * b := by
      intro b hb
      rw [← hwz]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (show Commute cy b from hcyB b hb) k).eq.symm
    have hBc' : B ≤ Subgroup.centralizer ({z} : Set G) := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hzB b hb)
    have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
      le_normalizer_of_le_centralizer hΩ c.pair.hK c.pair.hJ c.pair.ne c.pair.hz c.hBJ
        c.hB2 (by have := c.hB4; omega) hBc'
    have hBA : ∀ s ∈ B, conjSub s A = A := by
      intro s hs
      have hsK : conjSub s K = K := mem_normalizer_iff_conjSub_eq.mp (hBK hs)
      have hmem : conjSub s A ∈ Δ := c.hΔinv A c.hA s (c.hBS hs)
      have hle : conjSub s A ≤ K := by
        have := conjSub_mono (n := s) c.hAK
        rwa [hsK] at this
      exact eq_of_le_member hΩ c.hpair c.hcyc c.h2 hmem c.hA c.pair.hK hle c.hAK
    exact c.pair.commutes_of_normalizes_left hΩ c.hAK c.hBJ c.hAc c.hBc c.hA2 c.hB2
      c.hB4 hBA

end C66Data

theorem Pair.conjSub_eq_of_comm_z {K J : Subgroup G} {z t : G}
    (hΩ : HypOmegaGen Ω) (h : Pair Ω K J z t) {x : G} (hxJ : x ∈ J) (hxo : orderOf x = 4)
    (hxz : x * z = z * x) : conjSub x K = K := by
  have hV2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_centralizer hΩ h.hK h.hJ h.ne h.hz (Subgroup.zpowers_le.mpr hxJ)
      hV2 (by rw [Nat.card_zpowers, hxo]; norm_num)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxz))
  exact mem_normalizer_iff_conjSub_eq.mp (hle (Subgroup.mem_zpowers x))

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
