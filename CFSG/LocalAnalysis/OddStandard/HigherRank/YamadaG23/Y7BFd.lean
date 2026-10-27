module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56P
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3AbsT

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private lemma y7bfd_zpow_two_eq_one_or_self {Γ : Type} [Group Γ] {x : Γ} (hx : x ^ 2 = 1)
    (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · left
    rw [orderOf_eq_one_iff.mp h1, one_zpow]
  · have hmod := zpow_mod_orderOf x k
    rw [h2] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
      simp
    · right
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
      simp

private lemma y7bfd_conj_eq {Γ : Type} [Group Γ] {x h : Γ} :
    h * x * h⁻¹ = ⁅x, h⁆⁻¹ * x := by
  rw [commutatorElement_def]
  group

private lemma y7bfd_comm_mul {Γ : Type} [Group Γ] {α h f v : Γ}
    (hh : h * f * h⁻¹ = v * f) :
    ⁅α * h, f⁆ = ⁅α, v⁆ * v * ⁅α, f⁆ := by
  rw [commutatorElement_def]
  rw [show (α * h) * f * (α * h)⁻¹ * f⁻¹ = α * (h * f * h⁻¹) * α⁻¹ * f⁻¹ by group]
  rw [hh, commutatorElement_def, commutatorElement_def]
  group

private lemma y7bfd_inv_mul_z {Γ : Type} [Group Γ] {d z : Γ} (hd : d ^ 2 = z) (hz : z ^ 2 = 1) :
    (d * z)⁻¹ = d := by
  have hd4 : d ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hd, hz]
  rw [inv_eq_iff_mul_eq_one, ← hd]
  calc (d * d ^ 2) * d = d ^ 4 := by group
    _ = 1 := hd4

private lemma y7bfd_S_eq (s : Setting3 G L) :
    s.fr.S = Subgroup.closure ({s.fr.h₀} : Set G) ⊔ s.fr.A := by
  rw [SFrame.S, SFrame.A, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false, false_or]
  tauto

theorem y7b_CF (hH : F33Hyp s e) :
    ∀ x ∈ s.fr.S, (∀ f ∈ s.fr.F, ⁅x, f⁆ ∈ s.fr.Z) → x ∈ s.fr.A := by
  intro x hxS hcomm
  have hA := lfactsA_of_setting hH.hS hH.hZ s
  have hrel := s3_srel hH.hS hH.hZ s
  have hzsq : s.fr.z ^ 2 = 1 := hrel.z_sq
  have h0sq : s.fr.h₀ ^ 2 = 1 := hrel.h0_sq
  have hSN : s.fr.S ≤ Subgroup.normalizer (s.fr.A : Set G) :=
    hH.h32.2.1.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hH.h32.1.1).mp hH.h32.1.2)
  have h0NA : s.fr.h₀ ∈ Subgroup.normalizer (s.fr.A : Set G) :=
    hSN (Subgroup.subset_closure (by simp))
  have hTNA : Subgroup.closure ({s.fr.h₀} : Set G) ≤ Subgroup.normalizer (s.fr.A : Set G) :=
    (Subgroup.closure_le (Subgroup.normalizer (s.fr.A : Set G))).mpr
      (Set.singleton_subset_iff.mpr h0NA)
  have hxS' : x ∈ Subgroup.closure ({s.fr.h₀} : Set G) ⊔ s.fr.A := by
    rw [← y7bfd_S_eq s]
    exact hxS
  obtain ⟨y, hyT, c, hcA, hyc⟩ :=
    mem_sup_of_normalizes (T := Subgroup.closure ({s.fr.h₀} : Set G)) (C := s.fr.A)
      (fun y hy c hc => (Subgroup.mem_normalizer_iff.mp (hTNA hy) c).mp hc) x hxS'
  obtain ⟨k, hk⟩ := Subgroup.mem_closure_singleton.mp hyT
  rcases y7bfd_zpow_two_eq_one_or_self h0sq k with hk1 | hk0
  ·
    have hxc : x = c := by rw [hyc, ← hk, hk1, one_mul]
    rw [hxc]
    exact hcA
  ·
    exfalso
    have hy0 : y = s.fr.h₀ := by rw [← hk, hk0]
    have hαA : s.fr.h₀ * c * s.fr.h₀⁻¹ ∈ s.fr.A :=
      (Subgroup.mem_normalizer_iff.mp h0NA c).mp hcA
    have hxα : x = (s.fr.h₀ * c * s.fr.h₀⁻¹) * s.fr.h₀ := by
      rw [hyc, hy0]
      group
    have hb1sq : s.fr.b₁ ^ 2 = s.fr.z := by rw [SFrame.z]
    have hb1z_inv : (s.fr.b₁ * s.fr.z)⁻¹ = s.fr.b₁ := y7bfd_inv_mul_z hb1sq hzsq
    have hb2z_inv : (s.fr.b₂ * s.fr.z)⁻¹ = s.fr.b₂ :=
      y7bfd_inv_mul_z hrel.b2_sq hzsq
    have hconj1 : s.fr.h₀ * s.fr.a₁ * s.fr.h₀⁻¹ = s.fr.b₁ * s.fr.a₁ := by
      rw [y7bfd_conj_eq, hrel.a1h, hb1z_inv]
    have hconj2 : s.fr.h₀ * s.fr.a₂ * s.fr.h₀⁻¹ = s.fr.b₂ * s.fr.a₂ := by
      rw [y7bfd_conj_eq, hrel.a2h, hb2z_inv]
    have ha1b2 : s.fr.a₁ * s.fr.b₂ = s.fr.b₂ * s.fr.a₁ :=
      commutatorElement_eq_one_iff_mul_comm.mp hrel.a1b2
    have hconjf : s.fr.h₀ * (s.fr.a₁ * s.fr.a₂) * s.fr.h₀⁻¹
        = (s.fr.b₁ * s.fr.b₂) * (s.fr.a₁ * s.fr.a₂) := by
      calc s.fr.h₀ * (s.fr.a₁ * s.fr.a₂) * s.fr.h₀⁻¹
          = (s.fr.h₀ * s.fr.a₁ * s.fr.h₀⁻¹) * (s.fr.h₀ * s.fr.a₂ * s.fr.h₀⁻¹) := by
            group
        _ = (s.fr.b₁ * s.fr.a₁) * (s.fr.b₂ * s.fr.a₂) := by rw [hconj1, hconj2]
        _ = (s.fr.b₁ * s.fr.b₂) * (s.fr.a₁ * s.fr.a₂) := by
            rw [show (s.fr.b₁ * s.fr.a₁) * (s.fr.b₂ * s.fr.a₂)
                = s.fr.b₁ * (s.fr.a₁ * s.fr.b₂) * s.fr.a₂ by group, ha1b2]
            group
    have hfF : s.fr.a₁ * s.fr.a₂ ∈ s.fr.F := Subgroup.subset_closure (by simp)
    have hfA : s.fr.a₁ * s.fr.a₂ ∈ s.fr.A :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hb12A : s.fr.b₁ * s.fr.b₂ ∈ s.fr.A :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hvZ : ⁅s.fr.h₀ * c * s.fr.h₀⁻¹, s.fr.b₁ * s.fr.b₂⁆ ∈ s.fr.Z :=
      hA.comm_A _ hαA _ hb12A
    have hfZ : ⁅s.fr.h₀ * c * s.fr.h₀⁻¹, s.fr.a₁ * s.fr.a₂⁆ ∈ s.fr.Z :=
      hA.comm_A _ hαA _ hfA
    have hxfZ : ⁅(s.fr.h₀ * c * s.fr.h₀⁻¹) * s.fr.h₀, s.fr.a₁ * s.fr.a₂⁆ ∈ s.fr.Z := by
      rw [← hxα]
      exact hcomm _ hfF
    have hb12Z : s.fr.b₁ * s.fr.b₂ ∈ s.fr.Z := by
      have hdecomp :
          ⁅(s.fr.h₀ * c * s.fr.h₀⁻¹) * s.fr.h₀, s.fr.a₁ * s.fr.a₂⁆
            = ⁅s.fr.h₀ * c * s.fr.h₀⁻¹, s.fr.b₁ * s.fr.b₂⁆ * (s.fr.b₁ * s.fr.b₂)
              * ⁅s.fr.h₀ * c * s.fr.h₀⁻¹, s.fr.a₁ * s.fr.a₂⁆ :=
        y7bfd_comm_mul hconjf
      have heq : s.fr.b₁ * s.fr.b₂
          = ⁅s.fr.h₀ * c * s.fr.h₀⁻¹, s.fr.b₁ * s.fr.b₂⁆⁻¹
            * ⁅(s.fr.h₀ * c * s.fr.h₀⁻¹) * s.fr.h₀, s.fr.a₁ * s.fr.a₂⁆
            * ⁅s.fr.h₀ * c * s.fr.h₀⁻¹, s.fr.a₁ * s.fr.a₂⁆⁻¹ := by
        rw [hdecomp]
        group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hvZ) hxfZ)
        (Subgroup.inv_mem _ hfZ)
    obtain ⟨-, -, hw1, -, hwz, -⟩ := y56_v0 hH
    rw [SFrame.Z, Subgroup.mem_zpowers_iff] at hb12Z
    obtain ⟨m, hm⟩ := hb12Z
    rcases y7bfd_zpow_two_eq_one_or_self hzsq m with hm1 | hmz
    · exact hw1 (by rw [← hm, hm1])
    · exact hwz (by rw [← hm, hmz])

end CFSG.OddStandard.HigherRank.YamadaG23
