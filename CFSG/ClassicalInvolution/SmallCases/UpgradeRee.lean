module

public import CFSG.ClassicalInvolution.Generic.Induction
import CFSG.ClassicalInvolution.Basic
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification

private theorem commutator_mul_of_commute {G : Type*} [Group G] {a b c d : G} (hac : Commute a c)
    (had : Commute a d) (hbc : Commute b c) (hab : Commute a b) (hcd : Commute c d) :
    (a * b) * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = b * d * b⁻¹ * d⁻¹ := by
  have h1 : Commute a (b * c * d * b⁻¹) :=
    ((hab.mul_right hac).mul_right had).mul_right hab.inv_right
  have h2 : Commute c (b * d * b⁻¹ * d⁻¹) :=
    (((hbc.symm.mul_right hcd).mul_right hbc.symm.inv_right).mul_right hcd.inv_right)
  calc (a * b) * (c * d) * (a * b)⁻¹ * (c * d)⁻¹
      = a * (b * c * d * b⁻¹) * a⁻¹ * d⁻¹ * c⁻¹ := by group
    _ = (b * c * d * b⁻¹) * d⁻¹ * c⁻¹ := by
        rw [h1.eq]; group
    _ = c * (b * d * b⁻¹ * d⁻¹) * c⁻¹ := by
        have : b * c = c * b := hbc.eq
        calc (b * c * d * b⁻¹) * d⁻¹ * c⁻¹ = (c * b * d * b⁻¹) * d⁻¹ * c⁻¹ := by rw [this]
          _ = c * (b * d * b⁻¹ * d⁻¹) * c⁻¹ := by group
    _ = b * d * b⁻¹ * d⁻¹ := by rw [h2.eq]; group

theorem le_of_perfect_of_sup_eq_centralizer {G : Type*} [Group G] {x : G} {L K : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({x} : Set G))
    (hsup : Subgroup.zpowers x ⊔ L = Subgroup.centralizer ({x} : Set G))
    (hKC : K ≤ Subgroup.centralizer ({x} : Set G)) (hperf : Group.IsPerfect K) : K ≤ L := by
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)
      rw [← h1, mul_inv_cancel_right]
      exact hl
    · intro hl
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)
      have h2 : l = x * l * x⁻¹ := by
        have h3 : x * l = x * (x * l * x⁻¹) := by
          rw [← h1]
          group
        exact mul_left_cancel h3
      rw [h2]
      exact hl
  have hdec : ∀ k ∈ K, ∃ n : ℤ, ∃ l ∈ L, k = x ^ n * l := by
    intro k hk
    have hkC : k ∈ Subgroup.zpowers x ⊔ L := hsup ▸ hKC hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm,
      Set.mem_mul] at hkC
    obtain ⟨y, hy, l, hl, hyl⟩ := hkC
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨n, l, hl, hyl.symm⟩
  have hcentral : ∀ (n : ℤ) (c : G), c ∈ Subgroup.centralizer ({x} : Set G) →
      Commute (x ^ n) c := fun n c hc =>
    (show Commute x c from (Subgroup.mem_centralizer_singleton_iff.1 hc).symm).zpow_left n
  have hcomm : ⁅K, K⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨n₁, l₁, hl₁, rfl⟩ := hdec k₁ hk₁
    obtain ⟨n₂, l₂, hl₂, rfl⟩ := hdec k₂ hk₂
    have hl₁C := hLC hl₁
    have hl₂C := hLC hl₂
    rw [commutatorElement_def,
      commutator_mul_of_commute ((Commute.refl x).zpow_zpow n₁ n₂) (hcentral n₁ l₂ hl₂C)
        (hcentral n₂ l₁ hl₁C).symm (hcentral n₁ l₁ hl₁C) (hcentral n₂ l₂ hl₂C)]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)
  have hK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hperf
  rw [← hK]
  exact hcomm

theorem false_of_isClassicalMember_of_reeTitsModel {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {r e : ℕ} (hree : CFSG.Blueprint.ReeTitsModel G .twistedG2 r e) {K : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) : False := by
  obtain ⟨-, -, -, hr3, -, h3⟩ := hree.1
  obtain ⟨a, hea, -⟩ := hree.2
  subst hr3 hea
  have ha : 1 ≤ a := by omega
  obtain ⟨-, -, hcen, -⟩ := LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
    a ha G hree
  obtain ⟨L, hLC, hinf, hsup, -, -⟩ := hcen z hK.orderOf_eq_two
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hK.subnormal
  have hKL : K ≤ L := le_of_perfect_of_sup_eq_centralizer hLC hsup hKC hK.perfect
  have hz : z ∈ Subgroup.zpowers z ⊓ L := ⟨Subgroup.mem_zpowers z, hKL hK.mem⟩
  rw [hinf, Subgroup.mem_bot] at hz
  have h2 := hK.orderOf_eq_two
  rw [hz, orderOf_one] at h2
  omega

end CFSG.ClassicalInvolution.Upgrade
