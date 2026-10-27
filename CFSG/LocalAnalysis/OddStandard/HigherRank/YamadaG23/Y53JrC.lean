module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y53_zpow_two_eq_one_or_self {Γ : Type} [Group Γ] {x : Γ} (hx : x ^ 2 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
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

private lemma y53_conj_eq {Γ : Type} [Group Γ] {x h : Γ} :
    h * x * h⁻¹ = ⁅x, h⁆⁻¹ * x := by
  rw [commutatorElement_def]
  group

private theorem y53_S_eq (s : Setting3 G L) :
    s.fr.S = s.fr.A ⊔ Subgroup.closure ({s.fr.h₀} : Set G) := by
  rw [SFrame.S, SFrame.A, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false, false_or]
  tauto

private theorem y53_h0_normalizes_A {s : Setting3 G L} (hrel : SRel s.fr) :
    s.fr.h₀ ∈ Subgroup.normalizer (s.fr.A : Set G) := by
  have hzA : s.fr.z ∈ s.fr.A := s3_z_mem_A s
  have hle : Subgroup.zpowers s.fr.h₀ ≤ Subgroup.normalizer (s.fr.A : Set G) := by
    rw [SFrame.A, Subgroup.le_normalizer_closure_iff]
    intro h hh x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rcases y53_zpow_two_eq_one_or_self hrel.h0_sq k with hk1 | hk0
    · rw [← hk, hk1, one_mul, inv_one, mul_one]
      exact Subgroup.subset_closure hx
    · rw [← hk, hk0]
      rcases hx with rfl | rfl | rfl | rfl
      · rw [y53_conj_eq, hrel.a1h]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
          (Subgroup.subset_closure (by simp)) hzA)) (Subgroup.subset_closure (by simp))
      · rw [y53_conj_eq, hrel.b1h]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzA) (Subgroup.subset_closure (by simp))
      · rw [y53_conj_eq, hrel.a2h]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
          (Subgroup.subset_closure (by simp)) hzA)) (Subgroup.subset_closure (by simp))
      · rw [y53_conj_eq, hrel.b2h]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzA) (Subgroup.subset_closure (by simp))
  exact hle (Subgroup.mem_zpowers s.fr.h₀)

private theorem y53_mem_sup_closure_singleton {Γ : Type} [Group Γ] {H : Subgroup Γ} {g : Γ}
    (hg2 : g ^ 2 = 1) (hgH : g ∈ Subgroup.normalizer (H : Set Γ)) (x : Γ) :
    x ∈ H ⊔ Subgroup.closure {g} ↔ x ∈ H ∨ ∃ y ∈ H, x = y * g := by
  have hgg : g * g = 1 := by simpa [pow_two] using hg2
  let T : Subgroup Γ :=
    { carrier := {x : Γ | x ∈ H ∨ ∃ y ∈ H, x = y * g}
      one_mem' := Or.inl (one_mem H)
      mul_mem' := by
        rintro x z (hx | ⟨y, hy, rfl⟩) (hz | ⟨w, hw, rfl⟩)
        · exact Or.inl (mul_mem hx hz)
        · exact Or.inr ⟨x * w, mul_mem hx hw, (mul_assoc x w g).symm⟩
        · refine Or.inr ⟨y * (g * z * g⁻¹), mul_mem hy ?_, ?_⟩
          · exact (Subgroup.mem_set_normalizer_iff.mp hgH z).mp hz
          · rw [show y * (g * z * g⁻¹) * g = (y * g) * z by group]
        · refine Or.inl ?_
          rw [show (y * g) * (w * g) = y * (g * w * g⁻¹) * (g * g) by group,
            hgg, mul_one]
          exact mul_mem hy ((Subgroup.mem_set_normalizer_iff.mp hgH w).mp hw)
      inv_mem' := by
        rintro x (hx | ⟨y, hy, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨g * y⁻¹ * g⁻¹, ?_, ?_⟩
          · exact (Subgroup.mem_set_normalizer_iff.mp hgH y⁻¹).mp (inv_mem hy)
          · show (y * g)⁻¹ = (g * y⁻¹ * g⁻¹) * g
            rw [mul_inv_rev,
              show g⁻¹ * y⁻¹ = g * y⁻¹ by rw [inv_eq_of_mul_eq_one_right hgg]]
            group }
  have hle : H ⊔ Subgroup.closure {g} ≤ T := by
    refine sup_le (fun x hx => Or.inl hx) ?_
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact Or.inr ⟨1, one_mem H, (one_mul g).symm⟩
  have hge : T ≤ H ⊔ Subgroup.closure {g} := by
    intro x hx
    rcases hx with hxH | ⟨y, hy, hxy⟩
    · exact Subgroup.mem_sup_left hxH
    · rw [hxy]
      exact mul_mem (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hEq : H ⊔ Subgroup.closure {g} = T := le_antisymm hle hge
  rw [hEq]
  exact Iff.rfl

private theorem y53_mem_Z_comm {s : Setting3 G L} (hA : LFactsA s) {w : G}
    (hw : w ∈ s.fr.Z) : ∀ y ∈ s.fr.S, w * y = y * w := by
  have hw' : w ∈ cen s.fr.S := by rw [s3_cen_S s hA]; exact hw
  have hw'' : w ∈ Subgroup.centralizer (s.fr.S : Set G) := (Subgroup.mem_inf.mp hw').2
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp hw'' y hy).symm

private theorem y53_b1_not_mem_Z {s : Setting3 G L} (hA : LFactsA s) (hrel : SRel s.fr) :
    s.fr.b₁ ∉ s.fr.Z := by
  intro hb
  rw [SFrame.Z] at hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hz2 : s.fr.z ^ (2 : ℤ) = 1 := by simpa using hrel.z_sq
  have hb1sq : s.fr.b₁ ^ 2 = 1 := by
    have hz : (s.fr.b₁ : G) ^ (2 : ℤ) = 1 := by
      rw [← hk, ← zpow_mul, Int.mul_comm, zpow_mul, hz2, one_zpow]
    simpa using hz
  have hz1 : s.fr.z = 1 := by rw [show s.fr.z = s.fr.b₁ ^ 2 from rfl, hb1sq]
  have hzne : s.fr.z ≠ 1 := by
    intro h1
    have h2 := s3_z_order s hA
    rw [h1] at h2
    simp at h2
  exact hzne hz1

theorem y53_centS {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.fr.S, (∀ a ∈ s.fr.A, ⁅a, x⁆ ∈ s.fr.Z) → x ∈ s.fr.A := by
  intro x hxS hcomm
  have hA := lfactsA_of_setting hH.hS hH.hZ s
  have hrel := s3_srel hH.hS hH.hZ s
  rw [y53_S_eq s] at hxS
  rcases (y53_mem_sup_closure_singleton hrel.h0_sq (y53_h0_normalizes_A hrel) x).mp hxS with
    hxA | ⟨α, hαA, hx'⟩
  · exact hxA
  · exfalso
    have h1A : s.fr.a₁ ∈ s.fr.A := Subgroup.subset_closure (by simp)
    have hc : ⁅s.fr.a₁, α * s.fr.h₀⁆ ∈ s.fr.Z := by
      have h := hcomm s.fr.a₁ h1A
      rwa [hx'] at h
    have h0_mul : s.fr.h₀ * s.fr.h₀ = 1 := by rw [← pow_two]; exact hrel.h0_sq
    have h0_inv : s.fr.h₀⁻¹ = s.fr.h₀ := inv_eq_of_mul_eq_one_right h0_mul
    have hconj : s.fr.h₀ * s.fr.a₁⁻¹ * s.fr.h₀ = s.fr.a₁⁻¹ * (s.fr.b₁ * s.fr.z) := by
      have ha1h := hrel.a1h
      rw [commutatorElement_def, h0_inv] at ha1h
      rw [← ha1h]
      group
    have hdecomp : ⁅s.fr.a₁, α * s.fr.h₀⁆
        = ⁅s.fr.a₁, α⁆ * (α * (s.fr.b₁ * s.fr.z) * α⁻¹) := by
      rw [commutatorElement_def, mul_inv_rev, h0_inv]
      rw [show s.fr.a₁ * (α * s.fr.h₀) * s.fr.a₁⁻¹ * (s.fr.h₀ * α⁻¹)
            = s.fr.a₁ * α * (s.fr.h₀ * s.fr.a₁⁻¹ * s.fr.h₀) * α⁻¹ by group]
      rw [hconj]
      group
    have hca : ⁅s.fr.a₁, α⁆ ∈ s.fr.Z := hA.comm_A s.fr.a₁ h1A α hαA
    have hdZ : α * s.fr.b₁ * s.fr.z * α⁻¹ ∈ s.fr.Z := by
      have heq : α * s.fr.b₁ * s.fr.z * α⁻¹
          = ⁅s.fr.a₁, α⁆⁻¹ * ⁅s.fr.a₁, α * s.fr.h₀⁆ := by
        rw [hdecomp]
        group
      rw [heq]
      exact Subgroup.mul_mem (s.fr.Z) (Subgroup.inv_mem (s.fr.Z) hca) hc
    have hb1Z : s.fr.b₁ ∈ s.fr.Z := by
      have hcen : α⁻¹ * (α * s.fr.b₁ * s.fr.z * α⁻¹) * α = α * s.fr.b₁ * s.fr.z * α⁻¹ := by
        rw [← y53_mem_Z_comm hA hdZ α⁻¹
          (s3_A_le_S s (Subgroup.inv_mem (s.fr.A) hαA)), mul_assoc, inv_mul_cancel, mul_one]
      have hbz : s.fr.b₁ = (α⁻¹ * (α * s.fr.b₁ * s.fr.z * α⁻¹) * α) * s.fr.z⁻¹ := by group
      rw [hbz, hcen]
      exact Subgroup.mul_mem (s.fr.Z) hdZ
        (Subgroup.inv_mem (s.fr.Z) (Subgroup.mem_zpowers s.fr.z))
    exact y53_b1_not_mem_Z hA hrel hb1Z

theorem y53_centSg {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hact : ActsAs L g s.fr'.σ) :
    ∀ x ∈ s.fr.S ⊔ zpowers g, (∀ a ∈ s.fr.A, ⁅a, x⁆ ∈ s.fr.Z) → x ∈ s.fr.A := by
  intro x hx hcomm
  have h110 := hH.hLF.fact110 g hg2 hact
  have hxS : x ∈ L ⊔ Subgroup.closure ({g} : Set G) :=
    sup_le ((s3_S_le_L s).trans le_sup_left)
      ((le_of_eq (Subgroup.zpowers_eq_closure g)).trans le_sup_right) hx
  have hxmem : x ∈ (zL L ⊔ s.fr.A : Subgroup G) :=
    (Set.ext_iff.mp h110.1.2.1 x).mp ⟨hxS, hcomm⟩
  rw [f3_zL_eq_bot hH, bot_sup_eq] at hxmem
  exact hxmem

end CFSG.OddStandard.HigherRank.YamadaG23
