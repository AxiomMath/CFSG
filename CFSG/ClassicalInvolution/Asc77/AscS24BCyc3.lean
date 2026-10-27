module

public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

theorem mem_Dg_of_lam {a : G} (ha : a ∈ C.A)
    (h : (C.lam ⟨a, ha⟩ : G) = 1 ∨ (C.lam ⟨a, ha⟩ : G) = z) :
    a ∈ C.Dg ∨ a * C.D.x₂⁻¹ ∈ C.Dg := by
  rcases h with h | h
  · exact Or.inl ((C.lam_eq_one_iff ⟨a, ha⟩).mp (Subtype.ext h))
  · right
    have hmem : a * C.D.x₂⁻¹ ∈ C.A := C.A.mul_mem ha (C.A.inv_mem C.x₂_mem_A)
    refine (C.lam_eq_one_iff ⟨_, hmem⟩).mp (Subtype.ext ?_)
    have e : (⟨a * C.D.x₂⁻¹, hmem⟩ : ↥C.A) = ⟨a, ha⟩ * (⟨C.D.x₂, C.x₂_mem_A⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [h, C.lam_x₂, mul_inv_cancel]

theorem exists_gen_I [IsSimpleGroup G] (h3 : H3 p f) (hng : NoGraph p f)
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W)
    (hI : ∀ a : ↥C.A, (C.lam a : G) = 1 ∨ (C.lam a : G) = z) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  have hx₂P : C.D.x₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.D.x₂_mem
  have hdec : ∀ a ∈ C.A, ∃ e ∈ C.Dg, e⁻¹ * a ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro a ha
    rcases C.mem_Dg_of_lam ha (hI ⟨a, ha⟩) with h | h
    · exact ⟨a, h, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
    · refine ⟨_, h, ?_⟩
      have e : (a * C.D.x₂⁻¹)⁻¹ * a = C.D.x₂ := by group
      rw [e]
      exact hx₂P
  obtain ⟨y, hyS, hyM⟩ := IsConcreteLE.not_le_iff_exists.mp hSP
  obtain ⟨x, hxP, a, ha, rfl⟩ := C.exists_mem_A hng hyS
  obtain ⟨d, hd, hda⟩ := hdec a ha
  have hdS : d ∈ (S : Subgroup G) := C.A_le_S (C.Dg_le_A hd)
  have hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro hdP
    apply hyM
    have e : x * a = x * d * (d⁻¹ * a) := by group
    rw [e]
    exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxP hdP) hda).2
  refine ⟨d, hdS, ?_, ?_, d, hd, C.Dg_sq_of_not_mem h3 hd hdP⟩
  · rw [C.Dg_pow_four h3 hd]
    exact Subgroup.one_mem _
  · intro y' hy'
    obtain ⟨x', hx'P, a', ha', rfl⟩ := C.exists_mem_A hng hy'
    obtain ⟨e, he, hea⟩ := hdec a' ha'
    by_cases heP : e ∈ (S : Subgroup G) ⊓ MGrp Ω W
    · refine ⟨0, ?_⟩
      have e1 : (d ^ (0 : ℤ))⁻¹ * (x' * a') = x' * e * (e⁻¹ * a') := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx'P heP) hea
    · refine ⟨1, ?_⟩
      have h1 := C.Dg_inv_mul_mem h3 hd he hdP heP
      have h2 := C.P_normal (S.inv_mem hdS) hx'P
      have e1 : (d ^ (1 : ℤ))⁻¹ * (x' * a') =
          d⁻¹ * x' * d⁻¹⁻¹ * ((d⁻¹ * e) * (e⁻¹ * a')) := by group
      rw [e1]
      exact Subgroup.mul_mem _ h2 (Subgroup.mul_mem _ h1 hea)

theorem exists_gen_II [IsSimpleGroup G] (h3 : H3 p f) (hng : NoGraph p f) {a : G}
    (ha : a ∈ C.A) (h1 : (C.lam ⟨a, ha⟩ : G) ≠ 1) (hz : (C.lam ⟨a, ha⟩ : G) ≠ z) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  have hx₂P : C.D.x₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.D.x₂_mem
  have haS : a ∈ (S : Subgroup G) := C.A_le_S ha
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = (C.lam ⟨a, ha⟩ : G) := ⟨_, rfl⟩
  have hy₀mem : y₀ ∈ Subgroup.zpowers C.D.x₂ := hy₀ ▸ (C.lam ⟨a, ha⟩).2
  have hy₀sq : y₀ * y₀ ≠ 1 := by
    intro h
    rcases eq_one_or_eq_sq_of_mem_zpowers C.orderOf_x₂ hy₀mem h with h' | h'
    · exact h1 (hy₀ ▸ h')
    · exact hz (hy₀ ▸ h'.trans C.x₂_sq)
  obtain ⟨hsq, hgen⟩ := sq_and_gen_of_mem_zpowers C.orderOf_x₂ hy₀mem hy₀sq
  have hd₀A : a * a * C.D.x₂⁻¹ ∈ C.A :=
    C.A.mul_mem (C.A.mul_mem ha ha) (C.A.inv_mem C.x₂_mem_A)
  have hd₀ : a * a * C.D.x₂⁻¹ ∈ C.Dg := by
    refine (C.lam_eq_one_iff ⟨_, hd₀A⟩).mp (Subtype.ext ?_)
    have e : (⟨a * a * C.D.x₂⁻¹, hd₀A⟩ : ↥C.A) =
        ⟨a, ha⟩ * ⟨a, ha⟩ * (⟨C.D.x₂, C.x₂_mem_A⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [C.lam_x₂, ← hy₀, hsq, C.x₂_sq, mul_inv_cancel]
  have hca : Commute a C.D.x₂ :=
    Subgroup.mem_centralizer_singleton_iff.mp (C.A_le_centralizer_x₂ ha)
  have hcomm : Commute (a * a) C.D.x₂⁻¹ := (hca.mul_left hca).inv_right
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right C.hzK.sq
  have hsq₀ : (a * a * C.D.x₂⁻¹) * (a * a * C.D.x₂⁻¹) = a ^ 4 * z := by
    calc (a * a * C.D.x₂⁻¹) * (a * a * C.D.x₂⁻¹) = (a * a * C.D.x₂⁻¹) ^ 2 := (sq _).symm
      _ = (a * a) ^ 2 * (C.D.x₂ ^ 2)⁻¹ := by rw [hcomm.mul_pow, inv_pow]
      _ = a ^ 4 * z := by
          rw [C.x₂_sq, hzinv]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hd₀P : a * a * C.D.x₂⁻¹ ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro hP
    have h2 : (a * a * C.D.x₂⁻¹) * (a * a * C.D.x₂⁻¹) = 1 := by
      rcases C.Dg_mem_P hd₀ hP with h | h <;> rw [h]
      · exact mul_one 1
      · exact C.hzK.sq
    rw [hsq₀] at h2
    apply C.pow_four_ne_z ha
    calc a ^ 4 = a ^ 4 * z * z := by rw [mul_assoc, C.hzK.sq, mul_one]
      _ = z := by rw [h2, one_mul]
  have hd₀z := C.Dg_sq_of_not_mem h3 hd₀ hd₀P
  have ha4 : a ^ 4 = 1 := by
    have h := hsq₀.symm.trans hd₀z
    calc a ^ 4 = a ^ 4 * z * z⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  refine ⟨a, haS, by rw [ha4]; exact Subgroup.one_mem _, ?_, _, hd₀, hd₀z⟩
  intro y hy
  obtain ⟨x, hxP, a', ha', rfl⟩ := C.exists_mem_A hng hy
  obtain ⟨k, hk⟩ := hgen _ (C.lam ⟨a', ha'⟩).2
  have heA : a ^ (-k) * a' ∈ C.A := C.A.mul_mem (C.A.zpow_mem ha (-k)) ha'
  have he : a ^ (-k) * a' ∈ C.Dg := by
    refine (C.lam_eq_one_iff ⟨_, heA⟩).mp (Subtype.ext ?_)
    have e : (⟨a ^ (-k) * a', heA⟩ : ↥C.A) = ⟨a, ha⟩ ^ (-k) * ⟨a', ha'⟩ := rfl
    rw [e, map_mul, map_zpow]
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, OneMemClass.coe_one]
    rw [← hy₀, ← hk, zpow_neg, inv_mul_cancel]
  by_cases heP : a ^ (-k) * a' ∈ (S : Subgroup G) ⊓ MGrp Ω W
  · refine ⟨k, ?_⟩
    have e1 : (a ^ k)⁻¹ * (x * a') = a ^ (-k) * x * (a ^ (-k))⁻¹ * (a ^ (-k) * a') := by group
    rw [e1]
    exact Subgroup.mul_mem _ (C.P_normal (S.zpow_mem haS _) hxP) heP
  · refine ⟨k + 2, ?_⟩
    have h1 := C.Dg_inv_mul_mem h3 hd₀ he hd₀P heP
    have e1 : (a ^ (k + 2))⁻¹ * (x * a') = a ^ (-(k + 2)) * x * (a ^ (-(k + 2)))⁻¹ *
        (C.D.x₂⁻¹ * ((a * a * C.D.x₂⁻¹)⁻¹ * (a ^ (-k) * a'))) := by group
    rw [e1]
    exact Subgroup.mul_mem _ (C.P_normal (S.zpow_mem haS _) hxP)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₂P) h1)

theorem exists_gen [IsSimpleGroup G] (h3 : H3 p f) (hng : NoGraph p f)
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  by_cases hI : ∀ a : ↥C.A, (C.lam a : G) = 1 ∨ (C.lam a : G) = z
  · exact C.exists_gen_I h3 hng hSP hI
  · push Not at hI
    obtain ⟨⟨a, ha⟩, h1, hz⟩ := hI
    exact C.exists_gen_II h3 hng ha h1 hz

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
