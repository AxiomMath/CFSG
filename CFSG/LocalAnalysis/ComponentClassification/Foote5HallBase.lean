module

import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallEight
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeak

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

theorem nonempty_mulEquiv_of_data (hcD : c ∈ D) (hcard : Nat.card D = 2 * orderOf c)
    (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) :
    Nonempty (D ≃* DihedralGroup (orderOf c)) := by
  obtain ⟨u, huD, huC⟩ := exists_refl hcard
  obtain ⟨hu2, huc⟩ : u * u = 1 ∧ u * c * u⁻¹ = c⁻¹ := by
    rcases hD u huD with h | h
    · exact absurd h huC
    · exact h
  have hinv : ∀ x ∈ zpowers c, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow, huc, inv_zpow]
  obtain ⟨e⟩ := ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected (T := zpowers c) huC hu2 hinv
  have hle : zpowers c ⊔ zpowers u ≤ D := sup_le (zpowers_le.mpr hcD) (zpowers_le.mpr huD)
  have hcard' : Nat.card (zpowers c ⊔ zpowers u : Subgroup G) = Nat.card D := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, Nat.card_zpowers, hcard]
  have heq : zpowers c ⊔ zpowers u = D := eq_of_le_of_card_ge hle hcard'.ge
  rw [Nat.card_zpowers] at e
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans e⟩

theorem weak_of_hallConclusion (hcD : c ∈ D) (hk : 4 ∣ orderOf c)
    (hcard : Nat.card D = 2 * orderOf c)
    (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹))
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
    (hconc : ∃ S₀ T : Subgroup G, IsSylowOf 2 T ⊤ ∧ D ≤ S₀ ∧ S₀ ≤ T ∧
      Open.fusionStronglyClosed (S₀ : Set G) T ∧
      (S₀ = D ∨ (AschbacherTheorem3.IsSemidihedralTwoGroup S₀ ∧
        Nat.card S₀ = 2 * Nat.card D))) :
    HallWeakConclusion D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, T, hT, hDS, hST, hsc, hcase⟩ := hconc
  have hk0 : 0 < orderOf c := orderOf_pos c
  refine ⟨S₀, T, hT, hDS, hST, hsc, ?_, ?_⟩
  · intro x hxS hx2
    rcases hcase with rfl | ⟨⟨n, hn, ⟨f⟩⟩, hcardS⟩
    · exact hxS
    by_contra hxD
    have hTN := le_normalizer_of_sic hD hcl hcard hT.isPGroup (hDS.trans hST)
    have hxN := hTN (hST hxS)
    have hx1 : x ≠ 1 := fun h => hxD (h ▸ one_mem D)
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
    have h2n : 2 ^ n = 4 * orderOf c := by
      have h := Nat.card_congr f.toEquiv
      rw [CFSG.Semidihedral.card n (by omega), hcardS, hcard] at h
      omega
    have hfx : orderOf (f ⟨x, hxS⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxo]
    have hck : c ^ orderOf c = 1 := pow_orderOf_eq_one c
    have hdk : ∀ d ∈ D, d ^ orderOf c = 1 := by
      intro d hd
      rcases hD d hd with h | ⟨h, -⟩
      · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp h
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hck, one_zpow]
      · rw [show orderOf c = 2 * (orderOf c / 2) by omega, pow_mul,
          show d ^ 2 = 1 by rw [sq]; exact h, one_pow]
    rcases QuasiDihedralFusion.sd_involution_cases hn _ hfx with hz | hconj
    ·
      have hxc : ∀ y ∈ S₀, x * y = y * x := by
        intro y hy
        have h := Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn) (f ⟨y, hy⟩)
        rw [← hz, ← map_mul, ← map_mul] at h
        have h' := congrArg Subtype.val (f.injective h)
        simpa using h'.symm
      have hyk : ∀ y ∈ S₀, y ^ orderOf c = 1 := by
        intro y hy
        by_cases hyD : y ∈ D
        · exact hdk y hyD
        · have hw := inv_mul_mem_of_card_le hDS (by omega) hxS hy hxD hyD
          have hcomm : Commute x (x⁻¹ * y) := hxc _ (mul_mem (inv_mem hxS) hy)
          have hxk : x ^ orderOf c = 1 := by
            rw [show orderOf c = 2 * (orderOf c / 2) by omega, pow_mul,
              show x ^ 2 = 1 by rw [sq]; exact hx2, one_pow]
          rw [show y = x * (x⁻¹ * y) by group, hcomm.mul_pow, hxk, hdk _ hw, one_mul]
      have hr : orderOf ((f.symm (CFSG.Semidihedral.r n) : S₀) : G) = 2 * orderOf c := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, CFSG.Semidihedral.orderOf_r n (by omega),
          CFSG.Semidihedral.modulus]
        have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        omega
      have h8 := Nat.le_of_dvd hk0
        (orderOf_dvd_of_pow_eq_one (hyk _ (f.symm (CFSG.Semidihedral.r n)).2))
      omega
    ·
      have key : ∀ y (hy : y ∈ D), y * y = 1 → y ≠ 1 →
          f ⟨y, hDS hy⟩ ≠ CFSG.Semidihedral.z n → False := by
        intro y hyD hy2 hy1 hyz
        have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
        have hfy : orderOf (f ⟨y, hDS hyD⟩) = 2 := by
          rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hyo]
        rcases QuasiDihedralFusion.sd_involution_cases hn _ hfy with h | h
        · exact hyz h
        · obtain ⟨σ, hσ⟩ := isConj_iff.mp (hconj.symm.trans h)
          have h1 : f.symm σ * ⟨x, hxS⟩ * (f.symm σ)⁻¹ = ⟨y, hDS hyD⟩ := by
            apply f.injective
            rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hσ]
          have h2 : ((f.symm σ : S₀) : G) * x * ((f.symm σ : S₀) : G)⁻¹ = y := by
            have h' := congrArg Subtype.val h1
            simpa using h'
          exact hcl x hxN hxD hxo y hyD hyo ((f.symm σ : S₀) : G)⁻¹ (by rw [inv_inv]; exact h2)
      obtain ⟨u, huD, huC⟩ := exists_refl hcard
      have hu2 : u * u = 1 := by
        rcases hD u huD with h | ⟨h, -⟩
        · exact absurd h huC
        · exact h
      have hucC : u * c ∉ zpowers c := fun h => huC (by
        rw [show u = u * c * c⁻¹ by group]
        exact mul_mem h (inv_mem (mem_zpowers c)))
      have huc2 : (u * c) * (u * c) = 1 := by
        rcases hD _ (mul_mem huD hcD) with h | ⟨h, -⟩
        · exact absurd h hucC
        · exact h
      have hu1 : u ≠ 1 := fun h => huC (h ▸ one_mem _)
      have huc1 : u * c ≠ 1 := fun h => hucC (h ▸ one_mem _)
      by_cases hu : f ⟨u, hDS huD⟩ = CFSG.Semidihedral.z n
      · refine key (u * c) (mul_mem huD hcD) huc2 huc1 fun h => ?_
        rw [← hu] at h
        have h' := congrArg Subtype.val (f.injective h)
        have hc1 : c = 1 := by
          have : c = u⁻¹ * (u * c) := by group
          rw [this]
          change u⁻¹ * (u * c) = 1
          rw [show u * c = u from h']
          group
        rw [hc1, orderOf_one] at hk
        omega
      · exact key u huD hu2 hu1 hu
  · rcases hcase with rfl | ⟨-, h⟩
    · omega
    · omega

theorem weak_d8
    (hcD : c ∈ D) (hco : orderOf c = 4) (hcard : Nat.card D = 2 * orderOf c)
    (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹))
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) :
    HallWeakConclusion D := by
  obtain ⟨e₀⟩ := nonempty_mulEquiv_of_data hcD hcard hD
  rw [hco] at e₀
  exact weak_of_hallConclusion hcD (by rw [hco]) hcard hD hcl (HallD8.hall_d8 e₀ hcl)

end CFSG.ComponentClassification.Foote5.HallGen
