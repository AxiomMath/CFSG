module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X]

namespace Setting3

variable (s : Setting3 X)

theorem exists_r (hAZ : CF82AZ) (Z : ZData s.h) :
    ∃ r ∈ s.h.secG0 s.y, ∃ b₀ ∈ s.h.secB0 s.y, r⁻¹ * s.h.a * r = Z.z * b₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haG : s.h.a ∈ s.h.secSub s.y := s.secCond.a_mem_secSub
  have hzG : Z.z ∈ s.h.secSub s.y := s.D_le_secSub Z.hzD
  set aG : ↥(s.h.secSub s.y) := ⟨s.h.a, haG⟩ with haG'
  set zG : ↥(s.h.secSub s.y) := ⟨Z.z, hzG⟩ with hzG'
  have hzJ : s.h.subQ s.y zG ∈ s.sec.J := by
    rw [s.sec_J]
    exact mem_map_of_mem _ (show zG ∈ (s.h.secJ0 s.y).subgroupOf _ from s.D_le_J0 Z.hzD)
  have hz2 : orderOf (s.h.subQ s.y zG) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, show zG * zG = 1 from Subtype.ext Z.hzz, map_one]
    · intro h1
      have h2 := secQ_eq_one_of_two (w := zG) (k := 1) (by rw [pow_one, pow_two]; exact Z.hzz) h1
      have := s.D_inf_B0 ▸ mem_inf.mpr ⟨Z.hzD, h2⟩
      exact Z.hz1 (mem_bot.mp this)
  have ha2 : orderOf s.sec.a = 2 := s.sec.orderOf_a
  obtain ⟨gb, -, hgb⟩ := hAZ (s.h.subQuot s.y) s.p s.f s.hp s.hp2 s.hf s.simple s.centralizer_eq
    s.type s.mod4_L s.mod4_U s.sec.a s.a_mem ha2 s.sec.J s.sec.J_le s.sec.isPComponent_J s.J_type
    _ hzJ hz2
  rw [s.sec_a haG] at hgb
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(s.h.secSubImg s.y)) gb
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥(s.h.secSubImg s.y))).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.prime_two.coprime_iff_not_dvd).mp
      (pPrimeCore_coprime_card (p := 2) (G := ↥(s.h.secSubImg s.y)))
  have hu2 : IsPGroup 2 (zpowers (s.h.subMk s.y aG)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, show aG * aG = 1 from Subtype.ext (Six.a_mul_a_self s.h), map_one]
    · intro h1
      have h2 : s.h.subQ s.y aG = 1 := by
        show QuotientGroup.mk' _ (s.h.subMk s.y aG) = 1
        rw [h1, map_one]
      rw [← s.sec_a haG] at h2
      rw [h2, orderOf_one] at ha2
      exact absurd ha2 (by norm_num)
  have hv2 : IsPGroup 2 (zpowers (s.h.subMk s.y zG)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, show zG * zG = 1 from Subtype.ext Z.hzz, map_one]
    · intro h1
      have h2 : s.h.subQ s.y zG = 1 := by
        show QuotientGroup.mk' _ (s.h.subMk s.y zG) = 1
        rw [h1, map_one]
      rw [h2, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
  obtain ⟨c, -, hc⟩ := Eight.exists_conj_eq_of_map hker hu2 hv2 g₁ (by
    show s.h.subQ s.y zG = _
    rw [← hgb]
    rfl)
  obtain ⟨r, rfl⟩ := s.h.subMk_surjective s.y c
  have h1 : s.h.subMk s.y (zG⁻¹ * (r⁻¹ * aG * r)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← hc]
    exact inv_mul_cancel _
  have h2 : zG⁻¹ * (r⁻¹ * aG * r) ∈ (s.h.subMk s.y).ker := h1
  rw [s.h.ker_subMk s.y] at h2
  refine ⟨r, s.h.secSub_le_G0 s.y r.2, Z.z⁻¹ * ((r : X)⁻¹ * s.h.a * r), ?_, by group⟩
  have h3 := mem_subgroupOf.mp h2
  simpa using h3

end Setting3

end Eight2

end CFSG.ComponentClassification.GSThmB
