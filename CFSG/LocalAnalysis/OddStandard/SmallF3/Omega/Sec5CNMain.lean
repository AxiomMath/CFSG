module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5cn_R_le_C (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (hO : Asc82Outside) (hdict : Asc82HeartDict) (hMA : Asc82Fact513AModel)
    (hAut : Asc82FactAutOm6) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {π : SL23 × SL23 →* G}
    (hπ : Sec5CNPi π (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) z) :
    ∀ x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h, x ^ 4 = 1 →
      ∀ k ∈ K₁ ⊔ K₂, k * x = x * k := by
  obtain ⟨hQN, u, v, huvN, hu, hv⟩ := sec5cn_QN h36 h37 h52a hO hdict hMA hAut c hπ
  obtain ⟨πK, hπK⟩ := sec5cn_exists_pi c.pair₁₂
  obtain ⟨hA2, hAc, hzA, ⟨a, b, ha, hb, ha1, haz, hb1, hbz, hba, hbaz⟩, -⟩ :=
    sec5cn_heart_facts hdict c
  have hzK : ∀ k ∈ K₁ ⊔ K₂, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (c.K_le hk)).2
  have hρ₀P : π (u ^ 4, v ^ 4) ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h :=
    hπ.mk_mem _ _
  have hρ₀N : π (u ^ 4, v ^ 4) ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← sec5cn_pi_pow_mk]
    exact pow_mem huvN 4
  have hu3 : (u ^ 4) ^ 3 = 1 := by
    rw [← pow_mul]
    exact sec5cn_pow12 u
  have hv3 : (v ^ 4) ^ 3 = 1 := by
    rw [← pow_mul]
    exact sec5cn_pow12 v
  have hρ₀3 : π (u ^ 4, v ^ 4) ^ 3 = 1 := by
    rw [sec5cn_pi_pow_mk, hu3, hv3]
    exact map_one π
  have hEρ : ∀ x ∈ A ⊓ (K₁ ⊔ K₂), x * π (u ^ 4, v ^ 4) = π (u ^ 4, v ^ 4) * x := fun x hx =>
    c.A_inf_K_cent_P h36 hMA (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2 hρ₀P
  have hzE : z ∈ A ⊓ (K₁ ⊔ K₂) := Subgroup.mem_inf.mpr ⟨hzA, Subgroup.mem_sup_left c.z_mem_K₁⟩
  have hQK : ∀ q ∈ K₁ ⊔ K₂, q ^ 4 = 1 → q * π (u ^ 4, v ^ 4) = π (u ^ 4, v ^ 4) * q :=
    fun q hq hq4 => sec5cn_fix_Q hπK (Subgroup.mem_inf.mp ha).2 (Subgroup.mem_inf.mp hb).2
      (hA2 a (Subgroup.mem_inf.mp ha).1) (hA2 b (Subgroup.mem_inf.mp hb).1) ha1 hb1 haz hbz hba
      hbaz (hAc a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1) hzE ha hb
      (fun x hx => hA2 x (Subgroup.mem_inf.mp hx).1) hEρ hρ₀N hρ₀3 hq hq4
  have hKC : ∀ k ∈ K₁ ⊔ K₂, k * π (u ^ 4, v ^ 4) = π (u ^ 4, v ^ 4) * k :=
    sec5cn_gen_cent c fun κ hκ hodd =>
      sec5cn_odd_cent hπK c.z_ne_one hρ₀N hQK hκ hodd
  exact fun x hx hx4 k hk => sec5cn_Q_le_C hπ hu3 hv3 hu hv hzK hKC hQN hx hx4 hk

theorem asc82Fact513Comm_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (hO : Asc82Outside) (hdict : Asc82HeartDict) (hMA : Asc82Fact513AModel)
    (hAut : Asc82FactAutOm6) : Asc82Fact513Comm := by
  intro G _ _ t L S z r B A K₁ K₂ h c x hxP hxD hxt
  obtain ⟨π, hπ⟩ := sec5cn_exists_pi c.pair₃₄
  have hRC := sec5cn_R_le_C h36 h37 h52a hO hdict hMA hAut c hπ
  obtain ⟨hQN, -⟩ := sec5cn_QN h36 h37 h52a hO hdict hMA hAut c hπ
  obtain ⟨hs2', hsz, hsP⟩ := hxD
  have hs2 : (x⁻¹ * t * x) * (x⁻¹ * t * x) = 1 := by
    rw [← pow_two, ← hs2', pow_orderOf_eq_one]
  have hs1 : x⁻¹ * t * x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs2'
    omega
  refine sec5b513_conjugate_eq_iff.mpr ?_
  by_cases hcase : x⁻¹ * t * x = t ∨ x⁻¹ * t * x = t * z
  · obtain ⟨c₀, hc₀P, hc₀4, hc₀t⟩ :=
      hπ.exists_swap c.t_mem_sup₃₄ c.t_mul_self c.t_ne_one (c.t_ne_z h37)
    have hc₀N := hQN c₀ hc₀P hc₀4
    exact sec5cn_swap_N hπ (fun g hgt hgz => c.mem_normalizer_of_cent h36
      (Subgroup.mem_centralizer_singleton_iff.mpr hgt)
      (Subgroup.mem_centralizer_singleton_iff.mpr hgz)) hc₀N hc₀P hc₀t hxP hcase
  · push_neg at hcase
    exact sec5cn_core_of_eq h36 h52a hO hAut c rfl (c.P_le_cent hxP) hs2 hs1 hsz hxt hcase.1
      hcase.2 fun k hk => (hRC _ hsP (sec5cn_pow4_of_mul_self hs2) k hk).symm

end CFSG.OddStandard.SmallF3.Omega
