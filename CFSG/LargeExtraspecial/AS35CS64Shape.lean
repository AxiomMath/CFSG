module

public import CFSG.LargeExtraspecial.AS35CS64Trick

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_commSpace_cases [IsSimpleGroup G] (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z)
    {t : G} (htQ : t ∈ S.QG) (htx : t ∈ S.Qa g) (ht1 : t ≠ 1) :
    ∃ s : S.Qt, ∀ u ∈ commSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
      u = 0 ∨ u = S.cl t ∨ u = s ∨ u = S.cl t + s := by
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  have hx2 : x * x = 1 := by rw [← hgx]; exact S.conj_mul_self g
  have hlam := S.conj_ne_mul_z_of_mem_Qa hn hW hgx hxM hxz htQ htx ht1
  have hne : g * S.z * g⁻¹ ≠ S.z := by rw [hgx]; exact hxz
  have htz : t ≠ S.z := fun h => S.z_not_mem_Qa hW hne (h ▸ htx)
  have hclc : ∀ c : G, S.cl c + σ (S.cl c) = σ (S.cl c) - S.cl c := fun c => by
    rw [sub_eq_add_vec (ZMod 2), add_comm]
  have aux : ∀ c ∈ S.QG, c * t = t * c →
      S.cl c + σ (S.cl c) = 0 ∨ S.cl c + σ (S.cl c) = S.cl t := by
    intro c hcQ hct
    have hjQ := S.comm_mem_QG hxM hcQ
    have hmem : S.cl c + σ (S.cl c) ∈ commSpace σ := by
      rw [hclc]
      exact sub_mem_commSpace σ (S.cl c)
    have hj2 : (c * x * c⁻¹ * x⁻¹) ^ 2 = 1 := (S.q_cl_eq_zero_iff hjQ).mp (by
      rw [S.cl_comm hxM hcQ]
      exact S.q_commSpace_eq_zero hxM hx2 hlam hmem)
    rcases S.smith_trick hW hgx hxM hxz htQ htx ht1 hcQ hct hj2 with h | h | h | h
    · left
      rw [← S.cl_comm hxM hcQ, h, S.cl_one]
    · left
      rw [← S.cl_comm hxM hcQ, h, S.cl_z]
    · right
      rw [← S.cl_comm hxM hcQ, h]
    · right
      rw [← S.cl_comm hxM hcQ, h, S.cl_mul_z htQ]
  obtain ⟨c₀, hc₀Q, hc₀⟩ := S.exists_conj_eq_mul_z htQ ht1 htz
  have hc₀t : polar S.q (S.cl c₀) (S.cl t) = 1 := by
    rw [S.polar_cl_eq_one_iff hc₀Q htQ]
    intro h
    have h' : c₀ * t * c₀⁻¹ = t := by rw [h]; group
    rw [h'] at hc₀
    exact S.z_ne_one (mul_left_cancel (hc₀.symm.trans (mul_one t).symm))
  refine ⟨S.cl c₀ + σ (S.cl c₀), fun u hu => ?_⟩
  obtain ⟨v, hv⟩ := mem_commSpace.mp hu
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hu' : u = S.cl c + σ (S.cl c) := by rw [← hv, hclc]
  rcases zmod2_cases (polar S.q (S.cl c) (S.cl t)) with h0 | h1
  · rcases aux c hcQ ((S.polar_cl_eq_zero_iff hcQ htQ).mp h0) with h | h
    · left
      rw [hu', h]
    · right; left
      rw [hu', h]
  · have hcc : (c * c₀) * t = t * (c * c₀) := by
      rw [← S.polar_cl_eq_zero_iff (mul_mem hcQ hc₀Q) htQ, S.cl_mul hcQ hc₀Q, polar_add_left, h1,
        hc₀t]
      decide
    have hsum : S.cl (c * c₀) + σ (S.cl (c * c₀)) = u + (S.cl c₀ + σ (S.cl c₀)) := by
      rw [S.cl_mul hcQ hc₀Q, map_add, hu']
      abel
    rcases aux (c * c₀) (mul_mem hcQ hc₀Q) hcc with h | h
    · right; right; left
      rw [hsum] at h
      rw [eq_neg_of_add_eq_zero_left h, neg_vec_eq (ZMod 2)]
    · right; right; right
      rw [hsum] at h
      rw [eq_sub_of_add_eq h, sub_eq_add_vec (ZMod 2)]

theorem exists_sq_eq_z_of_mem_Qa [IsSimpleGroup G] (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z)
    {t : G} (htQ : t ∈ S.QG) (htx : t ∈ S.Qa g) (ht1 : t ≠ 1) :
    ∃ a ∈ S.QG, a * x = x * a ∧ a ^ 2 = S.z := by
  classical
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  by_contra hcon
  push Not at hcon
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  have hlam := S.conj_ne_mul_z_of_mem_Qa hn hW hgx hxM hxz htQ htx ht1
  obtain ⟨s, hs⟩ := S.exists_commSpace_cases hn hW hgx hxM hxz htQ htx ht1
  set A : Subgroup G := S.QG ⊓ centralizer ({x} : Set G) with hA
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨haQ, hac⟩ := mem_inf.mp ha
    rw [mem_centralizer_singleton_iff] at hac
    rcases S.sq_eq_one_or_z haQ with h | h
    · rwa [pow_two] at h
    · exact absurd h (hcon a haQ hac)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hab := hsq (a * b) (mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have hAle := S.card_le_of_commute (inf_le_left : A ≤ S.QG) hcomm
  have hfix : S.clPre (fixSpace σ) ≤ A := by
    intro e he
    obtain ⟨heQ, hecl⟩ := S.mem_clPre.mp he
    exact mem_inf.mpr ⟨heQ, mem_centralizer_singleton_iff.mpr
      (S.commute_of_fix hxM hlam heQ (mem_fixSpace.mp hecl))⟩
  have hcomm_le : commSpace σ ≤
      Submodule.span (ZMod 2) (({S.cl t, s} : Finset S.Qt) : Set S.Qt) := by
    intro u hu
    have h1 : S.cl t ∈ Submodule.span (ZMod 2) (({S.cl t, s} : Finset S.Qt) : Set S.Qt) :=
      Submodule.subset_span (by simp)
    have h2 : s ∈ Submodule.span (ZMod 2) (({S.cl t, s} : Finset S.Qt) : Set S.Qt) :=
      Submodule.subset_span (by simp)
    rcases hs u hu with h | h | h | h <;> rw [h]
    · exact zero_mem _
    · exact h1
    · exact h2
    · exact add_mem h1 h2
  have hrk : finrank (ZMod 2) (commSpace σ) ≤ 2 :=
    (Submodule.finrank_mono hcomm_le).trans ((finrank_span_finset_le_card _).trans
      Finset.card_le_two)
  have hsum := finrank_commSpace_add_finrank_fixSpace σ
  rw [S.finrank_Qt_eq_two_mul_width] at hsum
  have hle := (Subgroup.card_le_of_le hfix).trans hAle
  rw [S.card_clPre, S.card_submodule] at hle
  have h3 : 2 ^ (2 * S.width - 1) ≤ 2 ^ (S.width + 1) := by
    calc 2 ^ (2 * S.width - 1) = 2 * 2 ^ (2 * S.width - 2) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * 2 ^ finrank (ZMod 2) (fixSpace σ) :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ 2 ^ (S.width + 1) := hle
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

end Setting

end CFSG.LargeExtraspecial
