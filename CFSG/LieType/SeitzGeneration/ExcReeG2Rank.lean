module

public import CFSG.RankThree.Chevalley.SteinbergCFSmallReePlaneCore
public import CFSG.Walter.Ree.Cyclic
public import CFSG.RankThree.PartOne.KF1514B.Sylow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Walter.Ree.Model

section Ree


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem smallReeH_neg_one_orderOf (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    orderOf (smallReeH a K (-1)) = 2 := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, hS8, -, hconj, -⟩ := small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
  have h1 : smallReeH a K (-1) ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ smallReeE8 a K w₀, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : smallReeE8 a K w₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
      rw [this, Subgroup.card_bot] at hS8
      omega
    obtain ⟨g, -, hg⟩ := hconj x hx hx1
    rw [h1] at hg
    exact hx1 (calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [hg]; group)
  exact orderOf_eq_prime (CFSG.RankThree.Chevalley.smallReeH_neg_one_sq) h1

theorem smallReeH_mem_invCentralizer (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    smallReeH a K (-1) ∈ smallReeInvCentralizer a K := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨ψ, -, -, -, -, -, -, ⟨hsup, -, -⟩, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  rw [← hsup]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem relIndex_smallReeInvCentralizer (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (smallReeInvCentralizer a K).relIndex (ReeTag.G2.reeGamma K a) =
      Nat.card K ^ 2 * (Nat.card K ^ 2 - Nat.card K + 1) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, hΓ, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have hle : smallReeInvCentralizer a K ≤ ReeTag.G2.reeGamma K a := inf_le_left
  have h := Subgroup.relIndex_mul_card (H := smallReeInvCentralizer a K)
    (K := ReeTag.G2.reeGamma K a)
  rw [inf_of_le_left hle, card_smallReeInvCentralizer hw₀ hK, hΓ, ← hK] at h
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqq : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow two_ne_zero _
  have h1q2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
  have hpos : 0 < Nat.card K * (Nat.card K ^ 2 - 1) :=
    Nat.mul_pos hq1 (by have : 3 ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq3 2; omega)
  refine Nat.eq_of_mul_eq_mul_right hpos (h.trans ?_)
  zify [hq1, hqq, h1q2]
  ring

theorem no_plane_reeGamma_G2 (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup (ModGL ReeTag.G2.tag K)}
    (hEΓ : E ≤ ReeTag.G2.reeGamma K a) (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  have hEel : IsElementaryAbelian p ↥(E.subgroupOf Γ) := IsElementaryAbelian.subgroupOf hEΓ
  have hEcard' : Nat.card ↥(E.subgroupOf Γ) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv
  have hEp : IsPGroup p ↥(E.subgroupOf Γ) := IsElementaryAbelian.isPGroup p _
  by_cases hpq : p ∣ Nat.card K ^ 2 - Nat.card K + 1
  · obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
    have hcyc : IsCyclic (P : Subgroup ↥Γ) :=
      CFSG.Walter.Ree.reeGamma_isCyclic_sylow a ha K hK p hpq P
    have : IsCyclic ↥(E.subgroupOf Γ) :=
      isCyclic_of_injective (Subgroup.inclusion hEP) (Subgroup.inclusion_injective hEP)
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEcard' this
  · have hidx : ¬ p ∣ ((smallReeInvCentralizer a K).subgroupOf Γ).index := by
      change ¬ p ∣ (smallReeInvCentralizer a K).relIndex Γ
      rw [relIndex_smallReeInvCentralizer hK]
      intro hd
      rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
      · have h3 : p ∣ 3 ^ (2 * a + 1) := hK ▸ hp.dvd_of_dvd_pow h1
        have h4 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
      · exact hpq h1
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KF1514B.exists_conj_le_of_not_dvd_index hidx hEp
    have hCΓ : smallReeInvCentralizer a K ≤ Γ := inf_le_left
    have htΓ : smallReeH a K (-1) ∈ Γ := hCΓ (smallReeH_mem_invCentralizer hK)
    set E₁ : Subgroup ↥Γ := (E.subgroupOf Γ).map (MulAut.conj g).toMonoidHom with hE₁
    have hE₁el : IsElementaryAbelian p ↥E₁ := IsElementaryAbelian.map (A := E.subgroupOf Γ) _
    set E' : Subgroup (ModGL ReeTag.G2.tag K) := E₁.map Γ.subtype with hE'
    have hE'el : IsElementaryAbelian p ↥E' := IsElementaryAbelian.map (A := E₁) _
    have hE'card : Nat.card E' = p ^ 2 := by
      rw [hE', Subgroup.card_map_of_injective Γ.subtype_injective, hE₁,
        Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard']
    have hE'z : E' ≤ Subgroup.centralizer {smallReeH a K (-1)} := by
      rintro _ ⟨z, hz, rfl⟩
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (hg hz))).2
    exact CFSG.RankThree.Chevalley.smallRee_false_of_plane_le_centralizer_involution hK hp hp3
      htΓ (smallReeH_neg_one_orderOf hK) E' (Subgroup.map_subtype_le _) hE'el hE'card hE'z

end Ree

end CFSG.LieType.SeitzGeneration
