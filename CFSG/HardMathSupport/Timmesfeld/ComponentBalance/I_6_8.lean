module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega
public import CFSG.GroupTheory.FrobeniusNormalComplement

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open

theorem hasNormalPComplement_of_central_order_p {K : Type*} [Group K] [Finite K] {p : ℕ}
    [hp : Fact p.Prime] (hodd : p ≠ 2)
    (hcen : ∀ x : K, orderOf x = p → x ∈ Subgroup.center K) :
    CFSG.HasNormalPComplement p K := by
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ
  apply CFSG.SectionRank.Ccomm.isPGroup_of_coprime_eq_one
  intro a ha
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
  set C : Subgroup (Subgroup.normalizer (Q : Set K)) :=
    (Subgroup.centralizer (Q : Set K)).subgroupOf (Subgroup.normalizer (Q : Set K)) with hC
  have hker : (Q.normalizerMonoidHom).ker = C := Subgroup.normalizerMonoidHom_ker Q
  have : C.Normal := by rw [← hker]; infer_instance
  let ψ : (Subgroup.normalizer (Q : Set K)) ⧸ C →* MulAut Q :=
    QuotientGroup.lift C Q.normalizerMonoidHom (by rw [← hker])
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : Q.normalizerMonoidHom m = 1 := hx
    rw [QuotientGroup.eq_one_iff, ← hker]
    exact h1
  have hψn : ψ (QuotientGroup.mk n) = Q.normalizerMonoidHom n := rfl
  have hcop : (orderOf (Q.normalizerMonoidHom n)).Coprime p := by
    rw [← hψn, orderOf_injective ψ hψ]
    exact ha
  have hα : Q.normalizerMonoidHom n = 1 := by
    refine mulAut_eq_one_of_coprime_of_fix_omega hodd hQ hcop ?_
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    · have hord : orderOf (x : K) = p := by
        have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
        rcases (Nat.dvd_prime hp.out).1 h1 with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hx1
        · rw [Subgroup.orderOf_coe, h]
      have hc := hcen _ hord
      apply Subtype.ext
      have h2 := Subgroup.mem_center_iff.1 hc (n : K)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [h2]
      group
  rw [QuotientGroup.eq_one_iff]
  have hnC : n ∈ C := by rw [← hker]; exact hα
  exact hnC

theorem exists_orderOf_eq_prime_not_mem_center {K : Type*} [Group K] [Finite K]
    (hK : IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hdvd : p ∣ Nat.card K) :
    ∃ x : K, orderOf x = p ∧ x ∉ Subgroup.center K := by
  by_contra hno
  push Not at hno
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hN, hcop, hquot⟩ := hasNormalPComplement_of_central_order_p hodd hno
  have hKperf : Group.IsPerfect K := ⟨hK.1⟩
  have hQperf : Group.IsPerfect (K ⧸ N) := inferInstance
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra hns
    have hnt : Nontrivial (K ⧸ N) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (G := K ⧸ N) hquot.isNilpotent
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  rw [hNtop] at hcop
  have : Nat.card (⊤ : Subgroup K) = Nat.card K := Nat.card_congr (Subgroup.topEquiv).toEquiv
  rw [this] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd hp |>.1 hcop) hdvd

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
