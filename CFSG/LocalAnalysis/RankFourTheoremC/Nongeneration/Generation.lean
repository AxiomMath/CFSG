module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Lift
public import CFSG.Open.GeneratedCore
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration

open CFSG.Open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem le_glbCore_two_of_closure_fixed {p : ℕ} [Fact p.Prime] {R : Subgroup X}
    {K : Subgroup X} [K.Normal] (hperf : commutator ↥K = ⊤)
    (hZ : ¬ p ∣ Nat.card (center ↥K)) {A : Subgroup X} (hAR : A ≤ R) (hA : IsElemAbelian p A)
    {c : X} (hcR : c ∈ R) (hcK : c ∈ centralizer (K : Set X)) (hcp : orderOf c = p)
    (hcA : ∀ a ∈ A, a * c = c * a) {E : Subgroup (MulAut (K ⧸ center K))}
    (hE : E ≤ A.map (barAct K))
    (hgen : Subgroup.closure {kb : K ⧸ center K | ∃ e ∈ E, e ≠ 1 ∧ e kb = kb} = ⊤) :
    K ≤ GLBCore p 2 R := by
  classical
  have hp : p.Prime := Fact.out
  have hcpow : c ^ p = 1 := by rw [← hcp]; exact pow_orderOf_eq_one c
  set π : ↥K →* K ⧸ center ↥K := QuotientGroup.mk' (center ↥K) with hπ
  set W : Subgroup ↥K := (GLBCore p 2 R).comap K.subtype with hW
  have hsub : {kb : K ⧸ center K | ∃ e ∈ E, e ≠ 1 ∧ e kb = kb} ⊆
      (W.map π : Set (K ⧸ center K)) := by
    rintro kb ⟨e, heE, he1, hek⟩
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.1 (hE heE)
    have hap : a ^ p = 1 := hA.2 a haA
    have hnc : ∃ k ∈ K, a * k ≠ k * a := by
      by_contra hcon
      push Not at hcon
      exact he1 (barAct_eq_one_of_commute hcon)
    obtain ⟨k₁, hk₁, hne⟩ := hnc
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hne (by simp)
    have hao : orderOf a = p := orderOf_eq_prime hap ha1
    obtain ⟨k, hkmk, hkfix⟩ := exists_fixed_lift hZ hap hek
    have hca : c ∉ zpowers a := by
      intro hc
      have hle : zpowers c ≤ zpowers a := Subgroup.zpowers_le.2 hc
      have heq : zpowers c = zpowers a :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hcp, hao])
      have hamem : a ∈ zpowers c := heq ▸ Subgroup.mem_zpowers a
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hamem
      apply hne
      rw [← hj]
      exact ((Commute.zpow_right (show Commute k₁ c from
        Subgroup.mem_centralizer_iff.1 hcK k₁ hk₁) j).eq).symm
    obtain ⟨hel, hcard⟩ := GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hap hcpow ha1
      hca (hcA a haA)
    have hQR : zpowers a ⊔ zpowers c ≤ R :=
      sup_le (Subgroup.zpowers_le.2 (hAR haA)) (Subgroup.zpowers_le.2 hcR)
    have hrank : 2 ≤ Open.pRank p (zpowers a ⊔ zpowers c) :=
      GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_rfl hel hcard
    have hQle : zpowers a ⊔ zpowers c ≤ centralizer ({((k : K) : X)} : Set X) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : a * (k : X) * a⁻¹ = (k : X) := congrArg Subtype.val hkfix
        calc a * (k : X) = a * (k : X) * a⁻¹ * a := by group
          _ = (k : X) * a := by rw [h1]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hcK k k.2).symm
    have hkc : ((k : K) : X) ∈ centralizer ((zpowers a ⊔ zpowers c : Subgroup X) : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun q hq =>
        Subgroup.mem_centralizer_singleton_iff.1 (hQle hq)
    have hB : normalizer ((zpowers a ⊔ zpowers c : Subgroup X) : Set X) ≤ GLBCore p 2 R :=
      le_sSup ⟨zpowers a ⊔ zpowers c, hQR, hrank, rfl⟩
    have hkW : k ∈ W := hB (Subgroup.centralizer_le_normalizer _ hkc)
    exact Subgroup.mem_map.2 ⟨k, hkW, hkmk⟩
  have hmap : W.map π = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le _).2 hsub
  have hsup : W ⊔ center ↥K = ⊤ := by
    have h1 := Subgroup.comap_map_eq π W
    rw [hmap, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hWtop : W = ⊤ := eq_top_of_sup_center hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ W := hWtop ▸ Subgroup.mem_top _
  exact this

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration
