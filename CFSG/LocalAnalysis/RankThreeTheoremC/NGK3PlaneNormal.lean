module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Defs
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P D : Subgroup X} {z : X}

theorem PlaneData.z_mem (h : PlaneData P D z)
    (hω : ∀ c ∈ P, (∀ d ∈ D, c * d = d * c) → c ^ 3 = 1 → c ∈ zpowers z) :
    ∀ N : Subgroup X, N ≤ P → P ≤ normalizer (N : Set X) → N ≠ ⊥ → z ∈ N := by
  intro N hNP hPN hN
  obtain ⟨y, hyPN, hyc, hyo⟩ := exists_mem_inf_centralizer_of_ne_bot (p := 3) h.pgroup hPN
    (by rwa [inf_of_le_right hNP])
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hyz : y ∈ zpowers z := hω y hyPN.1
    (fun d hd => (mem_centralizer_iff.1 hyc d (h.plane.1 hd)).symm) hy3
  have heq : zpowers y = zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hyz) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hyo, h.zo]
  exact (zpowers_le.2 hyPN.2) (heq ▸ mem_zpowers z)

theorem PlaneData.inv_plane (h : PlaneData P D z)
    (hz : ∀ N : Subgroup X, N ≤ P → P ≤ normalizer (N : Set X) → N ≠ ⊥ → z ∈ N) :
    ∃ B : Subgroup X, B ≤ D ∧ Nat.card B = 9 ∧ IsElemAbelian 3 B ∧ z ∈ B ∧
      P ≤ normalizer (B : Set X) := by
  have hnc : ¬ IsCyclic D := fun hc => h.plane.2.1 hc.isMulCommutative
  obtain ⟨V, hVD, hPV, hVcard, hVpow, hVcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le Nat.prime_three (by norm_num) h.pgroup
      h.plane.1 h.normal hnc
  have hV9 : Nat.card V = 9 := by rw [hVcard]; norm_num
  have hVne : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hV9
    omega
  exact ⟨V, hVD, hV9,
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hVcomm a a.2 b b.2), hVpow⟩,
    hz V (hVD.trans h.plane.1) hPV hVne, hPV⟩

omit [Finite X] in
private lemma mul_comm_of_mem_sup_left {A A' : Subgroup X}
    (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hAA' : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a)
    {a : X} (ha : a ∈ A) {x : X} (hx : x ∈ A ⊔ A') : a * x = x * a := by
  have hle : A ⊔ A' ≤ centralizer ({a} : Set X) :=
    sup_le (fun u hu => mem_centralizer_singleton_iff.2 (hA u hu a ha))
      (fun u hu => mem_centralizer_singleton_iff.2 (hAA' a ha u hu).symm)
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

omit [Finite X] in
private lemma mul_comm_of_mem_sup {B B' : Subgroup X}
    (hB : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u) (hB' : ∀ u ∈ B', ∀ v ∈ B', u * v = v * u)
    (hBB' : ∀ b ∈ B, ∀ b' ∈ B', b * b' = b' * b) :
    ∀ x ∈ B ⊔ B', ∀ y ∈ B ⊔ B', x * y = y * x := by
  intro x hx y hy
  have hle : B ⊔ B' ≤ centralizer ({y} : Set X) := by
    refine sup_le (fun u hu => mem_centralizer_singleton_iff.2 ?_)
      (fun u hu => mem_centralizer_singleton_iff.2 ?_)
    · exact mul_comm_of_mem_sup_left hB hBB' hu hy
    · exact mul_comm_of_mem_sup_left (A := B') (A' := B) hB'
        (fun a ha a' ha' => (hBB' a' ha' a ha).symm) hu (sup_comm B B' ▸ hy)
  exact mem_centralizer_singleton_iff.1 (hle hx)

private lemma eq_nine_or_twentySeven {n : ℕ} (h9 : 9 ∣ n) (h27 : n ∣ 27) (hge : 9 ≤ n) :
    n = 9 ∨ n = 27 := by
  have hle : n ≤ 27 := Nat.le_of_dvd (by norm_num) h27
  interval_cases n <;> omega

theorem PlaneData.eq_of_comm (h : PlaneData P D z) :
    ∀ B B' : Subgroup X, B ≤ D → B' ≤ D → Nat.card B = 9 → Nat.card B' = 9 →
      (∀ b ∈ B, ∀ b' ∈ B', b * b' = b' * b) → B = B' := by
  intro B B' hBD hB'D hB hB' hcomm
  by_contra hne
  have hBc : IsMulCommutative B :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hB]; norm_num)
  have hB'c : IsMulCommutative B' :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hB']; norm_num)
  have hSD : B ⊔ B' ≤ D := sup_le hBD hB'D
  have hdvd : Nat.card (B ⊔ B' : Subgroup X) ∣ 27 := by
    have := Subgroup.card_dvd_of_le hSD
    rwa [h.card] at this
  have h9dvd : 9 ∣ Nat.card (B ⊔ B' : Subgroup X) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ B')
    rwa [hB] at this
  have h9le : 9 ≤ Nat.card (B ⊔ B' : Subgroup X) := by
    have := Subgroup.card_le_of_le (le_sup_left : B ≤ B ⊔ B')
    rwa [hB] at this
  rcases eq_nine_or_twentySeven h9dvd hdvd h9le with h9 | h27
  · exact hne ((Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ B') (by omega)).trans
      (Subgroup.eq_of_le_of_card_ge (le_sup_right : B' ≤ B ⊔ B') (by omega)).symm)
  · have hSeq : B ⊔ B' = D := Subgroup.eq_of_le_of_card_ge hSD (by rw [h.card, h27]; norm_num)
    apply h.plane.2.1
    refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    exact mul_comm_of_mem_sup
      (fun u hu v hv => congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : B) ⟨v, hv⟩))
      (fun u hu v hv => congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : B') ⟨v, hv⟩)) hcomm
      a (hSeq ▸ a.2) b (hSeq ▸ b.2)

end CFSG.LocalAnalysis.RankThreeTheoremC
