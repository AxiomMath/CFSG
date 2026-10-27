module

public import CFSG.GF2Type.Aschbacher1976HigherCenter.LayerFacts
public import CFSG.GF2Type.Aschbacher1976HigherCenter.PowFourCentralizes
public import CFSG.GF2Type.Aschbacher1976Common.CyclicTICommute
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GF2Type.Aschbacher1976HigherCenter.CenterFacts

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG CFSG.Open

theorem commute_conj_of_conjugate_le_local
    {G : Type} [Group G] [Finite G] {M B Q : Subgroup G} {z : G} {D : Subgroup Q} {k u : ℕ}
    (h : Setup M B Q z D k u) {g : G} (hgM : conjugate (critCenter D) g ≤ M) :
    ∀ b ∈ conjugate (critCenter D) g, ∀ x ∈ Q, b * (x⁻¹ * b * x) = (x⁻¹ * b * x) * b := by
  classical
  obtain ⟨hYcyc, hY2, hYcard, hTI, -⟩ := center_facts h
  have hY4 : 4 ≤ Nat.card (critCenter D) := by
    rw [hYcard]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h.three_le
  have hQ2 : IsPGroup 2 Q := by
    rw [h.core_eq]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 M
  have hMN : M ≤ normalizer (Q : Set G) := by
    rw [h.core_eq]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 M
  have hB2 : IsPGroup 2 (conjugate (critCenter D) g) :=
    hY2.map (MulAut.conj g⁻¹).toMonoidHom
  have hS : IsPGroup 2 (conjugate (critCenter D) g ⊔ Q : Subgroup G) :=
    hB2.to_sup_of_normal_right' hQ2 (hgM.trans hMN)
  intro b hb x hx
  have hx' : conjugate (critCenter D) (g * x) ≤ conjugate (critCenter D) g ⊔ Q := by
    rw [← conjugate_conjugate]
    intro y hy
    rw [mem_conjugate_iff] at hy
    have h1 : x * y * x⁻¹ ∈ conjugate (critCenter D) g := hy
    have h2 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem (mem_sup_right hx)) (mem_sup_left h1)) (mem_sup_right hx)
  have hmem : x⁻¹ * b * x ∈ conjugate (critCenter D) (g * x) := by
    rw [← conjugate_conjugate, mem_conjugate_iff]
    simpa [mul_assoc] using hb
  exact CFSG.GF2Type.Aschbacher1976Common.commute_of_conjugate_le hYcyc hY2 hY4 hTI hS
    (g := g) (h := g * x) le_sup_left hx' b hb _ hmem

theorem false_of_conjugate_center_in_local
    {G : Type} [Group G] [Finite G] {M B Q : Subgroup G} {z : G} {D : Subgroup Q} {k u : ℕ}
    (h : Setup M B Q z D k u) {g : G} (hgM : conjugate (critCenter D) g ≤ M)
    (hgY : conjugate (critCenter D) g ≠ critCenter D) : False := by
  classical
  obtain ⟨hYcyc, hY2, hYcard, hTI, -⟩ := center_facts h
  obtain ⟨P, hPQ, hP4, hMNP, hMcP⟩ := exists_layer h
  have hk3 := h.three_le
  have hBcyc : IsCyclic (conjugate (critCenter D) g) :=
    isCyclic_of_surjective
      ((critCenter D).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).toMonoidHom (MulEquiv.surjective _)
  have hBcard : Nat.card (conjugate (critCenter D) g) = 2 ^ k := by
    rw [← hYcard]
    exact card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨y, hy⟩ := hBcyc.exists_generator
  have hyo : orderOf (y : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hBcard]
  have hdvd : 2 ^ (k - 3) ∣ orderOf (y : G) := hyo ▸ pow_dvd_pow 2 (by omega)
  have hbo : orderOf ((y : G) ^ 2 ^ (k - 3)) = 8 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hyo, Nat.pow_div (by omega) (by norm_num),
      show k - (k - 3) = 3 by omega]
  have hbB : (y : G) ^ 2 ^ (k - 3) ∈ conjugate (critCenter D) g := pow_mem y.2 _
  set b : G := (y : G) ^ 2 ^ (k - 3) with hb
  have hcent : ∀ x ∈ P, b ^ 4 * x = x * b ^ 4 :=
    pow_four_commute_of_commute_conj hP4 (hMNP (hgM hbB))
      (fun x hx => commute_conj_of_conjugate_le_local h hgM b hbB x (hPQ hx))
  have hb4Y : b ^ 4 ∈ critCenter D :=
    hMcP ⟨hgM (pow_mem hbB 4), mem_centralizer_iff.mpr fun x hx => (hcent x hx).symm⟩
  have hbot : critCenter D ⊓ conjugate (critCenter D) g = ⊥ := (hTI g).resolve_left hgY
  have hb4 : b ^ 4 = 1 := by
    have : b ^ 4 ∈ critCenter D ⊓ conjugate (critCenter D) g := ⟨hb4Y, pow_mem hbB 4⟩
    rw [hbot] at this
    exact this
  have := orderOf_dvd_of_pow_eq_one hb4
  rw [hbo] at this
  norm_num at this

end CFSG.GF2Type.Aschbacher1976HigherCenter
