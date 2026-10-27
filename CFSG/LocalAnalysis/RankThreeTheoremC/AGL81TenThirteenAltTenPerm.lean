module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open Equiv Equiv.Perm

theorem perm_apply_inv (f : Perm (Fin 10)) (x : Fin 10) : f (f⁻¹ x) = x := by
  rw [Perm.coe_inv]
  exact f.apply_symm_apply x

theorem perm_inv_apply (f : Perm (Fin 10)) (x : Fin 10) : f⁻¹ (f x) = x := by
  rw [Perm.coe_inv]
  exact f.symm_apply_apply x

theorem sign_eq_neg_one_of_involution {τ : Perm (Fin 10)} (h2 : τ ^ 2 = 1)
    (hfix : ∀ x, τ x ≠ x) : Perm.sign τ = -1 := by
  have hsupp : τ.support = Finset.univ := by
    ext x
    simp [mem_support, hfix x]
  have hall : ∀ n ∈ τ.cycleType, n = 2 := by
    intro n hn
    have h1 := two_le_of_mem_cycleType hn
    have h3 : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h4 := Nat.le_of_dvd (by norm_num) ((dvd_of_mem_cycleType hn).trans h3)
    omega
  have hrep : τ.cycleType = Multiset.replicate (Multiset.card τ.cycleType) 2 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  have hsum := sum_cycleType τ
  rw [hsupp, Finset.card_univ, Fintype.card_fin, hrep, Multiset.sum_replicate,
    smul_eq_mul] at hsum
  have hcard : Multiset.card τ.cycleType = 5 := by omega
  rw [sign_of_cycleType, hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    hcard]
  decide

theorem false_of_sq_eq_mul {B : Finset (Fin 10)} {g i c : Perm (Fin 10)}
    (hg : ∀ x, g x ∈ B ↔ x ∉ B) (hsg : Perm.sign g = 1)
    (hi : ∀ x, x ∉ B → i x = x) (hsi : Perm.sign i = 1)
    (hc : ∀ x, x ∈ B → c x = x) (h : g ^ 2 = i * c) : False := by
  have hcB : ∀ y, y ∉ B → c y ∉ B := by
    intro y hy hcy
    have h1 : c (c y) = c y := hc _ hcy
    exact hy (c.injective h1 ▸ hcy)
  have hcg : ∀ y, y ∉ B → c y = (g ^ 2) y := by
    intro y hy
    rw [h, Perm.mul_apply, hi _ (hcB y hy)]
  have hcinv : ∀ y, y ∉ B → c⁻¹ y = (g ^ 2)⁻¹ y := by
    intro y hy
    have hy' : c⁻¹ y ∉ B := by
      intro hm
      have h1 : c (c⁻¹ y) = c⁻¹ y := hc _ hm
      rw [perm_apply_inv] at h1
      exact hy (h1 ▸ hm)
    have h1 := hcg _ hy'
    rw [perm_apply_inv] at h1
    rw [Perm.eq_inv_iff_eq]
    exact h1.symm
  have hcinvB : ∀ x, x ∈ B → c⁻¹ x = x := by
    intro x hx
    have h1 := hc x hx
    rw [← h1, perm_inv_apply, h1]
  set τ := g * c⁻¹ with hτ
  have hτB : ∀ x, x ∈ B → τ x = g x := by
    intro x hx
    rw [hτ, Perm.mul_apply, hcinvB x hx]
  have hτBc : ∀ y, y ∉ B → τ y = g⁻¹ y := by
    intro y hy
    rw [hτ, Perm.mul_apply, hcinv y hy]
    rw [show (g ^ 2)⁻¹ = g⁻¹ * g⁻¹ by rw [pow_two, mul_inv_rev], Perm.mul_apply,
      perm_apply_inv]
  have hginvB : ∀ y, y ∉ B → g⁻¹ y ∈ B := by
    intro y hy
    by_contra hm
    have h1 := (hg (g⁻¹ y)).2 hm
    rw [perm_apply_inv] at h1
    exact hy h1
  have hτ2 : τ ^ 2 = 1 := by
    ext x
    rw [pow_two, Perm.mul_apply, Perm.one_apply]
    by_cases hx : x ∈ B
    · rw [hτB x hx, hτBc _ (fun hm => ((hg x).1 hm) hx), perm_inv_apply]
    · rw [hτBc x hx, hτB _ (hginvB x hx), perm_apply_inv]
  have hτfix : ∀ x, τ x ≠ x := by
    intro x hx
    by_cases hxB : x ∈ B
    · rw [hτB x hxB] at hx
      exact ((hg x).1 (by rw [hx]; exact hxB)) hxB
    · rw [hτBc x hxB] at hx
      exact hxB (hx ▸ hginvB x hxB)
  have hsτ := sign_eq_neg_one_of_involution hτ2 hτfix
  have hsc : Perm.sign c = 1 := by
    have h1 : c = i⁻¹ * g ^ 2 := by rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1, map_mul, map_inv, map_pow, hsi, hsg, one_pow, inv_one, one_mul]
  have hgτ : g = τ * c := by rw [hτ, mul_assoc, inv_mul_cancel, mul_one]
  rw [hgτ, map_mul, hsτ, hsc] at hsg
  exact absurd hsg (by decide)

theorem apply_mem_support_of_commute {c γ : Perm (Fin 10)} (h : Commute c γ) {z : Fin 10}
    (hz : z ∈ γ.support) : c z ∈ γ.support := by
  rw [mem_support] at hz ⊢
  intro h1
  apply hz
  apply c.injective
  have h2 := DFunLike.congr_fun h.eq z
  simp only [Perm.mul_apply] at h2
  rw [h2, h1]

theorem fix_of_commute_range {B : Finset (Fin 10)} (hB : B.card = 5) {c : Perm (Fin 10)}
    (hc : ∀ k ∈ (alternatingGroup.ofSubtype B).range, Commute c (k : Perm (Fin 10))) :
    ∀ x ∈ B, c x = x := by
  intro x hx
  by_contra hne
  set y := c x with hy
  have h4 : 2 ≤ ((B.erase y).erase x).card := by
    have h1 : (B.erase y).card ≥ 4 := by
      have := Finset.card_erase_le (s := B) (a := y)
      have h2 := Finset.pred_card_le_card_erase (s := B) (a := y)
      omega
    have hxy : x ∈ B.erase y := Finset.mem_erase.2 ⟨fun h => hne h.symm, hx⟩
    rw [Finset.card_erase_of_mem hxy]
    omega
  obtain ⟨t, htsub, htc⟩ := Finset.exists_subset_card_eq h4
  set s := insert x t with hs
  have hxt : x ∉ t := fun h => (Finset.mem_erase.1 (htsub h)).1 rfl
  have hsc : s.card = 3 := by rw [hs, Finset.card_insert_of_notMem hxt, htc]
  have hsB : s ⊆ B := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hx
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 (htsub hz)).2).2
  have hys : y ∉ s := by
    intro hm
    rcases Finset.mem_insert.1 hm with h1 | h1
    · exact hne h1
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 (htsub h1)).2).1 rfl
  obtain ⟨γ, hγ, hγs⟩ := CFSG.AlternatingAutomorphism.exists_isThreeCycle_support_eq hsc
  have hγA : γ ∈ alternatingGroup (Fin 10) := hγ.mem_alternatingGroup
  have hγr : (⟨γ, hγA⟩ : alternatingGroup (Fin 10)) ∈ (alternatingGroup.ofSubtype B).range := by
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    exact hγs ▸ hsB
  have hcom := hc _ hγr
  have hxs : x ∈ γ.support := by rw [hγs]; exact Finset.mem_insert_self x t
  have := apply_mem_support_of_commute hcom hxs
  rw [hγs] at this
  exact hys this

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
