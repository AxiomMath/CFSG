module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Tools
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Six

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma seg27_odd_dvd_sixty {n : ℕ} (hn : n ∣ 60) (hodd : ¬ 2 ∣ n) (hge : 10 ≤ n) :
    n = 15 := by
  have hle : n ≤ 60 := Nat.le_of_dvd (by norm_num) hn
  interval_cases n <;> norm_num at *

private lemma seg27_dvd_fifteen_eq {m : ℕ} (hm : m ∣ 15) (hge : 6 ≤ m) (hle : m ≤ 8) :
    False := by
  interval_cases m <;> norm_num at hm

theorem seg27_case2 {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))} {p q : Fin 8}
    (h₀ : Seg27Six X₀ p q) (h₁ : Seg27Six X₁ p q) : ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  set Z : Subgroup (Equiv.Perm (Fin 8)) := X₀ ⊓ X₁
  have hX₀C : X₀ ≤ seg27AltFix ({p, q} : Set (Fin 8)) := by
    intro g hg
    rw [seg27_mem_altFix]
    refine ⟨h₀.le_alt hg, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₀.fix_p g hg
    · exact h₀.fix_q g hg
  have hX₁C : X₁ ≤ seg27AltFix ({p, q} : Set (Fin 8)) := by
    intro g hg
    rw [seg27_mem_altFix]
    refine ⟨h₁.le_alt hg, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₁.fix_p g hg
    · exact h₁.fix_q g hg
  have hcardC : Nat.card (seg27AltFix ({p, q} : Set (Fin 8))) = 360 :=
    seg27_card_altFix_two h₀.ne
  have hprod : 60 * 60 ≤ 360 * Nat.card Z := by
    have h := seg27_card_mul_card_le (A := X₀) (B := X₁)
      (C := seg27AltFix ({p, q} : Set (Fin 8))) hX₀C hX₁C
    rw [h₀.card, h₁.card, hcardC] at h
    exact h
  have hZge : 10 ≤ Nat.card Z := by omega
  have hZdvd : Nat.card Z ∣ 60 := by
    have h := Subgroup.card_dvd_of_le (H := Z) (K := X₀) inf_le_left
    rwa [h₀.card] at h
  by_cases h2 : 2 ∣ Nat.card Z
  · obtain ⟨g, hg, hg2⟩ := seg27_exists_orderOf_two Z h2
    exact ⟨g, hg, hg2⟩
  · exfalso
    have hn15 : Nat.card Z = 15 := seg27_odd_dvd_sixty hZdvd h2 hZge
    obtain ⟨h, hhZ, hh5⟩ :=
      seg27_exists_orderOf_prime Z Nat.prime_five (by rw [hn15]; norm_num)
    have hp : h p = p := h₀.fix_p h hhZ.1
    have hq : h q = q := h₀.fix_q h hhZ.1
    obtain ⟨o, hop, hoq, _hoo, hfix3⟩ :=
      seg27_exists_third_fixed_of_orderOf_five hh5 h₀.ne hp hq
    have hZo : ∀ z ∈ Z, z o = o := by
      intro z hzZ
      by_contra hzo
      have hzp : z p = p := h₀.fix_p z hzZ.1
      have hzq : z q = q := h₀.fix_q z hzZ.1
      have hzox : h (z o) ≠ z o := by
        intro hfix
        rcases hfix3 (z o) hfix with h1 | h1 | h1
        · exact hop (z.injective (h1.trans hzp.symm))
        · exact hoq (z.injective (h1.trans hzq.symm))
        · exact hzo h1
      have hmem : ∀ x : Fin 8, x ≠ p → x ≠ q → x ∈ MulAction.orbit Z o := by
        intro x hxp hxq
        by_cases hxo : x = o
        · rw [hxo]
          exact MulAction.mem_orbit_self o
        · have hxx : h x ≠ x := by
            intro hfix
            rcases hfix3 x hfix with h1 | h1 | h1
            · exact hxp h1
            · exact hxq h1
            · exact hxo h1
          obtain ⟨n, hn⟩ := seg27_exists_pow_eq_of_orderOf_five hh5 hzox hxx
          refine MulAction.mem_orbit_iff.mpr
            ⟨⟨(h ^ n) * z, Z.mul_mem (Z.pow_mem hhZ n) hzZ⟩, ?_⟩
          show ((h ^ n) * z) o = x
          rw [Equiv.Perm.mul_apply, hn]
      have hTsub : (Set.univ \ ({p, q} : Set (Fin 8))) ⊆ MulAction.orbit Z o := by
        intro x hx
        simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at hx
        exact hmem x hx.1 hx.2
      have hTcard : (Set.univ \ ({p, q} : Set (Fin 8))).ncard = 6 := by
        rw [Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, Set.ncard_pair h₀.ne]
        simp [Nat.card_eq_fintype_card]
      have horb_ge : 6 ≤ (MulAction.orbit Z o).ncard := by
        rw [← hTcard]
        exact Set.ncard_le_ncard hTsub (Set.toFinite _)
      have horb_le : (MulAction.orbit Z o).ncard ≤ 8 := by
        simpa [Nat.card_eq_fintype_card] using Set.ncard_le_card (MulAction.orbit Z o)
      have hmdvd : (MulAction.orbit Z o).ncard ∣ Nat.card Z := by
        rw [← MulAction.index_stabilizer Z o]
        exact Subgroup.index_dvd_card (H := MulAction.stabilizer Z o)
      have hmdvd15 : (MulAction.orbit Z o).ncard ∣ 15 := by
        rw [hn15] at hmdvd
        exact hmdvd
      exact seg27_dvd_fifteen_eq hmdvd15 horb_ge horb_le
    have hZle : Z ≤ X₀ ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) o := by
      intro z hz
      exact ⟨hz.1, MulAction.mem_stabilizer_iff.2 (by
        simpa [Equiv.Perm.smul_def] using hZo z hz)⟩
    have hcard10 : Nat.card (X₀ ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) o :
        Subgroup (Equiv.Perm (Fin 8))) = 10 :=
      h₀.card_stab o hop hoq
    have hle10 : Nat.card Z ≤ 10 := by
      have h := Subgroup.card_le_of_le hZle
      rwa [hcard10] at h
    omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
