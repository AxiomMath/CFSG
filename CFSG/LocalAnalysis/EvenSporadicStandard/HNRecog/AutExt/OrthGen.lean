module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthFin
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm Section3

variable {G : Type} [Group G]

theorem pi_surj {K M : Subgroup G} (hM : IsElemTwo 4 M)
    {S : Fin 2 → Set G} (hS : IsOrbitPartition K {x | x ∈ M ∧ x ≠ 1} S)
    (h0 : Nat.card ↥(S 0) = 5) (h1 : Nat.card ↥(S 1) = 10)
    {s : Fin 5 → G} (hs' : ∀ x ∈ S 0, ∃ i, s i = x)
    {ρ : ↥K →* Perm (Fin 5)} {π : Fv5 → G} (hπM : ∀ f, π f ∈ M)
    (hπadd : ∀ f g, π (f + g) = π f * π g) (hπs : ∀ i, π (Pi.single i 1) = s i)
    (hπconj : ∀ (l : ↥K) (f : Fv5), (l : G) * π f * (l : G)⁻¹ = π (fv5Act (ρ l) f)) :
    ∀ x ∈ M, ∃ f : Fv5, π f = x := by
  have hzero : π 0 = 1 := by
    have h : π 0 = π 0 * π 0 := by simpa using hπadd 0 0
    exact (mul_left_cancel ((mul_one (π 0)).trans h)).symm
  let N : Subgroup G :=
    { carrier := {x | ∃ f : Fv5, π f = x}
      one_mem' := ⟨0, hzero⟩
      mul_mem' := by
        rintro x y ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f + g, hπadd f g⟩
      inv_mem' := by
        rintro x ⟨f, rfl⟩
        refine ⟨f, ?_⟩
        have h2 : π f * π f = 1 := by rw [← hπadd f f, fv5_add_self, hzero]
        exact (inv_eq_of_mul_eq_one_right h2).symm }
  have hNM : N ≤ M := by
    rintro x ⟨f, rfl⟩
    exact hπM f
  have hS0N : S 0 ⊆ N := by
    intro x hx
    obtain ⟨i, hi⟩ := hs' x hx
    exact ⟨Pi.single i 1, by rw [hπs i, hi]⟩
  have hconjN : ∀ (l : ↥K) {x : G}, x ∈ N → (l : G) * x * (l : G)⁻¹ ∈ N := by
    rintro l x ⟨f, rfl⟩
    exact ⟨fv5Act (ρ l) f, (hπconj l f).symm⟩
  have hS1N : S 1 ⊆ N := by
    intro y hy
    by_contra hyN
    have hdisj : ∀ z, z ∈ S 1 → z ∈ N → False := by
      intro z hz hzN
      obtain ⟨k, hk, hk'⟩ := (hS.orbit 1).transitive z hz y hy
      have hkN : k * z * k⁻¹ ∈ N := hconjN ⟨k, hk⟩ hzN
      rw [hk'] at hkN
      exact hyN hkN
    have h1notS0 : (1 : G) ∉ S 0 := by
      intro h1S0
      exact (hS.subset 0 h1S0).2 rfl
    have hfin0 : (S 0).Finite :=
      Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero (by rw [h0]; norm_num))
    have hNset : (N : Set G) = insert (1 : G) (S 0) := by
      apply Set.Subset.antisymm
      · intro n hnN
        by_cases hn1 : n = 1
        · exact Set.mem_insert_iff.2 (Or.inl hn1)
        · have hnM : n ∈ M := hNM hnN
          obtain ⟨i, hi⟩ := hS.cover n ⟨hnM, hn1⟩
          fin_cases i
          · exact Set.mem_insert_iff.2 (Or.inr hi)
          · exact (hdisj n hi hnN).elim
      · intro n hn
        rcases Set.mem_insert_iff.1 hn with rfl | hn0
        · exact N.one_mem
        · exact hS0N hn0
    have hcardN : Nat.card ↥N = 6 := by
      calc Nat.card ↥N
          = Nat.card ↥(insert (1 : G) (S 0)) := Nat.card_congr (Set.equivOfEq hNset)
        _ = (insert (1 : G) (S 0)).ncard := Nat.card_coe_set_eq _
        _ = (S 0).ncard + 1 := Set.ncard_insert_of_notMem h1notS0 hfin0
        _ = Nat.card ↥(S 0) + 1 := by rw [Nat.card_coe_set_eq]
        _ = 6 := by rw [h0]
    have hdvd : Nat.card ↥N ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hNM
    rw [hcardN, hM.2] at hdvd
    norm_num at hdvd
  have hMN : M ≤ N := by
    intro x hxM
    by_cases hx1 : x = 1
    · rw [hx1]; exact N.one_mem
    · obtain ⟨i, hi⟩ := hS.cover x ⟨hxM, hx1⟩
      fin_cases i
      · exact hS0N hi
      · exact hS1N hi
  intro x hxM
  exact hMN hxM

theorem pi_one_vec {K M : Subgroup G}
    {S : Fin 2 → Set G} (hS : IsOrbitPartition K {x | x ∈ M ∧ x ≠ 1} S)
    (h0 : Nat.card ↥(S 0) = 5) (h1 : Nat.card ↥(S 1) = 10)
    {ρ : ↥K →* Perm (Fin 5)} {π : Fv5 → G} (hπM : ∀ f, π f ∈ M)
    (hπconj : ∀ (l : ↥K) (f : Fv5), (l : G) * π f * (l : G)⁻¹ = π (fv5Act (ρ l) f)) :
    π fv5One = 1 := by
  by_contra hPne
  have hPmem : π fv5One ∈ M := hπM fv5One
  have hfix : ∀ l : ↥K, (l : G) * π fv5One * (l : G)⁻¹ = π fv5One := by
    intro l
    rw [hπconj l fv5One, fv5Act_one_vec]
  obtain ⟨i, hi⟩ := hS.cover (π fv5One) ⟨hPmem, hPne⟩
  have hSsing : S i = {π fv5One} := by
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨hi, ?_⟩
    intro c hc
    obtain ⟨k, hk, hk'⟩ := (hS.orbit i).transitive (π fv5One) hi c hc
    have hkc : k * π fv5One * k⁻¹ = π fv5One := hfix ⟨k, hk⟩
    rw [hkc] at hk'
    exact hk'.symm
  have hcard1 : Nat.card ↥(S i) = 1 := by
    haveI : Subsingleton ↥(S i) := ⟨fun a b => by
      apply Subtype.ext
      have ha : (a : G) = π fv5One := by simpa [hSsing] using a.2
      have hb : (b : G) = π fv5One := by simpa [hSsing] using b.2
      rw [ha, hb]⟩
    haveI : Nonempty ↥(S i) := ⟨⟨π fv5One, hi⟩⟩
    exact Nat.card_unique
  by_cases hi0 : i = 0
  · rw [hi0] at hcard1
    rw [h0] at hcard1
    exact absurd hcard1 (by norm_num)
  · have hi1 : i = 1 := by
      apply Fin.ext
      have hne : (i : ℕ) ≠ 0 := fun hv => hi0 (Fin.ext (by simpa using hv))
      omega
    rw [hi1] at hcard1
    rw [h1] at hcard1
    exact absurd hcard1 (by norm_num)

end CFSG.EvenSporadicStandard.HNRecog.Section4
