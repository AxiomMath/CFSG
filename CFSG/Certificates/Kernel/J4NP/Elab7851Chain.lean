module

public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.KC.J4NP

open Classical

variable {G : Type*} [Group G]

noncomputable def posF (K : Subgroup G) (pos : G → ℕ) (M : ℕ) (H : Set G) : Finset ℕ :=
  (Finset.range M).filter fun p => ∃ b ∈ H, b ∉ K ∧ pos b = p

theorem mem_posF {K : Subgroup G} {pos : G → ℕ} {M : ℕ} {H : Set G} {p : ℕ} :
    p ∈ posF K pos M H ↔ p < M ∧ ∃ b ∈ H, b ∉ K ∧ pos b = p := by
  simp [posF]

theorem posF_mono {K : Subgroup G} {pos : G → ℕ} {M : ℕ} {H H' : Set G} (h : H ⊆ H') :
    posF K pos M H ⊆ posF K pos M H' := by
  intro p hp
  rw [mem_posF] at hp ⊢
  obtain ⟨hM, b, hb, hbK, rfl⟩ := hp
  exact ⟨hM, b, h hb, hbK, rfl⟩

structure ChainHyp (A K : Subgroup G) (pos : G → ℕ) (M : ℕ) : Prop where
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  sq : ∀ x ∈ A, x * x = 1
  lt : ∀ g ∈ A, g ∉ K → pos g < M
  pos_eq : ∀ g ∈ A, ∀ h ∈ A, g ∉ K → h ∉ K → (pos g = pos h ↔ g⁻¹ * h ∈ K)

@[expose] def ClosedIn (A : Subgroup G) (H : Set G) : Prop :=
  H ⊆ A ∧ (1 : G) ∈ H ∧ ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H

theorem inv_eq_of_sq {x : G} (h : x * x = 1) : x⁻¹ = x := by
  rw [inv_eq_iff_mul_eq_one, h]

theorem closedIn_union {A : Subgroup G} {K : Subgroup G} {pos : G → ℕ} {M : ℕ}
    (hc : ChainHyp A K pos M) {H : Set G} (hH : ClosedIn A H) {y : G} (hy : y ∈ A) :
    ClosedIn A (H ∪ (fun h => y * h) '' H) := by
  obtain ⟨hHA, h1, hmul⟩ := hH
  refine ⟨?_, Or.inl h1, ?_⟩
  · rintro x (hx | ⟨h, hh, rfl⟩)
    · exact hHA hx
    · exact A.mul_mem hy (hHA hh)
  · rintro a (ha | ⟨h, hh, rfl⟩) b (hb | ⟨h', hh', rfl⟩)
    · exact Or.inl (hmul a ha b hb)
    · refine Or.inr ⟨a * h', hmul a ha h' hh', ?_⟩
      change y * (a * h') = a * (y * h')
      rw [← mul_assoc, ← mul_assoc, hc.comm y hy a (hHA ha)]
    · refine Or.inr ⟨h * b, hmul h hh b hb, ?_⟩
      change y * (h * b) = y * h * b
      rw [mul_assoc]
    · refine Or.inl ?_
      have e : y * h * (y * h') = h * h' := by
        calc y * h * (y * h') = y * (h * y) * h' := by group
          _ = y * (y * h) * h' := by rw [hc.comm h (hHA hh) y hy]
          _ = (y * y) * h * h' := by group
          _ = h * h' := by rw [hc.sq y hy, one_mul]
      rw [e]
      exact hmul h hh h' hh'

theorem chain {A K : Subgroup G} {pos : G → ℕ} {M : ℕ} (hc : ChainHyp A K pos M)
    (P : Finset ℕ → Prop) (h0 : P ∅)
    (hstep : ∀ H : Set G, ClosedIn A H → ∀ g ∈ A, g ∉ K →
      (∀ p ∈ posF K pos M H, p < pos g) → P (posF K pos M H) →
        P (posF K pos M (H ∪ (fun h => g * h) '' H))) :
    ∀ B : Set G, ClosedIn A B → P (posF K pos M B) := by
  suffices H : ∀ n, ∀ B : Set G, ClosedIn A B → (posF K pos M B).card ≤ n → P (posF K pos M B) from
    fun B hB => H _ B hB le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB hn
  rcases (posF K pos M B).eq_empty_or_nonempty with he | hne
  · rw [he]
    exact h0
  set m := (posF K pos M B).max' hne with hm
  have hmB : m ∈ posF K pos M B := Finset.max'_mem _ hne
  obtain ⟨-, g, hgB, hgK, hgm⟩ := mem_posF.mp hmB
  have hgA : g ∈ A := hB.1 hgB
  let F : Set G → Prop := fun H => ClosedIn A H ∧ H ⊆ B ∧ m ∉ posF K pos M H
  have hF1 : F {1} := by
    refine ⟨⟨?_, rfl, ?_⟩, ?_, ?_⟩
    · rintro x rfl
      exact A.one_mem
    · rintro a rfl b rfl
      simp
    · rintro x rfl
      exact hB.2.1
    · rw [mem_posF]
      rintro ⟨-, b, rfl, hbK, -⟩
      exact hbK K.one_mem
  have inner : ∀ k, ∀ H, F H → (posF K pos M B \ posF K pos M H).card ≤ k →
      ∃ H, F H ∧ posF K pos M B ⊆ posF K pos M (H ∪ (fun h => g * h) '' H) := by
    intro k
    induction k with
    | zero =>
      intro H hH hk
      refine ⟨H, hH, fun p hp => ?_⟩
      have : p ∈ posF K pos M H := by
        by_contra hpH
        have := Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpH⟩⟩
        omega
      exact posF_mono Set.subset_union_left this
    | succ k ihk =>
      intro H hH hk
      by_cases hcov : posF K pos M B ⊆ posF K pos M (H ∪ (fun h => g * h) '' H)
      · exact ⟨H, hH, hcov⟩
      obtain ⟨q, hqB, hqn⟩ := Finset.not_subset.mp hcov
      obtain ⟨hqM, y, hyB, hyK, rfl⟩ := mem_posF.mp hqB
      have hyA : y ∈ A := hB.1 hyB
      have hHA := hH.1.1
      set H' := H ∪ (fun h => y * h) '' H with hH'
      have hqH : pos y ∉ posF K pos M H := fun h =>
        hqn (posF_mono Set.subset_union_left h)
      have hF' : F H' := by
        refine ⟨closedIn_union hc hH.1 hyA, ?_, ?_⟩
        · rintro x (hx | ⟨h, hh, rfl⟩)
          · exact hH.2.1 hx
          · exact hB.2.2 y hyB h (hH.2.1 hh)
        · rw [mem_posF]
          rintro ⟨-, b, hb, hbK, hbm⟩
          rcases hb with hb | ⟨h, hh, rfl⟩
          · exact hH.2.2 (mem_posF.mpr ⟨by rw [← hbm]; exact hc.lt b (hHA hb) hbK, b, hb, hbK, hbm⟩)
          ·
            have hhA : h ∈ A := hHA hh
            have hyhA : y * h ∈ A := A.mul_mem hyA hhA
            have e1 : (y * h)⁻¹ * g ∈ K := (hc.pos_eq _ hyhA g hgA hbK hgK).mp (by rw [hbm, hgm])
            have e2 : y⁻¹ * (g * h) = (y * h)⁻¹ * g := by
              rw [mul_inv_rev, inv_eq_of_sq (hc.sq h hhA)]
              calc y⁻¹ * (g * h) = y⁻¹ * (h * g) := by rw [hc.comm g hgA h hhA]
                _ = h * y⁻¹ * g := by
                  rw [← mul_assoc, hc.comm y⁻¹ (A.inv_mem hyA) h hhA]
            have hghK : g * h ∉ K := by
              intro hgh
              apply hyK
              have : y⁻¹ ∈ K := by
                have key : y⁻¹ = (y⁻¹ * (g * h)) * (g * h)⁻¹ := by group
                rw [key]
                exact K.mul_mem (e2 ▸ e1) (K.inv_mem hgh)
              simpa using K.inv_mem this
            have hpos : pos y = pos (g * h) :=
              (hc.pos_eq y hyA (g * h) (A.mul_mem hgA hhA) hyK hghK).mpr (e2 ▸ e1)
            exact hqn (mem_posF.mpr ⟨hqM, g * h, Or.inr ⟨h, hh, rfl⟩, hghK, hpos.symm⟩)
      refine ihk H' hF' ?_
      have hsub : posF K pos M B \ posF K pos M H' ⊂ posF K pos M B \ posF K pos M H := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff (subset_refl _)
          (posF_mono Set.subset_union_left)) |>.mpr ⟨pos y, Finset.mem_sdiff.mpr ⟨hqB, hqH⟩, ?_⟩
        intro h
        apply (Finset.mem_sdiff.mp h).2
        rw [mem_posF]
        exact ⟨hqM, y * 1, Or.inr ⟨1, hH.1.2.1, rfl⟩, by simpa using hyK, by simp⟩
      have := Finset.card_lt_card hsub
      omega
  obtain ⟨H, ⟨hHc, hHB, hmH⟩, hcov⟩ := inner _ {1} hF1 le_rfl
  have hHsub : posF K pos M H ⊆ (posF K pos M B).erase m := fun p hp =>
    Finset.mem_erase.mpr ⟨fun h => hmH (h ▸ hp), posF_mono hHB hp⟩
  have hlt : ∀ p ∈ posF K pos M H, p < pos g := by
    intro p hp
    have h1 := Finset.mem_erase.mp (hHsub hp)
    have h2 := Finset.le_max' _ p h1.2
    rw [← hm] at h2
    rw [hgm]
    omega
  have hcard : (posF K pos M H).card < n := by
    have := Finset.card_le_card hHsub
    rw [Finset.card_erase_of_mem hmB] at this
    have := Finset.card_pos.mpr hne
    omega
  have hPH := ih _ hcard H hHc le_rfl
  have hPB := hstep H hHc g hgA hgK hlt hPH
  have heq : posF K pos M (H ∪ (fun h => g * h) '' H) = posF K pos M B := by
    refine Finset.Subset.antisymm (posF_mono ?_) hcov
    rintro x (hx | ⟨h, hh, rfl⟩)
    · exact hHB hx
    · exact hB.2.2 g hgB h (hHB hh)
  rwa [heq] at hPB

end CFSG.KC.J4NP

end
