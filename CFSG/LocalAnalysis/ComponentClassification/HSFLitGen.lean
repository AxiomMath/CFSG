module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ComponentClassification.HSFLit

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_finset_closure_eq_or_pow_le [Finite G] (H : Subgroup G) (m : ℕ) :
    ∃ s : Finset G, (s : Set G) ⊆ H ∧ s.card ≤ m ∧
      (closure (s : Set G) = H ∨ 2 ^ m ≤ Nat.card (closure (s : Set G))) := by
  classical
  induction m with
  | zero => exact ⟨∅, by simp, by simp, Or.inr (by simp)⟩
  | succ m ih =>
    obtain ⟨s, hsH, hs, h⟩ := ih
    by_cases hc : closure (s : Set G) = H
    · exact ⟨s, hsH, hs.trans (Nat.le_succ m), Or.inl hc⟩
    · rcases h with h | h
      · exact absurd h hc
      have hle : closure (s : Set G) ≤ H := (closure_le H).mpr hsH
      obtain ⟨g, hgH, hgs⟩ : ∃ g ∈ H, g ∉ closure (s : Set G) := by
        by_contra hne
        push Not at hne
        exact hc (le_antisymm hle hne)
      refine ⟨insert g s, ?_, ?_, Or.inr ?_⟩
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hgH, hsH⟩
      · exact (Finset.card_insert_le g s).trans (Nat.succ_le_succ hs)
      · have hlt : closure (s : Set G) < closure ((insert g s : Finset G) : Set G) := by
          refine lt_of_le_of_ne (closure_mono (by simp)) fun heq => hgs ?_
          rw [heq]
          exact subset_closure (by simp)
        have hdvd : Nat.card (closure (s : Set G)) ∣
            Nat.card (closure ((insert g s : Finset G) : Set G)) :=
          Subgroup.card_dvd_of_le hlt.le
        have hne : Nat.card (closure (s : Set G)) ≠
            Nat.card (closure ((insert g s : Finset G) : Set G)) := fun he =>
          hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le he.symm.le)
        obtain ⟨c, hc'⟩ := hdvd
        have hpos : 0 < Nat.card (closure ((insert g s : Finset G) : Set G)) := Nat.card_pos
        have hc2 : 2 ≤ c := by
          rcases c with _ | _ | c
          · rw [hc', mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
          · exact absurd (by rw [hc']; simp) hne
          · omega
        rw [hc', pow_succ]
        exact Nat.mul_le_mul h hc2

theorem exists_finset_closure_eq_of_card_le [Finite G] (H : Subgroup G) {k : ℕ}
    (hk : Nat.card H ≤ 2 ^ k) :
    ∃ s : Finset G, s.card ≤ k ∧ closure (s : Set G) = H := by
  obtain ⟨s, hsH, hs, h⟩ := exists_finset_closure_eq_or_pow_le H k
  refine ⟨s, hs, ?_⟩
  rcases h with h | h
  · exact h
  · have hle : closure (s : Set G) ≤ H := (closure_le H).mpr hsH
    exact Subgroup.eq_of_le_of_card_ge hle (hk.trans h)

theorem exists_finset_closure_eq_of_map {G' : Type*} [Group G'] (f : G →* G') (H : Subgroup G)
    {a b : ℕ} {s : Finset G'} (hs : s.card ≤ a) (hsH : closure (s : Set G') = H.map f)
    {r : Finset G} (hr : r.card ≤ b) (hrH : closure (r : Set G) = H ⊓ f.ker) :
    ∃ u : Finset G, u.card ≤ a + b ∧ closure (u : Set G) = H := by
  classical
  have hpre : ∀ y ∈ s, ∃ x ∈ H, f x = y := by
    intro y hy
    have : y ∈ H.map f := hsH ▸ subset_closure hy
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, hx, rfl⟩
  choose! g hgH hgf using hpre
  have hgle : closure ((s.image g : Finset G) : Set G) ≤ H := by
    rw [closure_le, Finset.coe_image]
    rintro _ ⟨y, hy, rfl⟩
    exact hgH y hy
  refine ⟨s.image g ∪ r, (Finset.card_union_le _ _).trans
    (add_le_add (Finset.card_image_le.trans hs) hr), le_antisymm ?_ ?_⟩
  · rw [closure_le, Finset.coe_union]
    rintro x (hx | hx)
    · exact hgle (subset_closure hx)
    · have : x ∈ H ⊓ f.ker := hrH ▸ subset_closure hx
      exact this.1
  · intro h hh
    have himg : f '' ((s.image g : Finset G) : Set G) = s := by
      rw [Finset.coe_image, ← Set.image_comp]
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        rw [Function.comp_apply, hgf y' hy']
        exact hy'
      · intro hy
        exact ⟨y, hy, hgf y hy⟩
    have h1 : f h ∈ (closure ((s.image g : Finset G) : Set G)).map f := by
      rw [MonoidHom.map_closure, himg, hsH]
      exact ⟨h, hh, rfl⟩
    obtain ⟨w, hw, hwf⟩ := h1
    have hk : w⁻¹ * h ∈ closure (r : Set G) := by
      rw [hrH]
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hgle hw)) hh, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwf, inv_mul_cancel]
    rw [show h = w * (w⁻¹ * h) by group]
    refine mul_mem (closure_mono ?_ hw) (closure_mono ?_ hk)
    · rw [Finset.coe_union]
      exact Set.subset_union_left
    · rw [Finset.coe_union]
      exact Set.subset_union_right

theorem exists_finset_closure_eq_of_isCyclic (H : Subgroup G) [IsCyclic H] :
    ∃ s : Finset G, s.card ≤ 1 ∧ closure (s : Set G) = H := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨{(g : G)}, by simp, le_antisymm ?_ ?_⟩
  · rw [closure_le, Finset.coe_singleton, Set.singleton_subset_iff]
    exact g.2
  · intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨h, hh⟩)
    rw [Finset.coe_singleton]
    have : (h : G) = (g : G) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [this]
    exact zpow_mem (subset_closure (Set.mem_singleton _)) k

theorem exists_finset_closure_eq_of_sylow [Finite G] {k : ℕ} (S : Sylow 2 G)
    (h : ∀ U : Subgroup G, U ≤ S → ∃ s : Finset G, s.card ≤ k ∧ closure (s : Set G) = U)
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    ∃ s : Finset G, s.card ≤ k ∧ closure (s : Set G) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ hp)
  obtain ⟨s, hs, hsP⟩ := h _ hle
  refine ⟨s.image (MulAut.conj g⁻¹).toMonoidHom, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsP, Subgroup.map_map]
  convert Subgroup.map_id P using 2
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end CFSG.ComponentClassification.HSFLit
