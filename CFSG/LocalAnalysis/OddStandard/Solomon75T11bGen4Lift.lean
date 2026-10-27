module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataSylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bGen4Defs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS AhatData

namespace AhatData

@[expose] def Gen4Good (n : ℕ) (Q : Subgroup (Perm (Fin n))) : Prop :=
  ∀ H : Subgroup (Perm (Fin n)), H ≤ Q →
    (∃ s : Finset (Perm (Fin n)), s.card ≤ 3 ∧
      Subgroup.closure (s : Set (Perm (Fin n))) = H) ∨
    (∃ s : Finset (Perm (Fin n)), s.card ≤ 4 ∧
      Subgroup.closure (s : Set (Perm (Fin n))) = H ∧ ∃ u ∈ H, DblI u)

variable {n : ℕ}

theorem Gen4Good.conj {Q : Subgroup (Perm (Fin n))} (h : Gen4Good n Q) (g : Perm (Fin n)) :
    Gen4Good n (conjSub g Q) := by
  classical
  intro H hH
  have hH' : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have := hH hx
    rw [mem_conjSub] at this
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hback :
      (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
    rw [Subgroup.map_map]
    have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  have hclos : ∀ s : Finset (Perm (Fin n)),
      Subgroup.closure ((s.image (MulAut.conj g).toMonoidHom : Finset (Perm (Fin n))) :
        Set _) =
        (Subgroup.closure (s : Set (Perm (Fin n)))).map (MulAut.conj g).toMonoidHom := by
    intro s
    rw [MonoidHom.map_closure]
    simp [Finset.coe_image]
  rcases h _ hH' with ⟨s, hs, hcl⟩ | ⟨s, hs, hcl, u, hu, hdbl⟩
  · refine Or.inl ⟨s.image (MulAut.conj g).toMonoidHom, (Finset.card_image_le).trans hs, ?_⟩
    rw [hclos, hcl, hback]
  · refine Or.inr ⟨s.image (MulAut.conj g).toMonoidHom, (Finset.card_image_le).trans hs, ?_,
      g * u * g⁻¹, ?_, ?_⟩
    · rw [hclos, hcl, hback]
    · rw [← hback]
      exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
    · exact dblI_conj.2 hdbl

theorem CoverCtx.gen4 {K : Type} [Group K] [Finite K] {S : Subgroup K} (X : CoverCtx n K S)
    (hQ : Gen4Good n X.Q) {H : Subgroup K} (hH : H ≤ S) :
    ∃ s : Finset K, s.card ≤ 4 ∧ Subgroup.closure (s : Set K) = H := by
  classical
  have hZ2 : Nat.card (center K) = 2 := X.C.hX.2.1
  obtain ⟨z, hzZ, hz1, hZ⟩ :
      ∃ z : K, z ∈ center K ∧ z ≠ 1 ∧ ∀ y ∈ center K, y = 1 ∨ y = z := by
    rw [Nat.card_eq_two_iff' (1 : ↥(center K))] at hZ2
    obtain ⟨y, hy1, hy⟩ := hZ2
    refine ⟨y, y.2, fun h => hy1 (Subtype.ext h), fun w hw => ?_⟩
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val (hy ⟨w, hw⟩ (fun h => hw1 (congrArg Subtype.val h))))
  have hHb : H.map X.C.ρ ≤ X.Q := X.map_le hH
  have lift : ∀ sb : Finset (Perm (Fin n)),
      Subgroup.closure (sb : Set (Perm (Fin n))) = H.map X.C.ρ →
      ∃ t : Finset K, t.card ≤ sb.card ∧ (↑t : Set K) ⊆ H ∧
        (Subgroup.closure (t : Set K)).map X.C.ρ = H.map X.C.ρ := by
    intro sb hsb
    have hmem : ∀ b ∈ sb, ∃ a ∈ H, X.C.ρ a = b := fun b hb => by
      have : b ∈ H.map X.C.ρ := hsb ▸ Subgroup.subset_closure hb
      exact this
    choose! g hgH hgρ using hmem
    refine ⟨sb.image g, Finset.card_image_le, ?_, ?_⟩
    · intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      exact hgH b hb
    · rw [MonoidHom.map_closure, ← hsb]
      congr 1
      ext x
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
        rw [hgρ b hb]
        exact hb
      · intro hx
        exact ⟨g x, ⟨x, hx, rfl⟩, hgρ x hx⟩
  have decomp : ∀ t : Finset K, (↑t : Set K) ⊆ H →
      (Subgroup.closure (t : Set K)).map X.C.ρ = H.map X.C.ρ →
      ∀ h ∈ H, ∃ l ∈ Subgroup.closure (t : Set K), l⁻¹ * h ∈ center K := by
    intro t htH hmap h hh
    have : X.C.ρ h ∈ (Subgroup.closure (t : Set K)).map X.C.ρ := by
      rw [hmap]; exact ⟨h, hh, rfl⟩
    obtain ⟨l, hl, hlh⟩ := this
    refine ⟨l, hl, ?_⟩
    rw [← X.C.ρ_eq_one_iff, map_mul, map_inv, hlh, inv_mul_cancel]
  have closure_le : ∀ t : Finset K, (↑t : Set K) ⊆ H → Subgroup.closure (t : Set K) ≤ H :=
    fun t htH => (Subgroup.closure_le H).2 htH
  rcases hQ _ hHb with ⟨sb, hsb, hcl⟩ | ⟨sb, hsb, hcl, u, hu, hdbl⟩
  · obtain ⟨t, ht, htH, htmap⟩ := lift sb hcl
    by_cases hzH : z ∈ H
    · refine ⟨insert z t, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hzH
        · exact htH hx
      · intro h hh
        obtain ⟨l, hl, hlh⟩ := decomp t htH htmap h hh
        have hc : l⁻¹ * h ∈ Subgroup.closure (↑(insert z t) : Set K) := by
          rcases hZ _ hlh with h1 | h1
          · rw [h1]; exact one_mem _
          · rw [h1]; exact Subgroup.subset_closure (by simp)
        have hl' : l ∈ Subgroup.closure (↑(insert z t) : Set K) :=
          Subgroup.closure_mono (by intro x hx; simp [hx]) hl
        have := mul_mem hl' hc
        simpa using this
    · refine ⟨t, ht.trans (by omega), ?_⟩
      apply le_antisymm (closure_le t htH)
      intro h hh
      obtain ⟨l, hl, hlh⟩ := decomp t htH htmap h hh
      have hlH : l ∈ H := closure_le t htH hl
      have hc : l⁻¹ * h ∈ H := mul_mem (inv_mem hlH) hh
      rcases hZ _ hlh with h1 | h1
      · have : h = l := by
          have := h1
          rw [inv_mul_eq_one] at this
          exact this.symm
        rw [this]; exact hl
      · exact absurd (h1 ▸ hc) hzH
  · obtain ⟨t, ht, htH, htmap⟩ := lift sb hcl
    have hzL : z ∈ H → z ∈ Subgroup.closure (t : Set K) := by
      intro hzH
      by_contra hzL
      have : u ∈ (Subgroup.closure (t : Set K)).map X.C.ρ := by
        rw [htmap]; exact hu
      obtain ⟨l, hl, hlu⟩ := this
      have hl2 : l * l ∈ center K := by
        rw [← X.C.ρ_eq_one_iff, map_mul, hlu]
        exact hdbl.1
      have hl2L : l * l ∈ Subgroup.closure (t : Set K) := mul_mem hl hl
      rcases hZ _ hl2 with h1 | h1
      · exact X.hD l (by rw [hlu]; exact hdbl) h1
      · exact hzL (h1 ▸ hl2L)
    refine ⟨t, ht.trans hsb, ?_⟩
    apply le_antisymm (closure_le t htH)
    intro h hh
    obtain ⟨l, hl, hlh⟩ := decomp t htH htmap h hh
    have hlH : l ∈ H := closure_le t htH hl
    have hc : l⁻¹ * h ∈ H := mul_mem (inv_mem hlH) hh
    rcases hZ _ hlh with h1 | h1
    · have : h = l := by
        have := h1
        rw [inv_mul_eq_one] at this
        exact this.symm
      rw [this]; exact hl
    · have hzH : z ∈ H := h1 ▸ hc
      have hzL' := hzL hzH
      have : h = l * (l⁻¹ * h) := by group
      rw [this]
      exact mul_mem hl (h1 ▸ hzL')

theorem exists_coverCtx_conj_gen4 {K : Type} [Group K] [Finite K] [NeZero n] (hn : 8 ≤ n)
    (hn' : n ≤ 11) (hK : IsDoubleCoverOfAlt K n)
    (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128) (hgood : SylowGood n (P0 n))
    (S : Sylow 2 K) :
    ∃ (X : CoverCtx n K (S : Subgroup K)) (g : Perm (Fin n)), X.Q = conjSub g (P0 n) := by
  let C := CoverSetup.ofCover hK
  obtain ⟨g, hg⟩ := exists_conj_comap hn hn' hK C hP0 S
  obtain ⟨a, -, b, -, c, -, ha, hb, hc, h2, h3⟩ := hgood.eight
  refine ⟨⟨C, conjSub g (P0 n), ?_, hg, hgood.conj g, hn', ?_, ?_, ?_⟩, g, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_conj_mem.1 hx
    have hy' := P0_le_alternatingGroup hn hn' hy
    rw [Perm.mem_alternatingGroup] at hy' ⊢
    simp [Perm.sign_mul, hy']
  · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP0]
  · exact fun x hx => C.isoI_sq_eq_one hn hn' ⟨a, b, c, ha, hb, hc, h2, h3⟩ hx
  · exact fun x hx => C.dblI_sq_ne_one hn hx

theorem sylowGen4_of_good [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11)
    (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128) (hgood : SylowGood n (P0 n))
    (hg4 : Gen4Good n (P0 n)) : CFSG.OddStandard.Solomon75.SylowGen4 n := by
  intro K _ _ hK S H hHS
  obtain ⟨X, g, hg⟩ := exists_coverCtx_conj_gen4 hn hn' hK hP0 hgood S
  exact X.gen4 (hg ▸ hg4.conj g) hHS

end AhatData

end CFSG.OddStandard.Solomon75
