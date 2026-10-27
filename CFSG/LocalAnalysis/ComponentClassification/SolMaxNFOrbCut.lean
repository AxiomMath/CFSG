module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbRel

public section

namespace CFSG.ComponentClassification.SolMax.NFOrb

open Equiv

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem iff_or_iff_not_of_rel_eq {f g : ι → Prop} (x₀ : ι)
    (h : ∀ p q, (f p ↔ f q) ↔ (g p ↔ g q)) : (∀ p, f p ↔ g p) ∨ ∀ p, f p ↔ ¬ g p := by
  by_cases h₀ : f x₀ ↔ g x₀
  · left
    intro p
    have := h p x₀
    tauto
  · right
    intro p
    have := h p x₀
    tauto

theorem exists_ne_four (h5 : 5 ≤ Fintype.card ι) (a b c d : ι) :
    ∃ p : ι, p ≠ a ∧ p ≠ b ∧ p ≠ c ∧ p ≠ d := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, d} : Finset ι)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨p, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

@[expose] def cutRel (side : ι → Prop) (z y : ι) : Set (ι × ι) :=
  {x | side (swap z y x.1) ↔ side (swap z y x.2)}

theorem cutRel_injective (h5 : 5 ≤ Fintype.card ι) {side : ι → Prop} {z y z' y' : ι}
    (hz : side z) (hy : ¬ side y) (hz' : side z') (hy' : ¬ side y')
    (h : cutRel side z y = cutRel side z' y') : z = z' ∧ y = y' := by
  have hrel : ∀ p q, (side (swap z y p) ↔ side (swap z y q)) ↔
      (side (swap z' y' p) ↔ side (swap z' y' q)) := fun p q => by
    have := congrArg (fun S : Set (ι × ι) => (p, q) ∈ S) h
    exact iff_of_eq this
  have hzy : z ≠ y := fun h => hy (h ▸ hz)
  have hzy' : z ≠ y' := fun h => hy' (h ▸ hz)
  have hyz' : y ≠ z' := fun h => hy (h ▸ hz')
  rcases iff_or_iff_not_of_rel_eq z hrel with h1 | h1
  · constructor
    · by_contra hzz
      have := h1 z
      rw [swap_apply_left, swap_apply_of_ne_of_ne hzz hzy'] at this
      exact hy (this.mpr hz)
    · by_contra hyy
      have := h1 y
      rw [swap_apply_right, swap_apply_of_ne_of_ne hyz' hyy] at this
      exact hy (this.mp hz)
  · exfalso
    obtain ⟨p, hpz, hpy, hpz', hpy'⟩ := exists_ne_four h5 z y z' y'
    have := h1 p
    rw [swap_apply_of_ne_of_ne hpz hpy, swap_apply_of_ne_of_ne hpz' hpy'] at this
    tauto

theorem cutRel_ne (h4 : 4 ≤ Fintype.card ι) {side : ι → Prop} {z y : ι} (hz : side z)
    (hy : ¬ side y) : {x : ι × ι | side x.1 ↔ side x.2} ≠ cutRel side z y := by
  intro h
  have hrel : ∀ p q, (side p ↔ side q) ↔ (side (swap z y p) ↔ side (swap z y q)) := fun p q => by
    have := congrArg (fun S : Set (ι × ι) => (p, q) ∈ S) h
    exact iff_of_eq this
  have hzy : z ≠ y := fun h => hy (h ▸ hz)
  rcases iff_or_iff_not_of_rel_eq z hrel with h1 | h1
  · have := h1 z
    rw [swap_apply_left] at this
    exact hy (this.mp hz)
  · obtain ⟨x, y₁, hxy, hxz, hxy', -, -⟩ := exists_two_notMem h4 z y
    · have := h1 x
      rw [swap_apply_of_ne_of_ne hxz hxy'] at this
      tauto

variable {t : ι → ι → Perm Ω}

theorem false_of_cut [Fintype Ω] [DecidableEq Ω] (ht : ∀ c d e, t c d * t d e = t c e)
    (hs : ∀ c d, t c d = t d c) (h5 : 5 ≤ Fintype.card ι)
    (hΩ : Fintype.card Ω ≤ 2 * Fintype.card ι + 3)
    (hequiv : ∀ τ ∈ alternatingGroup ι, ∃ π : Perm Ω, ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d))
    {ω : Ω} {a b a' b' : ι} (hab : t a b ω ≠ ω) (hcut : ∀ x, t a x ω = ω ∨ t b x ω = ω)
    (ha' : a' ≠ a) (haa' : t a a' ω = ω) (hb' : b' ≠ b) (hbb' : t b b' ω = ω) : False := by
  classical
  set side : ι → Prop := fun x => t a x ω = ω with hside
  have hrel : ∀ p q, t p q ω = ω ↔ (side p ↔ side q) := by
    intro p q
    constructor
    · intro h
      constructor
      · intro hp
        exact pair_fix_trans ht hp h
      · intro hq
        exact pair_fix_trans ht hq (by rw [hs]; exact h)
    · intro h
      by_cases hp : side p
      · have hq := h.mp hp
        exact pair_fix_trans ht (by rw [hs]; exact hp) hq
      · have hq : ¬ side q := fun hq => hp (h.mpr hq)
        have hbp := (hcut p).resolve_left hp
        have hbq := (hcut q).resolve_left hq
        exact pair_fix_trans ht (by rw [hs]; exact hbp) hbq
  have hsa : side a := by simp only [hside, pair_self ht, Perm.one_apply]
  have hsb : ¬ side b := hab
  have hsa' : side a' := haa'
  have hsb' : ¬ side b' := fun h => hab ((hrel a b).mpr ⟨fun _ => absurd h
    (fun h' => ((hrel b b').mp hbb').mpr h' |> fun h'' => hsb h''), fun h'' => absurd h'' hsb⟩)
  set B := Finset.univ.filter side with hB
  set B' := Finset.univ.filter fun x => ¬ side x with hB'
  have hBB' : B.card + B'.card = Fintype.card ι := Finset.card_filter_add_card_filter_not _
  have hB2 : 2 ≤ B.card := by
    have : ({a, a'} : Finset ι) ⊆ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hB, hsa, hsa']
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair (Ne.symm ha')] at h2
  have hB'2 : 2 ≤ B'.card := by
    have : ({b, b'} : Finset ι) ⊆ B' := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hB', hsb, hsb']
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair (Ne.symm hb')] at h2
  have hrealize : ∀ z ∈ B, ∀ y ∈ B', ∃ ω₁ ω₂ : Ω, pairRel t ω₁ = cutRel side z y ∧
      pairRel t ω₂ = cutRel side z y ∧ ω₁ ≠ ω₂ := by
    intro z hz y hy
    simp only [hB, hB', Finset.mem_filter, Finset.mem_univ, true_and] at hz hy
    have hzy : z ≠ y := fun h => hy (h ▸ hz)
    obtain ⟨u, v, huv, hside_uv, huz, huy, hvz, hvy⟩ : ∃ u v : ι, u ≠ v ∧ (side u ↔ side v) ∧
        u ≠ z ∧ u ≠ y ∧ v ≠ z ∧ v ≠ y := by
      obtain ⟨p₁, p₂, h12, h1z, h1y, h2z, h2y⟩ := exists_two_notMem (by omega) z y
      obtain ⟨p₃, h3z, h3y, h31, h32⟩ := exists_ne_four h5 z y p₁ p₂
      by_cases e12 : side p₁ ↔ side p₂
      · exact ⟨p₁, p₂, h12, e12, h1z, h1y, h2z, h2y⟩
      by_cases e13 : side p₁ ↔ side p₃
      · exact ⟨p₁, p₃, Ne.symm h31, e13, h1z, h1y, h3z, h3y⟩
      · exact ⟨p₂, p₃, Ne.symm h32, by tauto, h2z, h2y, h3z, h3y⟩
    set τ := swap z y * swap u v with hτ
    have hτA : τ ∈ alternatingGroup ι := swap_mul_swap_mem_alternatingGroup hzy huv
    obtain ⟨π, hπ⟩ := hequiv τ hτA
    have hτinv : ∀ p, side (τ⁻¹ p) ↔ side (swap z y p) := by
      intro p
      rw [hτ, mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply]
      set q := swap z y p
      by_cases hqu : q = u
      · rw [hqu, swap_apply_left]
        exact hside_uv.symm
      by_cases hqv : q = v
      · rw [hqv, swap_apply_right]
        exact hside_uv
      rw [swap_apply_of_ne_of_ne hqu hqv]
    have hR : pairRel t (π ω) = cutRel side z y := by
      ext ⟨p, q⟩
      change t p q (π ω) = π ω ↔ (side (swap z y p) ↔ side (swap z y q))
      have h1 := pair_fix_conj hπ (τ⁻¹ p) (τ⁻¹ q) ω
      rw [perm_apply_inv, perm_apply_inv] at h1
      rw [h1, hrel, hτinv, hτinv]
    refine ⟨π ω, t (τ a) (τ b) (π ω), hR, by rw [pairRel_apply ht hs, hR], fun h => ?_⟩
    exact hab ((pair_fix_conj hπ a b ω).mp h.symm)
  set R₀ : Set (ι × ι) := {x | side x.1 ↔ side x.2} with hR₀
  have hpR₀ : pairRel t ω = R₀ := by
    ext ⟨p, q⟩
    exact hrel p q
  set S := insert R₀ ((B ×ˢ B').image fun x => cutRel side x.1 x.2) with hS
  have hinj : Set.InjOn (fun x : ι × ι => cutRel side x.1 x.2) (B ×ˢ B' : Finset (ι × ι)) := by
    rintro ⟨z, y⟩ hzy ⟨z', y'⟩ hzy' h
    simp only [hB, hB', Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ,
      true_and, Set.mem_ofPred_eq] at hzy hzy'
    obtain ⟨h1, h2⟩ := cutRel_injective h5 hzy.1 hzy.2 hzy'.1 hzy'.2 h
    rw [h1, h2]
  have hR₀S : R₀ ∉ (B ×ˢ B').image fun x => cutRel side x.1 x.2 := by
    intro h
    obtain ⟨⟨z, y⟩, hzy, hEq⟩ := Finset.mem_image.mp h
    simp only [hB, hB', Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hzy
    exact cutRel_ne (by omega) hzy.1 hzy.2 hEq.symm
  have hScard : S.card = B.card * B'.card + 1 := by
    rw [hS, Finset.card_insert_of_notMem hR₀S, Finset.card_image_of_injOn hinj,
      Finset.card_product]
  have hcount := card_mul_le_of_fibre (pairRel t) S (k := 2) (fun R hR => by
    rw [hS, Finset.mem_insert, Finset.mem_image] at hR
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    rcases hR with rfl | ⟨⟨z, y⟩, hzy, rfl⟩
    · refine ⟨ω, by simp [hpR₀], t a b ω, ?_, fun h => hab h.symm⟩
      simp [pairRel_apply ht hs, hpR₀]
    · rw [Finset.mem_product] at hzy
      obtain ⟨ω₁, ω₂, h₁, h₂, h12⟩ := hrealize z hzy.1 y hzy.2
      exact ⟨ω₁, by simp [h₁], ω₂, by simp [h₂], h12⟩)
  rw [hScard] at hcount
  obtain ⟨x, hx⟩ : ∃ x, B.card = x + 2 := ⟨B.card - 2, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y, B'.card = y + 2 := ⟨B'.card - 2, by omega⟩
  rw [hx, hy] at hcount hBB'
  have : (x + 2) * (y + 2) = x * y + (2 * x + 2 * y + 4) := by ring
  rw [this] at hcount
  omega

end CFSG.ComponentClassification.SolMax.NFOrb
