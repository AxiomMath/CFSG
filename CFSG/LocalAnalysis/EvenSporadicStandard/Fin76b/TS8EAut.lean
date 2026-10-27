module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem central_aut_inner {G : Type} [Group G] [Finite G] {E : Subgroup G} {t : G}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htE : t ∈ E)
    (hcomm : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 ∨ e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = t)
    (hcen : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t)
    (hcard : Nat.card E = 32)
    (hgen : ∃ a b c d : G, Subgroup.closure ({a, b, c, d} : Set G) = E)
    {f : G} (hf : f ∈ normalizer (E : Set G))
    (hc : ∀ x ∈ E, f * x * f⁻¹ = x ∨ f * x * f⁻¹ = t * x) :
    ∃ e' ∈ E, ∀ x ∈ E, f * x * f⁻¹ = e' * x * e'⁻¹ := by
  classical
  have htt : ∀ y : G, t * (t * y) = y := fun y => by rw [← mul_assoc, ht2, one_mul]
  let N : Subgroup (MulAut ↥E) :=
    { carrier := {φ | ∀ x : ↥E, (φ x : G) = x ∨ (φ x : G) = t * x}
      mul_mem' := by
        intro φ ψ hφ hψ x
        rw [MulAut.mul_apply]
        rcases hψ x with h1 | h1
        · have : ψ x = x := Subtype.ext h1
          rw [this]; exact hφ x
        · rcases hφ (ψ x) with h2 | h2
          · right; rw [h2]; exact h1
          · left; rw [h2, h1, htt]
      one_mem' := fun x => Or.inl rfl
      inv_mem' := by
        intro φ hφ x
        have h1 := hφ (φ⁻¹ x)
        rw [MulAut.apply_inv_self] at h1
        rcases h1 with h1 | h1
        · left; exact h1.symm
        · right
          calc ((φ⁻¹ x : ↥E) : G) = t * (t * ((φ⁻¹ x : ↥E) : G)) := (htt _).symm
            _ = t * x := by rw [← h1] }
  obtain ⟨a, b, c, d, hgenE⟩ := hgen
  have hmemE : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg => hgenE ▸ subset_closure hg
  have ha := hmemE a (by simp)
  have hb := hmemE b (by simp)
  have hc' := hmemE c (by simp)
  have hd := hmemE d (by simp)
  have key : ∀ (φ ψ : N) (g : G) (hg : g ∈ E),
      (((φ.1 ⟨g, hg⟩ : ↥E) : G) = g ↔ ((ψ.1 ⟨g, hg⟩ : ↥E) : G) = g) →
        φ.1 ⟨g, hg⟩ = ψ.1 ⟨g, hg⟩ := by
    intro φ ψ g hg hiff
    have htg : t * g ≠ g := fun hh => ht1 (mul_right_cancel (hh.trans (one_mul g).symm))
    apply Subtype.ext
    rcases φ.2 ⟨g, hg⟩ with h1 | h1 <;> rcases ψ.2 ⟨g, hg⟩ with h2 | h2
    · rw [h1, h2]
    · exact absurd (h2.symm.trans (hiff.1 h1)) htg
    · exact absurd (h1.symm.trans (hiff.2 h2)) htg
    · rw [h1, h2]
  let β : N → Bool × Bool × Bool × Bool := fun φ =>
    (decide (((φ.1 ⟨a, ha⟩ : ↥E) : G) = a), decide (((φ.1 ⟨b, hb⟩ : ↥E) : G) = b),
      decide (((φ.1 ⟨c, hc'⟩ : ↥E) : G) = c), decide (((φ.1 ⟨d, hd⟩ : ↥E) : G) = d))
  have hβinj : Function.Injective β := by
    intro φ ψ hφψ
    simp only [β, Prod.mk.injEq, decide_eq_decide] at hφψ
    obtain ⟨h1, h2, h3, h4⟩ := hφψ
    have hgens : ∀ g (hg : g ∈ ({a, b, c, d} : Set G)),
        φ.1 ⟨g, hmemE g hg⟩ = ψ.1 ⟨g, hmemE g hg⟩ := by
      intro g hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact key φ ψ g (hmemE g (by simp)) h1
      · exact key φ ψ g (hmemE g (by simp)) h2
      · exact key φ ψ g (hmemE g (by simp)) h3
      · exact key φ ψ g (hmemE g (by simp)) h4
    have hall : ∀ x (hx : x ∈ Subgroup.closure ({a, b, c, d} : Set G)),
        φ.1 ⟨x, hgenE ▸ hx⟩ = ψ.1 ⟨x, hgenE ▸ hx⟩ := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact hgens x hx
      | one => rw [show (⟨1, _⟩ : ↥E) = 1 from rfl, map_one, map_one]
      | mul x y hx hy ihx ihy =>
        rw [show (⟨x * y, _⟩ : ↥E) = ⟨x, hgenE ▸ hx⟩ * ⟨y, hgenE ▸ hy⟩ from rfl, map_mul, map_mul,
          ihx, ihy]
      | inv x hx ih =>
        rw [show (⟨x⁻¹, _⟩ : ↥E) = (⟨x, hgenE ▸ hx⟩ : ↥E)⁻¹ from rfl, map_inv, map_inv, ih]
    apply Subtype.ext
    refine MulEquiv.ext fun e => ?_
    have := hall e.1 (hgenE ▸ e.2)
    exact this
  have hNcard : Nat.card N ≤ 16 := by
    have := Nat.card_le_card_of_injective β hβinj
    simpa [Nat.card_prod] using this
  let ι : ↥E →* MulAut ↥E := MulAut.conj
  have hrange_le : ι.range ≤ N := by
    rintro _ ⟨e, rfl⟩ x
    have h1 := hcomm e e.2 x x.2
    have hx : ((MulAut.conj e x : ↥E) : G) = e * x * e⁻¹ := rfl
    rw [hx]
    rcases h1 with h1 | h1
    · left; exact mul_inv_eq_one.1 h1
    · right; exact mul_inv_eq_iff_eq_mul.1 h1
  have hker : Nat.card ι.ker ≤ 2 := by
    have hmem : ∀ k : ι.ker, ((k.1 : ↥E) : G) = 1 ∨ ((k.1 : ↥E) : G) = t := by
      intro k
      refine hcen (k.1 : ↥E) (k.1 : ↥E).2 fun y hy => ?_
      have h1 := MonoidHom.mem_ker.1 k.2
      have h2 := congrArg (fun m : MulAut ↥E => ((m ⟨y, hy⟩ : ↥E) : G)) h1
      simp only [MulAut.one_apply] at h2
      have h3 : ((k.1 : ↥E) : G) * y * ((k.1 : ↥E) : G)⁻¹ = y := h2
      calc y * ((k.1 : ↥E) : G) = ((k.1 : ↥E) : G) * y * ((k.1 : ↥E) : G)⁻¹ * ((k.1 : ↥E) : G) := by
            rw [h3]
        _ = ((k.1 : ↥E) : G) * y := by group
    let g : ι.ker → Bool := fun k => decide (((k.1 : ↥E) : G) = 1)
    have hg : Function.Injective g := by
      intro k₁ k₂ hk
      simp only [g, decide_eq_decide] at hk
      apply Subtype.ext
      apply Subtype.ext
      rcases hmem k₁ with h1 | h1 <;> rcases hmem k₂ with h2 | h2
      · rw [h1, h2]
      · exact absurd (h2.symm.trans (hk.1 h1)) ht1
      · exact absurd (h1.symm.trans (hk.2 h2)) ht1
      · rw [h1, h2]
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have hrange : 16 ≤ Nat.card ι.range := by
    have h1 := Subgroup.card_mul_index ι.ker
    rw [Subgroup.index_ker, hcard] at h1
    have := Nat.mul_le_mul_right (Nat.card ι.range) hker
    omega
  have hfinN : Finite (MulAut ↥E) := Finite.of_injective (fun φ : MulAut ↥E => (φ : ↥E → ↥E))
    (fun φ ψ h => DFunLike.coe_injective h)
  have hrangeN : ι.range = N :=
    Subgroup.eq_of_le_of_card_ge hrange_le (hNcard.trans hrange)
  have hfN : E.normalizerMonoidHom ⟨f, hf⟩ ∈ N := by
    intro x
    exact hc x x.2
  rw [← hrangeN] at hfN
  obtain ⟨e', he'⟩ := hfN
  refine ⟨(e' : G), e'.2, fun x hx => ?_⟩
  have h1 := congrArg (fun m : MulAut ↥E => ((m ⟨x, hx⟩ : ↥E) : G)) he'
  exact h1.symm

end CFSG.EvenSporadicStandard.Fin76b
