module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Link
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Prof

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

section Link

variable {G : Type} [Group G] [Finite G] {K₁ L T : Subgroup G} {s : G}

theorem link5b_aut (h : Sol78Link5bData K₁ L T s) (hK : CFSG.IsQuasisimple ↥K₁) (hne : K₁ ≠ L) :
    K₁ ≤ L ∧ ∃ σ : MulAut ↥L, σ ≠ 1 ∧ σ * σ = 1 ∧
      (∀ x : ↥L, ((σ x : ↥L) : G) = s * x * s⁻¹) ∧ ∀ k : ↥L, (k : G) ∈ K₁ → σ k = k := by
  obtain ⟨hs, hKL, hs2, hsK, hsL⟩ :=
    Hyp.link5b_setup hK hne h.L_comp h.s_sq h.K_comp h.incl.1 h.link
  set σ : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨s, hs⟩ with hσ
  have hσapp : ∀ l : ↥L, ((σ l : ↥L) : G) = s * l * s⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hs⟩ l
  refine ⟨hKL, σ, ?_, ?_, hσapp, ?_⟩
  · intro h1
    apply hsL
    rw [mem_centralizer_iff]
    intro l hl
    have h2 := hσapp ⟨l, hl⟩
    rw [h1] at h2
    have h3 : l = s * l * s⁻¹ := h2
    calc l * s = (s * l * s⁻¹) * s := by rw [← h3]
      _ = s * l := by group
  · ext l
    have h4 : (l : G) * s ^ 2 = s ^ 2 * l := mem_centralizer_iff.1 hs2 l l.2
    have e1 : (((σ * σ) l : ↥L) : G) = s * (s * (l : G) * s⁻¹) * s⁻¹ := by
      rw [MulAut.mul_apply, hσapp, hσapp]
    have e2 : (((1 : MulAut ↥L) l : ↥L) : G) = l := rfl
    show (((σ * σ) l : ↥L) : G) = (((1 : MulAut ↥L) l : ↥L) : G)
    rw [e1, e2]
    have h4' : (l : G) * (s * s) = (s * s) * l := by rw [← pow_two]; exact h4
    calc s * (s * (l : G) * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
      _ = (l * (s * s)) * (s * s)⁻¹ := by rw [h4']
      _ = l := by group
  · intro k hk
    apply Subtype.ext
    rw [hσapp]
    have h5 : (k : G) * s = s * k := mem_centralizer_iff.1 hsK k hk
    calc s * (k : G) * s⁻¹ = (k * s) * s⁻¹ := by rw [h5]
      _ = k := by group

end Link

section Profile

variable {K : Type} [Group K]

theorem not_lamProfile_of_fixesElem {n b : ℕ} (ab : Prop) (hK : InvolutionFixesElem K n)
    (hbn : b < n) : ∀ α : MulAut K, α ≠ 1 → α * α = 1 →
      ¬ Hyp.LamProfile ab b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
        ((∃ k : K, α = MulAut.conj k) → ¬ Hyp.LamProfile ab b ↥(fixSubgroup α)) :=
  fun α h1 h2 => ⟨fun hL => not_elemBound_fixProd hK hbn h1 h2 hL.2.1,
    fun _ hL => not_elemBound_fixSubgroup hK hbn h1 h2 hL.2.1⟩

theorem not_lamProfile_of_nonsolvable (b : ℕ) (ab : Prop)
    (hK : ∀ α : MulAut K, α ≠ 1 → α * α = 1 → ¬ Group.IsSolvable ↥(fixSubgroup α)) :
    ∀ α : MulAut K, α ≠ 1 → α * α = 1 →
      ¬ Hyp.LamProfile ab b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
        ((∃ k : K, α = MulAut.conj k) → ¬ Hyp.LamProfile ab b ↥(fixSubgroup α)) :=
  fun α h1 h2 => ⟨fun hL => by
      have := hL.1
      exact hK α h1 h2 (Group.isSolvable_of_isSolvable_injective
        (inl_injective' ↥(fixSubgroup α) (Multiplicative (ZMod 2)))),
    fun _ hL => by
      have := hL.1
      exact hK α h1 h2 this⟩

end Profile

end CFSG.EvenSporadicStandard.Induction
