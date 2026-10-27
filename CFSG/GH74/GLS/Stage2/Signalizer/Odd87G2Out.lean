module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Arith
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResG2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)


variable {F : Type} [Field F] [Finite F]

theorem g2_outer_involution_bad (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {α : MulAut (adjointGroup ReeTag.G2.tag F)} (hα : α ^ 2 = 1)
    (hnot : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →* MulAut (adjointGroup ReeTag.G2.tag F)).range) :
    ∃ K : Subgroup (adjointGroup ReeTag.G2.tag F), K ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      IsSimpleGroup ↥K ∧ (∃ x y : ↥K, x * y ≠ y * x) ∧ ∀ k : Kind, ¬ KindFactor k ↥K := by
  classical
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hodd
  have hF2 : ringChar F ≠ 2 := hchar ▸ hp2
  have h1 : ∀ x : ModGL ReeTag.G2.tag F, Units.map (entrywiseHom (1 : F ≃+* F).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hquad : ∀ {p' e : ℕ}, p'.Prime → 1 ≤ e → Nat.card F = (p' ^ e) ^ 2 → ∀ δ : F ≃+* F,
      (∀ c, δ c = c ^ (p' ^ e)) → ∀ (g : adjointGroup ReeTag.G2.tag F) (a : Fin ReeTag.G2.tag.rank → Fˣ),
      (∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) = (g : ModGL ReeTag.G2.tag F) *
        rootDiagUnit ReeTag.G2.tag a *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag F) * (rootDiagUnit ReeTag.G2.tag a)⁻¹ *
          (g : ModGL ReeTag.G2.tag F)⁻¹) →
      ∃ K : Subgroup (adjointGroup ReeTag.G2.tag F), K ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
        IsSimpleGroup ↥K ∧ (∃ x y : ↥K, x * y ≠ y * x) ∧ ∀ k : Kind, ¬ KindFactor k ↥K := by
    intro p' e hp' he hKe δ hδ g a hαg
    have hδ1 : δ ≠ 1 := by
      intro hδ1
      apply hnot
      refine ivk93res_inner_of_diag (g := g) (a := a) fun h => ?_
      rw [hαg h, hδ1, h1]
    obtain ⟨K, hK, hs, hn, hcardK⟩ := ivk93res_g2_quadratic hF2 hp' he hKe δ hδ hδ1 hαg hα
    refine ⟨K, hK, hs, hn, ?_⟩
    have hx3 : 3 ≤ p' ^ e := by
      by_contra hlt
      have h2 : p' ^ e ≤ 2 := by omega
      have h4 : (p' ^ e) ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    have hp'2 : p' ≠ 2 := by
      rintro rfl
      rw [hKe] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by norm_num)).2
        ((Nat.even_pow' (by omega)).2 even_two))
    exact quad_bad_numbers hp' hp'2 he hx3 hcardK
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F ReeTag.G2.prime := by
      have h := ringChar.charP F
      rw [hchar] at h
      exact h
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hcard hα with
      ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, rfl⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact hquad Nat.prime_three he hKe δ hδ g a hαg
    · have hb : 1 ≤ b := by
        by_contra hb0
        have hb0' : b = 0 := by omega
        subst hb0'
        simp at hfb
        subst hfb
        simp at hcard
        omega
      have hK' : Nat.card F = 3 ^ (2 * b + 1) := hfb ▸ hcard
      obtain ⟨K, hK, hs, hn, hcardK⟩ := ivk93res_g2_ree hb hK' hα
      exact ⟨K, hK, hs, hn, ree_bad_numbers hb hcardK⟩
  · rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inr (Or.inr ⟨rfl, by rw [hchar]; exact hp3⟩))
        hodd hα with ⟨g, a, hαg⟩ | ⟨p', e, hp', he, hKe, δ, hδ, g, a, hαg⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact hquad hp' he hKe δ hδ g a hαg

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
