module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorLines
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne

public section

namespace CFSG.AGLEmbedding

open Subgroup

section ClassTwo

variable {D : Type*} [Group D] [Finite D]

open scoped IsMulCommutative

theorem exists_isMulCommutative_of_lineTransitive {A : Type*} [CommGroup A] [Finite A] {s : ℕ}
    [Fact s.Prime] (hs5 : s ≠ 5) (hA : ∀ a : A, a ^ 5 = 1) (hAcard : Nat.card A = 5 ^ 2)
    (hD : ∀ d : D, d ^ s = 1) (hc : commutator D ≤ center D) (ψ : A →* MulAut D)
    (hψ : ∃ a, ψ a ≠ 1) (Γ : Set (MulAut A × MulAut D))
    (hΓ : ∀ g ∈ Γ, ∀ a, g.2 * ψ a = ψ (g.1 a) * g.2)
    (htrans : ∀ F F' : Subgroup A, F.index = 5 → F'.index = 5 →
      ∃ g ∈ Γ, F.map g.1.toMonoidHom = F') :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have hs : s.Prime := Fact.out
  have h5 : Nat.Prime 5 := by norm_num
  by_cases hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z
  · have hcomm : IsMulCommutative (D ⧸ center D) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
    let ρ : MulAut D →* MulAut (D ⧸ center D) := quotientCenterAut
    let _ : MulDistribMulAction A (D ⧸ center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
    have hV : ∀ v : D ⧸ center D, v ^ s = 1 := fun v => by
      induction v using QuotientGroup.induction_on with
      | H d => rw [← QuotientGroup.mk_pow, hD, QuotientGroup.mk_one]
    have hnt : ∃ (a : A) (v : D ⧸ center D), a • v ≠ v := by
      obtain ⟨a, ha⟩ := hψ
      obtain ⟨d, hd⟩ : ∃ d : D, ψ a d ≠ d := by
        by_contra h
        push Not at h
        exact ha (MulEquiv.ext h)
      refine ⟨a, d, fun h => hd (apply_eq_of_mk_apply_eq ((Nat.coprime_primes h5 hs).mpr
        (Ne.symm hs5)) hD ?_ (hZ a) h)⟩
      rw [← map_pow, hA a, map_one]
    have hcompat : ∀ (f : MulAut D) (α : MulAut A), (∀ a, f * ψ a = ψ (α a) * f) →
        ∀ (a : A) (v : D ⧸ center D), ρ f (a • v) = α a • ρ f v := fun f α hf a v => by
      change (ρ f * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ f) v
      rw [← map_mul, ← map_mul, hf]
    obtain ⟨F, hFinj, hFidx, hne⟩ := exists_four_lines_fixedPiece hs5 hA hAcard hV
      ((fun g => ((g.1, ρ g.2) : MulAut A × MulAut (D ⧸ center D))) '' Γ) (by
        rintro _ ⟨g, hg, rfl⟩ a v
        exact hcompat g.2 g.1 (hΓ g hg) a v) (by
        intro F F' hF hF'
        obtain ⟨g, hg, hgF⟩ := htrans F F' hF hF'
        exact ⟨(g.1, ρ g.2), ⟨g, hg, rfl⟩, hgF⟩) hnt
    obtain ⟨v, hv, hcard⟩ := exists_orthogonal_of_injective hs5 hA hV (commPairing hc)
      (fun a v w => commPairing_aut hc (hZ a) v w) (commPairing_self hc) hFinj hFidx hne
    obtain ⟨E, hE, hEcard⟩ := exists_isMulCommutative_of_commPairing hc v hv
    exact ⟨E, hE, hcard.trans hEcard⟩
  · push Not at hZ
    obtain ⟨a, z, hz, haz⟩ := hZ
    let ρ : MulAut D →* MulAut (center D) := MulAut.characteristic (center D)
    let _ : MulDistribMulAction A (center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
    have hcompat : ∀ (f : MulAut D) (α : MulAut A), (∀ a, f * ψ a = ψ (α a) * f) →
        ∀ (a : A) (v : center D), ρ f (a • v) = α a • ρ f v := fun f α hf a v => by
      change (ρ f * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ f) v
      rw [← map_mul, ← map_mul, hf]
    obtain ⟨F, hFinj, hFidx, hne⟩ := exists_four_lines_fixedPiece hs5 hA hAcard
      (fun z => Subtype.ext (hD z))
      ((fun g => ((g.1, ρ g.2) : MulAut A × MulAut (center D))) '' Γ) (by
        rintro _ ⟨g, hg, rfl⟩ a v
        exact hcompat g.2 g.1 (hΓ g hg) a v) (by
        intro F F' hF hF'
        obtain ⟨g, hg, hgF⟩ := htrans F F' hF hF'
        exact ⟨(g.1, ρ g.2), ⟨g, hg, rfl⟩, hgF⟩)
      ⟨a, ⟨z, hz⟩, fun h => haz (congrArg Subtype.val h)⟩
    obtain ⟨v, -, hcard⟩ := exists_orthogonal_of_injective hs5 hA
      (fun z => Subtype.ext (hD z)) (1 : center D →* center D →* center D)
      (fun _ _ _ => rfl) (fun _ => rfl) hFinj hFidx hne
    refine ⟨(closure (Set.range v)).map (center D).subtype, ⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x', -, hx'⟩ := x.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx']; exact
        (mem_center_iff.mp x'.2 y).symm)
    · rwa [card_map_of_injective (center D).subtype_injective]

end ClassTwo

end CFSG.AGLEmbedding
