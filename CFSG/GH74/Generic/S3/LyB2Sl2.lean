module

public import CFSG.GH74.Generic.S3.LyB2Dickson
public import CFSG.GH74.Generic.S3.LyB2Exc

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.BenderSuzuki.MatrixGroups Subgroup

theorem center_eq_bot_of_simple_nonab {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem false_of_exc_quotient
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {S₁ : Type} [Group S₁]
    (ρ : S₁ →* PSL2MatrixGroup F) (hρ : ∀ g ∈ ρ.ker, g ∈ center S₁) (P : Subgroup S₁)
    {K₀ : Type} [Group K₀] (hK₀ : IsExcB2 K₀) (φ : P →* K₀) (hφ : Function.Surjective φ) : False := by
  obtain ⟨hsim, hnab, hord⟩ := hK₀.simple_quotient
  have hfin : Finite (K₀ ⧸ center K₀) :=
    Nat.finite_of_card_ne_zero (by rcases hord with h | h | h | h | h <;> omega)
  let ψ₀ : P →* K₀ ⧸ center K₀ := (QuotientGroup.mk' (center K₀)).comp φ
  have hψ₀ : Function.Surjective ψ₀ := (QuotientGroup.mk'_surjective _).comp hφ
  let ρP : P →* PSL2MatrixGroup F := ρ.comp P.subtype
  have hker : ρP.ker ≤ ψ₀.ker := by
    intro g hg
    have hg1 : (g : S₁) ∈ ρ.ker := hg
    have hc : (g : S₁) ∈ center S₁ := hρ _ hg1
    have hcen : ψ₀ g ∈ center (K₀ ⧸ center K₀) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨h, rfl⟩ := hψ₀ s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.1 hc (h : S₁))
    rw [center_eq_bot_of_simple_nonab hsim hnab, Subgroup.mem_bot] at hcen
    exact hcen
  let ψ₁ : ρP.range →* K₀ ⧸ center K₀ :=
    (QuotientGroup.lift ρP.ker ψ₀ hker).comp (QuotientGroup.quotientKerEquivRange ρP).symm.toMonoidHom
  have hψ₁ : Function.Surjective ψ₁ := by
    intro s
    obtain ⟨g, rfl⟩ := hψ₀ s
    exact ⟨QuotientGroup.quotientKerEquivRange ρP (QuotientGroup.mk g), by simp [ψ₁]⟩
  rcases simple_quotient_of_le_psl2 hodd hsim hnab ρP.range ψ₁ hψ₁ with h | ⟨q, hq⟩
  · exact hord.ne_sixty h
  · exact hord.two_mul_ne q (by rw [← hq]; ring)

end CFSG.GH74.Generic.S3
