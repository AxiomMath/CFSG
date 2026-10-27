module

public import CFSG.LargeExtraspecial.S10FourW6
public import CFSG.GF2Type.Smith1979.GammaU.Dict2
public import CFSG.GF2Type.Smith1980Orth.Setup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S10
  CFSG.LargeExtraspecial.S14 CFSG.GF2Type.Smith1980Orth

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem canon_of_dec108 (I : TimInputs) (hw : S.width = 6) (hP : NoPGL25 S g) {t : S.O}
    {X : Hyp10 S g t}
    {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb) {θ : S.O} (hθ : θ ∈ ⁅Yb, Yb⁆) (hθ1 : θ ≠ 1) :
    ∀ m ∈ S.Mbar, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) = aT S g →
      m * θ * m⁻¹ = θ ∨ m * θ * m⁻¹ = θ⁻¹ := by
  rintro _ ⟨k, rfl⟩ hfix
  have hn : 3 ≤ S.width := by omega
  have hN := (S.timmesfeld_12_4_1 X.H.conj_mem X.H.conj_ne hn k).2 hfix
  have hle : (S.Lbar g ⊓ Xb).map (cK S k) ≤ S.Lbar g := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hN x).1 hx.1
  have hE := D.timmesfeld_10_8_two I.hCE hP hle
  obtain ⟨τ, hτ, hτ1⟩ : ∃ τ ∈ S.Lbar g ⊓ Xb, τ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : S.Lbar g ⊓ Xb = ⊥ := (eq_bot_iff_forall _).2 hcon
    have h2 := D.two_mul_card_Ebar I.hCE
    rw [hbot, card_bot] at h2
    have hge := S.card_Lbar_ge X.H.conj_mem X.H.conj_ne
    have h4 : 2 ^ 2 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hY := D.map_commutator_eq I.hCE hP hτ hτ1 (hE.symm ▸ hτ)
  have hmem : S.ρ k * θ * (S.ρ k)⁻¹ ∈ ⁅Yb, Yb⁆ := by
    rw [← hY]
    exact ⟨θ, hθ, rfl⟩
  have hne : S.ρ k * θ * (S.ρ k)⁻¹ ≠ 1 := fun h => hθ1 (by
    calc θ = (S.ρ k)⁻¹ * (S.ρ k * θ * (S.ρ k)⁻¹) * S.ρ k := by group
      _ = 1 := by rw [h]; group)
  exact D.dec.eq_or_eq_inv_of_mem_commutator hθ hθ1 hmem hne

end CFSG.GF2Type.Smith1979.GammaU.Dict
