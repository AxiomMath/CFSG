module

public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Gen
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbG23

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Inner


theorem inner_of_diag {F : Type} [Field F] {α : MulAut (adjointGroup ReeTag.G2.tag F)}
    {g : adjointGroup ReeTag.G2.tag F} {a : Fin ReeTag.G2.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) =
      (g : ModGL ReeTag.G2.tag F) * rootDiagUnit ReeTag.G2.tag a * h *
        (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag F)⁻¹) :
    α ∈ (MulAut.conj : adjointGroup ReeTag.G2.tag F →*
      MulAut (adjointGroup ReeTag.G2.tag F)).range := by
  obtain ⟨-, hrest⟩ := G2_F4_root_character_diagonals_inner ReeTag.G2.tag (Or.inl rfl) F
  obtain ⟨B, hB, -⟩ := (G2_F4_root_character_diagonals_inner ReeTag.G2.tag (Or.inl rfl) F).1
  obtain ⟨-, -, hdC, -⟩ := hrest B hB a
  refine ⟨g * ⟨rootDiagUnit ReeTag.G2.tag a, hdC⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hαg h]
  show (((g * ⟨rootDiagUnit ReeTag.G2.tag a, hdC⟩ : adjointGroup ReeTag.G2.tag F) * h *
    (g * ⟨rootDiagUnit ReeTag.G2.tag a, hdC⟩ : adjointGroup ReeTag.G2.tag F)⁻¹ :
      adjointGroup ReeTag.G2.tag F) : ModGL ReeTag.G2.tag F) = _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end Inner

section Classification


@[expose] noncomputable def phi : MulAut G23 := ReeTag.G2.finiteReeAut (ZMod 3) 0

theorem exists_conj_phi (α : MulAut G23) (hα : α * α = 1)
    (hout : α ∉ (MulAut.conj : G23 →* MulAut G23).range) :
    (∃ ψ : MulAut G23, ψ * α * ψ⁻¹ = phi) ∧ Nat.card (fixedGroup α) = 1512 := by
  have hK : Nat.card (ZMod 3) = 3 ^ 1 := by simp
  have hα2 : α ^ 2 = 1 := by rw [sq]; exact hα
  have : CharP (ZMod 3) ReeTag.G2.prime := ZMod.charP 3
  rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional
      (K := ZMod 3) (f := 1) le_rfl hK hα2 with
    ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, hαeq⟩
  · exact absurd (inner_of_diag hαg) hout
  · exfalso
    have h3 : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega) 3
    have h9 : 3 * 3 ≤ 3 ^ e * 3 ^ e := Nat.mul_le_mul h3 h3
    have hc : Nat.card (ZMod 3) = 3 := by simp
    rw [hKe, sq] at hc
    omega
  · have hb : b = 0 := by omega
    subst hb
    have hα' : (MulAut.conj g * ReeTag.G2.finiteReeAut (ZMod 3) 0) ^ 2 = 1 := by
      rw [← hαeq]
      exact hα2
    obtain ⟨⟨ψ, hψ⟩, -, hcard⟩ :=
      G2_exceptional_coset_involution_fixed_p_components 0 (ZMod 3) (by simp) g hα'
    rw [← hαeq] at hψ hcard
    exact ⟨⟨ψ, hψ⟩, hcard rfl⟩

end Classification

end CFSG.CGT.PushingUpLit.CGT6.EmbG23
