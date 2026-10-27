module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Fus3
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10One

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage1.Thm6.Prod

section Fused

variable {G : Type} [Group G] [Finite G]

theorem fused_false
    (h11 : Lemma20_11) {z : G} {k : Kind} {S M : Subgroup G} (hF : Fail20 G z k S M) (hMC : M = Cen z)
    {ε : Bool} {q : ℕ} (hTL : TypeL4 z k S ε q) (hfused : Fused ε q) : False := by
  have hctx : Stage2Ctx G z k S := hF.ctx.ctx17.ctx
  obtain ⟨hk, L₁, L₂, hL4⟩ := hTL
  subst hk
  have hT : TypeCl z (Kind.l4 ε) S := Or.inl ⟨ε, q, rfl, L₁, L₂, hL4⟩
  have hP := hL4.pair
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := by
    have := hF.ctx.thm4.1
    rwa [hMC] at this
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hP h4a
  have hmod4 : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨m, hm⟩ := hP.odd
    omega
  have hq9 : q ≠ 9 := by
    rintro rfl
    have h8 := hL4.mod8
    cases ε <;> simp [Fused] at hfused h8
  have hone : OneClassInv G := by
    rcases hL4.fusion with ⟨-, hone⟩ | ⟨h2, -⟩
    · exact hone
    · exfalso
      unfold Fused at hfused
      cases ε <;> simp at hfused h2 <;> omega
  obtain ⟨U, hUS, hU4, hUn, hzU, hAut⟩ := Bender.Thm2.exists_U_typeOne hctx (Or.inl hone)
  have hz2 := hctx.orderOf_z
  have hz1 : z ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hz2
    omega
  obtain ⟨g, hg, hgz⟩ := exists_move_of_autOrd hU4 hzU hz1 hAut
  have hmax : IsCoatom (Cen z) := by
    have := hF.ctx.ctx17.mem.1
    rwa [hMC] at this
  have hne : pPrimeCore 2 ↥(Cen z) ≠ ⊥ := by
    intro hbot
    apply hF.odd_ne
    rw [hMC]
    unfold pPrimeCoreOf
    rw [hbot, Subgroup.map_bot]
  have hSetup : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g :=
    ⟨hctx, hL4, hK, hq9, hmax, hne, hUS, hU4, hUn, hzU, hg, hgz⟩
  exact hF.fail (fused_conc201 h11 hF hMC hT ⟨rfl, L₁, L₂, hL4⟩ hfused hSetup)

end Fused

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
