module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Key
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208P1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10One
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Stage2

theorem lemma20_8_g2 {G : Type} [Group G] [Finite G] {z : G} {S M : Subgroup G}
    (h : Fail20 G z Kind.g2 S M) (hMC : M = Cen z) : False := by
  subst hMC
  have hctx : Stage2Ctx G z Kind.g2 S := h.ctx.ctx17.ctx
  have hmax : IsCoatom (Cen z) := h.ctx.ctx17.mem.1
  have h4a : Thm4a (Cen z) := h.ctx.thm4.1
  have h4c : Thm4c z (Cen z) := h.ctx.thm4.2.2
  have hg := Final.L26.g2_data hctx
  have hone : Signalizer.TypeOneCase G Kind.g2 := Or.inl hg.one_class
  obtain ⟨U, hUS, hU4, hUn, hzU, hAut⟩ := exists_U_typeOne hctx hone
  have key : ∀ g ∈ normalizer (U : Set G), g * z * g⁻¹ ≠ z →
      ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z := fun g hgN hgz =>
    g2_key hctx h4a h4c hUS hU4 hzU hUn hgN hgz
  have hbot : pPrimeCore 2 ↥(Cen z) = ⊥ := L208Key.oddCore_eq_bot_of_key hctx hmax hU4 hzU hAut key
  apply h.odd_ne
  show (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype = ⊥
  rw [hbot, Subgroup.map_bot]

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
