module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208SpKey
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208P1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10One
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Stage2

theorem lemma20_8_sporadic {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}
    (h : Fail20 G z k S M) (hMC : M = Cen z) (hk : k = Kind.mcl ∨ k = Kind.ly) : False := by
  subst hMC
  have hctx : Stage2Ctx G z k S := h.ctx.ctx17.ctx
  have hmax : IsCoatom (Cen z) := h.ctx.ctx17.mem.1
  have h4a : Thm4a (Cen z) := h.ctx.thm4.1
  have hz2 : orderOf z = 2 := hctx.central.1
  obtain ⟨n, hn8, hn11, hsp⟩ : ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Stage1Sporadic G z S n := by
    have hd := hctx.data
    rcases hk with rfl | rfl
    · cases hd with
      | mcl h' =>
        obtain ⟨n, hn, hsp⟩ := h'
        exact ⟨n, by omega, by omega, hsp⟩
    · cases hd with
      | ly h' =>
        obtain ⟨n, hn, hsp⟩ := h'
        exact ⟨n, by omega, by omega, hsp⟩
  have hone : Signalizer.TypeOneCase G k := Or.inl hsp.one_class
  obtain ⟨U, hUS, hU4, hUn, hzU, hAut⟩ := exists_U_typeOne hctx hone
  have key : ∀ g ∈ normalizer (U : Set G), g * z * g⁻¹ ≠ z →
      ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z := by
    intro g hgN hgz a ha
    have hgU : ∀ u : G, u ∈ U ↔ g * u * g⁻¹ ∈ U := Subgroup.mem_normalizer_iff.1 hgN
    have htU : g * z * g⁻¹ ∈ U := (hgU z).1 hzU
    have htC : g * z * g⁻¹ ∈ Cen z := hctx.S_le_Cen (hUS htU)
    have ht2 : orderOf (g * z * g⁻¹) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj g) z
      rw [MulAut.conj_apply] at this
      rw [this, hz2]
    have htk := toBar_not_center htC ht2 hgz hz2 hsp.cover.2.1
    exact conj_oddCore_le hn8 hn11 h4a hsp.cover hz2 htC ht2 htk rfl a ha
  have hbot : pPrimeCore 2 ↥(Cen z) = ⊥ := L208Key.oddCore_eq_bot_of_key hctx hmax hU4 hzU hAut key
  apply h.odd_ne
  show (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype = ⊥
  rw [hbot, Subgroup.map_bot]

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp
