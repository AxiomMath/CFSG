module

public import CFSG.GH74.GLS.Stage4.T2P71Defs
public import CFSG.GH74.GLS.Stage4.T2P71L72NS

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.F1Loc
  CFSG.Assembly.LowTwoRank

section Local


variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {n : ℕ} {N : T2N3 G} {u : G}

theorem local_three (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hIVK : CFSG.GH74.GLS.IVK.IVK_4_1_R_L3) (h : P71Env Gs n N u) (hlt : Lt3 G n) (hn : 3 ≤ n)
    {f : G} (hf : f ∈ N.F) (hfo : orderOf f = 3) :
    ∃ (m : ℕ) (hzC : N.z ∈ centralizer ({f} : Set G)), n = 3 * m ∧
      CFSG.GH74.GLS.IVK.Hyp94Loc
        (↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G))) Gs
        (QuotientGroup.mk (⟨N.z, hzC⟩ : ↥(centralizer ({f} : Set G)))) .G2 3 m := by
  obtain ⟨F₁, F₂, iF₁, iF₂, t, hS, hR⟩ := h.setup
  have hctx := h.ctx
  exact f1_core_lt hL hL3 hIVK hn h.std hS hR hlt rfl rfl rfl h.q₁ h.q₂ h.sec5 h.coord
    Nat.prime_three (by norm_num) hfo hf (fun s hs => hctx.FS f hf s hs)

end Local

end CFSG.GH74.GLS.Stage4.Rest.L72
