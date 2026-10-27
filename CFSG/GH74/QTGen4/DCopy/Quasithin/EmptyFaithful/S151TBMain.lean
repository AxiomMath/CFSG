module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151TBA7Weight
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151XF
public import CFSG.Quasithin.EmptyFaithful.S151TBThree

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15120NoHatA6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) → ¬ IsHatA6Block L

@[expose] def Input15120L3Block_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) → IsLnBlock L 3

structure Input15120TwoBRes_F4 : Prop where

  noHatA6 : Input15120NoHatA6_F4

  l3Block : Input15120L3Block_F4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem isBlock_of_listD'_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (rH : Input15120NoHatA6_F4)
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hchar : CharTwo L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (hD : ListD' L) :
    IsAltBlockType L 7 ∨ IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L := by
  have hN := g1_le_normalizer h37 h38 hc hcomp hD
  have hq := hc.hL.quasi
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans hN)
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := (s1516_le_g1 T Z₁).trans hN
  obtain ⟨h1, -, h3⟩ := hC27 G (g1_1516 Z₁) (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) L
    (omegaOneCenterOf (pCoreOf 2 (L ⊔ q1_1516 Mc Z₁))) hc.h18.five.2.2 hcomp hq hchar
    hc.hL.not_le hRN rfl
  rcases h3 with ⟨hchi, hcases⟩ | ⟨⟨n, α, hn5, hn8, hsh, hα, -⟩, -⟩ | ⟨hHat, -⟩ | ⟨hexc, hidx⟩ |
    ⟨hAS, -⟩ | ⟨hg, -, -⟩ | ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ | ⟨hh, -, -⟩
  · rcases hcases with ⟨⟨n, hn, hlin⟩, -⟩ | ⟨hA5, -⟩ | ⟨hA7, -⟩ | ⟨hA7, -⟩
    · exact (listD'_false_of_lin2 hq hn hlin hD).elim
    · obtain ⟨α, hα⟩ := (isAltType_iff_exists_isAltBlockTypeWith (by decide)).1 hA5
      exact (listD'_false_of_alt hq (Or.inl rfl) hα hD).elim
    · exact Or.inl ⟨hchi.1.1, (isAltType_iff_exists_isAltBlockTypeWith (by decide)).1 hA7⟩
    · exact Or.inl ⟨hchi.1.1, (isAltType_iff_exists_isAltBlockTypeWith (by decide)).1 hA7⟩
  · have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl
    · exact (listD'_false_of_alt hq (Or.inl rfl) hα hD).elim
    · exact Or.inr (Or.inr (Or.inl ⟨hsh, α, hα⟩))
    · exact Or.inl ⟨hsh, α, hα⟩
    · exact (listD'_false_of_alt hq (Or.inr rfl) hα hD).elim
  · exact (rH G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hHat).elim
  · exact (not_excA7_index hc hcomp hSN hexc hidx).elim
  · rcases hAS with h6 | hsp4
    · exact Or.inr (Or.inr (Or.inl h6))
    · exact (listD'_false_of_sp4 hq hsp4 hD).elim
  · exact Or.inr (Or.inr (Or.inr hg))
  · obtain ⟨ψ₀, hψ₀, hO2, hker⟩ := exists_epi_autOn hRN h1
    exact (listD'_false_of_sl3 hq hn1 hF (e.toMonoidHom.comp ψ₀)
      (e.surjective.comp hψ₀) (fun x hx => by
        have := hO2 hx
        simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
        simpa using hx)) hD).elim
  · obtain ⟨ψ₀, hψ₀, hO2, hker⟩ := exists_epi_autOn hRN h1
    rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact (listD'_false_of_sl4 hq (e.toMonoidHom.comp ψ₀) (e.surjective.comp hψ₀)
        (fun x hx => by
          have := hO2 hx
          simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
          simpa using hx)) hD).elim
    · exact (listD'_false_of_sl5 hq (e.toMonoidHom.comp ψ₀) (e.surjective.comp hψ₀)
        (fun x hx => by
          have := hO2 hx
          simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
          simpa using hx)) hD).elim

theorem input15120TwoB_of_res_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (h : Input15120TwoBRes_F4) : Input15120TwoB_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hD
  refine ⟨hD, fun hcomp => ?_, fun hcomp htype => three_of_block h37 hc hcomp htype,
    fun hcomp => input15120A7Weight_of_c27_F4 h37 h38 hC27 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp⟩
  by_cases hL3 : IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L))
  · exact Or.inr (Or.inl (h.l3Block G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3))
  · exact isBlock_of_listD'_F4 h37 h38 hC27 h.noHatA6 hc hchar hcomp
      ((listD_iff_or.1 hD).resolve_right hL3)

end CFSG.Quasithin.S151TB
