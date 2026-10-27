module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.HypOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem center_eq_bot_of_isSporadic
    {Y : Type} [Group Y] (hY : IsSporadic Y .M11) : center Y = ⊥ := by
  obtain ⟨e₀⟩ := hY
  have e : Y ≃* NativeSporadic.M11 := e₀
  have hc : Subgroup.center NativeSporadic.M11 = ⊥ := CFSG.Sporadic.Schreier.m11_center_eq_bot'
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ Subgroup.center NativeSporadic.M11 := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hc, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem m11_not_standard
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) :
    ¬ IsSporadic L .M11 := by
  intro hL
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hLq : IsSporadic (L ⧸ center L) .M11 := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hI : HypothesisOne (L ⧸ center L) := by
    obtain ⟨φ⟩ := hLq
    exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv φ.symm hypothesisOne_native
  have hinn := allInner_of_isSporadic hLq
  have hS := h.card_sylow_eq_two_of_inner hI hinn
  obtain ⟨t, ht, ht2⟩ := h.exists_involution_centralizer
  obtain ⟨hC, hd, -⟩ := h.centralizer_eq_prod_of_center_eq_bot hS ht ht2
    (h.centralizer_le_sup_centralizer_of_inner ht ht2 hinn) hZ
  obtain ⟨e⟩ := hL
  have hF : M11Facts L := M11Facts.of_mulEquiv e.symm m11Facts_native
  obtain ⟨a, b, g, h1, h2, h3, h4, h5, h6, h7⟩ := hF.exists_elts
  have hts : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by decide)
  refine Setting.false' (G := G)
    { t := t
      L := L
      a := a
      b := b
      g := g
      simple := h.simple
      nonabelian := h.nonabelian
      t_sq := hts
      t_ne := ht1
      comm := fun ℓ hℓ => (mem_centralizer_iff.1 ht ℓ hℓ).symm
      t_not_mem := fun htL => ht1 (mem_bot.1 (hd.le_bot ⟨htL, mem_zpowers t⟩))
      centralizer_eq := hC
      a_mem := a.2
      b_mem := b.2
      g_mem := g.2
      a8 := by simpa using congrArg Subtype.val h1
      b_sq := by simpa using congrArg Subtype.val h2
      rel := by simpa using congrArg Subtype.val h3
      a4 := fun h' => h4 (Subtype.ext (by simpa using h'))
      b_not_pow := fun j hj => h5 j (Subtype.ext (by simpa using hj))
      g_z := by simpa using congrArg Subtype.val h6
      g_b := by simpa using congrArg Subtype.val h7
      card_L := hF.card
      card_inv := hF.card_inv
      conj_inv := hF.conj_inv }

end CFSG.EvenSporadicStandard.M11Std
