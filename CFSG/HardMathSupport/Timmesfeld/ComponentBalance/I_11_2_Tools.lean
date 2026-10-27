module

public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.Open.GLBDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Foundations.KCoreOpen

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open

section TwoLocal

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem bddAbove_twoLocalRank (hp : 1 < p) :
    BddAbove {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
  refine ⟨Nat.card X, ?_⟩
  rintro k ⟨H, -, rfl⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp H
  have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp
  have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card X := hE ▸ Subgroup.card_le_card_group E
  change CFSG.Open.pRank p H ≤ Nat.card X
  omega

theorem le_glaTwoLocalRank_of_isTwoLocal (hp : 1 < p) {H : Subgroup X} (hH : IsTwoLocal H) :
    CFSG.Open.pRank p H ≤ GLATwoLocalRank p X :=
  le_csSup (bddAbove_twoLocalRank hp) ⟨H, hH, rfl⟩

theorem le_glaTwoLocalRank_normalizer (hp : 1 < p) {T : Subgroup X} (hT : T ≠ ⊥)
    (h2 : IsPGroup 2 T) : CFSG.Open.pRank p (Subgroup.normalizer (T : Set X)) ≤ GLATwoLocalRank p X :=
  le_glaTwoLocalRank_of_isTwoLocal hp ⟨T, hT, h2, rfl⟩

theorem le_glaTwoLocalRank_of_le_normalizer (hp : 1 < p) {T E : Subgroup X} (hT : T ≠ ⊥)
    (h2 : IsPGroup 2 T) (hE : IsElemAbelian p E) (hEN : E ≤ Subgroup.normalizer (T : Set X))
    {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ GLATwoLocalRank p X :=
  (CFSG.SectionRank.le_pRank hp hEN hE hk).trans (le_glaTwoLocalRank_normalizer hp hT h2)

theorem exists_twoLocal_attaining (hp : 1 < p) (h2 : ∃ t : X, orderOf t = 2) :
    ∃ T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      CFSG.Open.pRank p (Subgroup.normalizer (T : Set X)) = GLATwoLocalRank p X := by
  obtain ⟨t, ht⟩ := h2
  have hne : {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}.Nonempty := by
    refine ⟨_, Subgroup.normalizer (Subgroup.zpowers t : Set X), ⟨_, ?_, ?_, rfl⟩, rfl⟩
    · intro h
      have := Subgroup.zpowers_eq_bot.1 h
      rw [this, orderOf_one] at ht
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨H, ⟨T, hT, hT2, rfl⟩, hk⟩ := Nat.sSup_mem hne (bddAbove_twoLocalRank hp)
  exact ⟨T, hT, hT2, hk⟩

theorem exists_twoLocal_attaining_elemAbelian (hp : 1 < p) (h2 : ∃ t : X, orderOf t = 2) :
    ∃ T E : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ IsElemAbelian p E ∧
      E ≤ Subgroup.normalizer (T : Set X) ∧ Nat.card E = p ^ GLATwoLocalRank p X := by
  obtain ⟨T, hT, hT2, hk⟩ := exists_twoLocal_attaining hp h2
  obtain ⟨E, hEN, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp (Subgroup.normalizer (T : Set X))
  exact ⟨T, E, hT, hT2, hE, hEN, hk ▸ hcard⟩

theorem exists_twoLocal_attaining_subgroup (hp : 1 < p) (L : Subgroup X)
    (h2 : ∃ t : ↥L, orderOf t = 2) :
    ∃ T E : Subgroup X, T ≤ L ∧ E ≤ L ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ IsElemAbelian p E ∧
      E ≤ Subgroup.normalizer (T : Set X) ∧ Nat.card E = p ^ GLATwoLocalRank p ↥L := by
  obtain ⟨T, E, hT, hT2, hE, hEN, hcard⟩ := exists_twoLocal_attaining_elemAbelian hp h2
  refine ⟨T.map L.subtype, E.map L.subtype, Subgroup.map_subtype_le T, Subgroup.map_subtype_le E,
    fun h => hT ((Subgroup.map_eq_bot_iff_of_injective T L.subtype_injective).1 h),
    hT2.map _, CFSG.SectionRank.isElemAbelian_map hE _, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 (hEN he) x).1 hx
      exact ⟨e * x * e⁻¹, this, by simp⟩
    · rintro ⟨x, hx, hxe⟩
      have h1 : e⁻¹ * x * e ∈ T := by
        have := (Subgroup.mem_normalizer_iff.1 (hEN he) (e⁻¹ * x * e)).2
        simpa using this (by simpa [mul_assoc] using hx)
      refine ⟨e⁻¹ * x * e, h1, ?_⟩
      have := congrArg (fun z : X => (e : X)⁻¹ * z * (e : X)) hxe
      simpa [mul_assoc] using this
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]

end TwoLocal

section KGroup

theorem isKGroup_of_le {X : Type*} [Group X] (hX : IsKGroup X) (C : Subgroup X) :
    IsKGroup ↥C :=
  hX.subgroup C

end KGroup

section ElemAbelian

variable {G : Type*} [Group G] {p : ℕ}

theorem isElemAbelian_of_le {E F : Subgroup G} (hE : IsElemAbelian p E) (h : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE h

theorem isPGroup_of_isElemAbelian (_hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem exists_card_eq_of_isElemAbelian [Finite G] (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : ∃ k, Nat.card E = p ^ k := by
  have := Fact.mk hp
  exact IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hp hE)

theorem pRank_eq_of_card [Finite G] (hp : 1 < p) {E : Subgroup G} (hE : IsElemAbelian p E)
    {k : ℕ} (hk : Nat.card E = p ^ k) : CFSG.Open.pRank p E = k :=
  le_antisymm (CFSG.SectionRank.pRank_le hp fun _ hE' _ => hk ▸ Subgroup.card_le_of_le hE')
    (CFSG.SectionRank.le_pRank hp le_rfl hE hk)

theorem pRank_gLBConj [Finite G] (hp : 1 < p) (g : G) (H : Subgroup G) :
    CFSG.Open.pRank p (GLBConj g H) = CFSG.Open.pRank p H :=
  CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective H

end ElemAbelian

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
