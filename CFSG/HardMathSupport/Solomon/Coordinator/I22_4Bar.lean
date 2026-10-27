module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Pre

variable {G : Type*} [Group G]

@[expose] def i224Pre (p : ℕ) (X : Subgroup G) (T : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
    Subgroup G :=
  (T.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype

theorem mem_i224Pre {p : ℕ} {X : Subgroup G} {T : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} {x : G} :
    x ∈ i224Pre p X T ↔ ∃ hx : x ∈ X, QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hx⟩ ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem barX_le_of_pre {p : ℕ} {X S : Subgroup G} {T : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)}
    (h : S ≤ i224Pre p X T) : barX p X S ≤ T := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨hx, hT⟩ := mem_i224Pre.1 (h ((Subgroup.mem_subgroupOf).1 hs))
  exact hT

end Pre

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem i224_pRank_eq {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : CFSG.Open.pRank p E = k := by
  unfold CFSG.Open.pRank
  have hbound : ∀ k' : ℕ, k' ∈ {k | ∃ E' : Subgroup G, E' ≤ E ∧ IsElemAbelian p E' ∧
      Nat.card E' = p ^ k} → k' ≤ k := by
    intro k' hk'
    obtain ⟨E', hE'E, -, hk''⟩ := hk'
    have h1 : Nat.card E' ≤ Nat.card E := Subgroup.card_le_of_le hE'E
    rw [hk'', hk] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  exact le_antisymm (csSup_le ⟨k, E, le_rfl, hE, hk⟩ hbound)
    (le_csSup ⟨k, hbound⟩ ⟨E, le_rfl, hE, hk⟩)

theorem i224_card_le_iff {p : ℕ} (hp : p.Prime) {A E : Subgroup G} (hA : IsElemAbelian p A)
    (hE : IsElemAbelian p E) :
    CFSG.Open.pRank p A - 1 ≤ CFSG.Open.pRank p E ↔ Nat.card A ≤ p * Nat.card E := by
  obtain ⟨a, ha⟩ := LocalBalance.Lemma54Ns.exists_card_eq_pow hp hA
  obtain ⟨e, he⟩ := LocalBalance.Lemma54Ns.exists_card_eq_pow hp hE
  rw [i224_pRank_eq hp hA ha, i224_pRank_eq hp hE he, ha, he, ← pow_succ',
    Nat.pow_le_pow_iff_right hp.one_lt]
  omega

theorem i224_card_barX {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hE : IsPGroup p E)
    (hEX : E ≤ X) : Nat.card (barX p X E) = Nat.card E := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (E.subgroupOf X).subtype with hf
  have hfi := injective_barX_comp hp hE hEX
  have hrange : f.range = barX p X E := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv]

end Rank

section Comp

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem i224_comm_cj {L : Subgroup Ω} (hL : CFSG.Open.IsComponentOf L ⊤) (g g' : Ω)
    (hne : i224Cj g L ≠ i224Cj g' L) :
    ∀ x ∈ i224Cj g L, ∀ y ∈ i224Cj g' L, x * y = y * x := by
  have hA : CFSG.Open.IsComponentOf (i224Cj g L) ⊤ :=
    CFSG.Quasithin.B113.isComponentOf_conj hL (Subgroup.mem_top g)
  have hB : CFSG.Open.IsComponentOf (i224Cj g' L) ⊤ :=
    CFSG.Quasithin.B113.isComponentOf_conj hL (Subgroup.mem_top g')
  have hcomm : ⁅i224Cj g L, i224Cj g' L⁆ = ⊥ := by
    rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hA hB.2.1 with h1 | h1
    · rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hB hA.2.1 with h2 | h2
      · exact absurd (le_antisymm h1 h2) hne
      · rw [Subgroup.commutator_comm]
        exact h2
    · exact h1
  intro x hx y hy
  have : ⁅x, y⁆ ∈ (⊥ : Subgroup Ω) := hcomm ▸ Subgroup.commutator_mem_commutator hx hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

end Comp

section Normalizer

variable {G : Type*} [Group G] [Finite G]

theorem i224_mem_normalizer_of_barX {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L)
    {b : G} (hb : b ∈ X)
    (hn : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hb⟩ ∈
      Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    b ∈ Subgroup.normalizer (L : Set G) := by
  have hX : GLBConj b X = X := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hb)
  have h1 := glaPComponent_gLBConj hL b
  rw [hX] at h1
  have h2 : barX p X (GLBConj b L) = barX p X L := by
    rw [barX_gLBConj_eq p hb L]
    exact gLBConj_eq_of_mem_normalizer hn
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique h1 hL h2)

theorem i224_barX_inf_normalizer {p : ℕ} {X B L : Subgroup G} (hL : GLAPComponent p X L) :
    barX p X B ⊓ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore p ↥X)) =
      barX p X (B ⊓ Subgroup.normalizer (L : Set G)) := by
  apply le_antisymm
  · rintro y ⟨hyB, hyN⟩
    obtain ⟨b, hb, rfl⟩ := hyB
    have hbB : (b : G) ∈ B := (Subgroup.mem_subgroupOf).1 hb
    have hbN : (b : G) ∈ Subgroup.normalizer (L : Set G) := i224_mem_normalizer_of_barX hL b.2 hyN
    exact ⟨b, (Subgroup.mem_subgroupOf).2 ⟨hbB, hbN⟩, rfl⟩
  · exact le_inf (barX_mono p inf_le_left) (barX_le_normalizer inf_le_right)

end Normalizer

end CFSG.HardMathSupport.Solomon.Coordinator
