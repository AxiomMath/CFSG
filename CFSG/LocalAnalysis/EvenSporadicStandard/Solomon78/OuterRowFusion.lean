module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def Sol78ChainFusion (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L s →
    ∃ (L' K : Subgroup G) (t u : G), StdHyp G L' ∧ IsSporadic L' s ∧ SolomonHyp G L' K t u ∧
      Sol78Fusion u t

theorem outer2_row_not_standard_of_fusion (s : TauCeti.SporadicName)
    (hchain : Sol78ChainFusion s)
    (hI : ∀ (Y : Type) [Group Y], IsSporadic Y s → HypothesisOne Y)
    (hfours : ∀ (Y : Type) [Group Y], IsSporadic Y s → CFSG.EvenSmallLie.FoursGroupCondition Y)
    (humv : ∀ (Y : Type) [Group Y], IsSporadic Y s → UMovesCond Y)
    (G : Type) [Group G] [Finite G] (L : Subgroup G) (hStd : StdHyp G L) :
    ¬ IsSporadic L s := by
  intro hL
  obtain ⟨L', K, t, u, hStd', hL', h, hf⟩ := hchain G L hStd hL
  obtain ⟨e⟩ := hL'
  have := h.simpleL
  have hZ : center L' = ⊥ := center_eq_bot_of_simple_nonabelian h.nonabelianL
  have hq : IsSporadic (L' ⧸ center L') s :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hS : ∀ S : Sylow 2 (centralizer (L' : Set G)), Nat.card S = 2 := fun S =>
    hStd'.card_sylow_eq_two_of_fours (hI _ hq) (hfours _ ⟨e⟩) S
  exact solomon_closing_3_12_3 hStd' hS h hf
    (sol78UMoves_of_cond (humv _ ⟨e⟩) h.u_order h.u_mem)

@[expose] def Sol78NoExc (s : TauCeti.SporadicName) (c : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (t u : G), StdHyp G L → IsSporadic L s →
    SolomonHyp G L K t u → ¬ centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G) →
    ∀ (u₁ : G) (hN : u₁ ∈ normalizer (L : Set G)), u₁ * u₁ = 1 → u₁ * t = t * u₁ →
      IsConj u u₁ → Nat.card (fixSubgroup (L.normalizerMonoidHom ⟨u₁, hN⟩)) ≠ c

theorem outer2_row_not_standard_exc (s : TauCeti.SporadicName) (c : ℕ) (hchain : Sol78Chain s)
    (hno : Sol78NoExc s c)
    (hI : ∀ (Y : Type) [Group Y], IsSporadic Y s → HypothesisOne Y)
    (hfours : ∀ (Y : Type) [Group Y], IsSporadic Y s → CFSG.EvenSmallLie.FoursGroupCondition Y)
    (hacc : ∀ (Y : Type) [Group Y], IsSporadic Y s →
      AutCenterCondExc Y (fun α => Nat.card (fixSubgroup α) = c))
    (hinn : ∀ (Y : Type) [Group Y], IsSporadic Y s → ∀ y : Y, y * y = 1 →
      Nat.card (fixSubgroup (MulAut.conj y)) ≠ c)
    (humv : ∀ (Y : Type) [Group Y], IsSporadic Y s → UMovesCond Y)
    (G : Type) [Group G] [Finite G] (L : Subgroup G) (hStd : StdHyp G L) :
    ¬ IsSporadic L s := by
  intro hL
  obtain ⟨L', K, t, u, hStd', hL', h⟩ := hchain G L hStd hL
  obtain ⟨e⟩ := hL'
  have := h.simpleL
  have hZ : center L' = ⊥ := center_eq_bot_of_simple_nonabelian h.nonabelianL
  have hq : IsSporadic (L' ⧸ center L') s :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hS : ∀ S : Sylow 2 (centralizer (L' : Set G)), Nat.card S = 2 := fun S =>
    hStd'.card_sylow_eq_two_of_fours (hI _ hq) (hfours _ ⟨e⟩) S
  have hf := sol78Fusion_of_autCenterExc hStd' hS h (hacc _ ⟨e⟩) fun u₁ hN h2 hc hconj hex => by
    by_cases hMt : centralizer ({t} : Set G) ≤ L' ⊔ centralizer (L' : Set G)
    · have hu₁M : u₁ ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hc
      obtain ⟨l, hl, hx⟩ := mem_sup_centralizer_iff.1 (hMt hu₁M)
      have hνl : L'.normalizerMonoidHom ⟨u₁, hN⟩ = MulAut.conj (⟨l, hl⟩ : L') :=
        (normalizerMonoidHom_eq_conj_iff hN ⟨l, hl⟩).2 hx
      have hll : (⟨l, hl⟩ : L') * ⟨l, hl⟩ = 1 := by
        have hmem : ((⟨l, hl⟩ : L') * ⟨l, hl⟩) ∈ center L' := by
          rw [mem_center_iff]
          intro x
          apply Subtype.ext
          have hx' := hx (l * x * l⁻¹) (L'.mul_mem (L'.mul_mem hl x.2) (L'.inv_mem hl))
          have hx'' := hx x x.2
          have hu₁u₁ : u₁ * (u₁ * (x : G) * u₁⁻¹) * u₁⁻¹ = x := by
            calc u₁ * (u₁ * (x : G) * u₁⁻¹) * u₁⁻¹ = (u₁ * u₁) * x * (u₁ * u₁)⁻¹ := by group
              _ = x := by rw [h2]; group
          rw [hx'', hx'] at hu₁u₁
          have h3 : (l * l) * (x : G) * (l * l)⁻¹ = x := by
            calc (l * l) * (x : G) * (l * l)⁻¹ = l * (l * x * l⁻¹) * l⁻¹ := by group
              _ = x := hu₁u₁
          exact (mul_inv_eq_iff_eq_mul.1 h3).symm
        rw [hZ, Subgroup.mem_bot] at hmem
        exact hmem
      rw [hνl] at hex
      exact hinn _ ⟨e⟩ ⟨l, hl⟩ hll hex
    · exact hno G L' K t u hStd' ⟨e⟩ h hMt u₁ hN h2 hc hconj hex
  exact solomon_closing_3_12_3 hStd' hS h hf
    (sol78UMoves_of_cond (humv _ ⟨e⟩) h.u_order h.u_mem)

end CFSG.EvenSporadicStandard.Solomon78
