module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal

@[expose] def ChevalleyExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (b a : X) (Y E : Subgroup X), IsUnbalancingConfig b a Y E →
      OddLieType (Y ⧸ Open.fusionZStar Y) →
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f

@[expose] def CoverExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (b a : X) (Y E : Subgroup X), IsUnbalancingConfig b a Y E →
      ((∃ n : ℕ, Odd n ∧ 7 ≤ n ∧
          Nonempty (Y ⧸ Open.fusionZStar Y ≃* alternatingGroup (Fin n))) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) →
      center (Y ⧸ pPrimeCore 2 Y) = ⊥

theorem not_mem_center_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) {x : X} (hx : x ≠ 1) : x ∉ center X := by
  intro hxc
  have hc : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (mem_center_iff.mp (h ▸ mem_top b) a)
  rw [hc, mem_bot] at hxc
  exact hx hxc

theorem lieModel_psl_two_params {G : Type} [Group G] {p f : ℕ} (h : LieModel G .PSL 2 p f)
    (hp2 : p ≠ 2) : 1 ≤ f ∧ 5 ≤ p ^ f := by
  rcases h with ⟨-, hadm, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨hp, hf, -, -, h23⟩ := hadm
    refine ⟨hf, ?_⟩
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hne : p ^ f ≠ 3 := fun h => h23 (by rw [h])
    obtain ⟨k, hk⟩ := hodd
    omega
  all_goals exact absurd h0 (by norm_num)

theorem thompson_burgoyne_of_exclusions
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hHe : HeldTrivialMultiplier)
    (hChev : ChevalleyExclusion) (hCov : CoverExclusion)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (x y : X) (L : Subgroup X)
    (hT : UnbalancedLayer.GSUnbalancingTriple x y L) :
    (∃ n : ℕ, Odd n ∧ 9 ≤ n ∧ Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* NativeSporadic.He) ∨
        LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2) := by
  have hC := isUnbalancingConfig_of_triple hT
  obtain ⟨hx, -, -, hLx, hL, -⟩ := id hC
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hxZ := not_mem_center_of_isSimpleGroup hnonab hx1
  rcases config_uList hUc hK hxZ hC with hodd | hA | hL34 | hHeS
  · obtain ⟨p, f, hp, hp2, hm⟩ := hChev X hnonab hK hz hU x y L _ hC hodd
    have hc := hCov X hnonab hK hz hU x y L _ hC (.inr ⟨p, f, hp, hp2, hm⟩)
    obtain ⟨hf, h5⟩ := lieModel_psl_two_params hm hp2
    exact .inr (.inl (.inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv
      (coreQuotientEquiv_of_center_eq_bot L hc).symm hm⟩))
  · have hc := hCov X hnonab hK hz hU x y L _ hC (.inl hA)
    obtain ⟨n, hn, h7, ⟨e⟩⟩ := hA
    have e' := (coreQuotientEquiv_of_center_eq_bot L hc).trans e
    rcases (show n = 7 ∨ 9 ≤ n by obtain ⟨k, rfl⟩ := hn; omega) with rfl | h9
    · exact .inr (.inl (.inl ⟨e'⟩))
    · exact .inl ⟨n, hn, h9, ⟨e'⟩⟩
  · exact .inr (.inr (.inr hL34))
  · obtain ⟨eHe⟩ := hHeS
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq := twoComponent_coreQuotient_quasisimple hLx hL
    have hc := hHe _ hq ⟨(coreQuotientCenterEquiv L).trans eHe⟩
    exact .inr (.inr (.inl ⟨(coreQuotientEquiv_of_center_eq_bot L hc).trans eHe⟩))

end CFSG.ComponentClassification.TBLit
