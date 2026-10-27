module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterFamilies
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterF4G2

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Open CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

theorem card_range_le_of_cyclic {D A : Type} [Group D] [Group A] [Finite A] [IsCyclic A]
    (α : D →* A) {p : ℕ} (hp : p.Prime) (hexp : ∀ x : D, x ^ p = 1) :
    Nat.card α.range ≤ p := by
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    rw [← map_pow, hexp x, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  exact Nat.le_of_dvd hp.pos hexpα

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem exists_inner_of_elemAbelian_adjointE_gen (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (MulAut (adjointGroup τ K)))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : 3 * p < Nat.card D) :
    ∃ x ∈ D ⊓ inner (adjointGroup τ K), x ≠ 1 := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨Φ, -, -, hΦcard⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  have hdet : τ.cartan.det.natAbs ≤ 3 := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]; decide
    · rw [det_cartan_E7]; decide
    · rw [det_cartan_E8]; decide
  have hdetpos : 0 < τ.cartan.det.natAbs := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]; decide
    · rw [det_cartan_E7]; decide
    · rw [det_cartan_E8]; decide
  have hE2 : exactE τ ∣ 2 := by
    rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  have hΦker3 : Nat.card Φ.ker ≤ 3 := (Nat.le_of_dvd hdetpos hΦcard).trans hdet
  have hΦfin : Finite Φ.ker :=
    Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hΦcard hdetpos).ne'
  let ρ : D →* Outer (adjointGroup τ K) :=
    (QuotientGroup.mk' (inner (adjointGroup τ K))).comp D.subtype
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxin : (x : MulAut (adjointGroup τ K)) ∈ inner (adjointGroup τ K) :=
      (QuotientGroup.eq_one_iff (N := inner (adjointGroup τ K)) _).1 hx
    exact Subtype.ext (hno x ⟨x.2, hxin⟩)
  let α : D →* RingAut K := (MonoidHom.fst _ _).comp (Φ.comp ρ)
  have hexpD : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hexp x x.2)
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hrange : Nat.card α.range ≤ p := card_range_le_of_cyclic α hp hexpD
  have hmem : ∀ x : α.ker, ρ x ∈ Φ.ker := by
    intro x
    have hx1 : (Φ (ρ x)).1 = 1 := x.2
    have hyp : (Φ (ρ x)) ^ p = 1 := by
      rw [← map_pow, ← map_pow, hexpD, map_one, map_one]
    have h1 : (Φ (ρ x)).2 ^ p = 1 := by
      have := congrArg Prod.snd hyp
      simpa using this
    have h2 : orderOf (Φ (ρ x)).2 ∣ exactE τ := by
      have := orderOf_dvd_natCard (Φ (ρ x)).2
      have hne : exactE τ ≠ 0 := by rcases hτ with rfl | rfl | rfl <;> simp [exactE]
      have h3 : Nat.card (Multiplicative (ZMod (exactE τ))) = exactE τ := by
        have : NeZero (exactE τ) := ⟨hne⟩
        rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      rwa [h3] at this
    have h4 : orderOf (Φ (ρ x)).2 ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h6 : orderOf (Φ (ρ x)).2 ∣ Nat.gcd p 2 := Nat.dvd_gcd h4 (h2.trans hE2)
    have h7 : Nat.gcd p 2 = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
    rw [h7] at h6
    have hz : (Φ (ρ x)).2 = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)
    exact Prod.ext hx1 hz
  have hker : Nat.card α.ker ≤ 3 := by
    have hinj : Function.Injective (fun x : α.ker => (⟨ρ x, hmem x⟩ : Φ.ker)) := by
      intro x y hxy
      exact Subtype.ext (hρinj (congrArg Subtype.val hxy))
    exact (Nat.card_le_card_of_injective _ hinj).trans hΦker3
  have hsplit : Nat.card D = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have : Nat.card D ≤ p * 3 := by
    rw [hsplit]; exact Nat.mul_le_mul hrange hker
  omega

theorem three_mul_lt_pow_three_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    3 * p < p ^ 3 := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp0 : 0 < p := hp.pos
  have : 3 * p < p * p * p := by nlinarith
  calc 3 * p < p * p * p := this
    _ = p ^ 3 := by ring

section Bridge


theorem nonempty_mulEquiv_adjoint_of_bridge {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hbr : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) {S : Type} [Group S]
    (e0 : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) [Fact q.p.Prime] :
    Nonempty (S ≃* adjointGroup τ (GaloisField q.p q.exponent)) := by
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨eB⟩ := hbr q hv (GaloisField q.p q.exponent) (by rw [hKq, TauCeti.PrimePower.card_def])
  exact ⟨e0.trans (eB.symm.trans adjointEquivQuotient.symm)⟩

theorem exists_inner_of_bridge_E_all {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hbr : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (S : Type) [Group S]
    (e0 : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3) :
    ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_adjoint_of_bridge hbr q hv e0
  set φ : MulAut S ≃* MulAut (adjointGroup τ (GaloisField q.p q.exponent)) :=
    MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := exists_inner_of_elemAbelian_adjointE_gen hτ hp hp2
    (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by rw [hcardD]; exact three_mul_lt_pow_three_of_odd_prime hp hp2)
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

theorem lieOuterRankFamE6 : LieOuterRankFam .E6 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  exact exists_inner_of_bridge_E_all (Or.inl rfl) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q
    hv S e0 hp hp2 D hD hcard

theorem lieOuterRankFamE7 : LieOuterRankFam .E7 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  exact exists_inner_of_bridge_E_all (Or.inr (Or.inl rfl))
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv S e0 hp hp2 D hD hcard

theorem lieOuterRankFamE8 : LieOuterRankFam .E8 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  exact exists_inner_of_bridge_E_all (Or.inr (Or.inr rfl))
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv S e0 hp hp2 D hD hcard

theorem lieOuterRankFamF4 : LieOuterRankFam .F4 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨e⟩ := nonempty_mulEquiv_adjoint_of_bridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv e0
  have hlt : p < Nat.card D := hcard ▸ lt_pow_three_of_prime hp
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hcyc := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  by_cases h2 : q.p = 2
  · have hchar : CharP K ReeTag.F4.prime := by
      have : CharP K q.p := inferInstance
      rw [show ReeTag.F4.prime = 2 from rfl, ← h2]
      exact this
    have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, h2]
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      even_F4_exact_automorphism_normal_form q.exponent_pos K hK2
    have : NeZero (2 * q.exponent) := ⟨by have := q.exponent_pos; omega⟩
    have : IsCyclic (Multiplicative (ZMod (2 * q.exponent))) := inferInstance
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient
      (A := Multiplicative (ZMod (2 * q.exponent))) e Θ hker hp D hD.2 hlt
    exact ⟨x, hx, hx1⟩
  · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
      q.prime_p h2 q.exponent_pos K hK .F4 (Or.inl rfl)
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 hlt
    exact ⟨x, hx, hx1⟩

theorem lieOuterRankFamG2 : LieOuterRankFam .G2 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨e⟩ := nonempty_mulEquiv_adjoint_of_bridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv e0
  have hlt : p < Nat.card D := hcard ▸ lt_pow_three_of_prime hp
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hcyc := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  by_cases h2 : q.p = 2
  · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, h2]
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hf2 : 2 ≤ q.exponent := by
      by_contra hlt2
      have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [TauCeti.PrimePower.card_def, h2, h1] at hq3
      omega
    have : CharP K 2 := by
      have : CharP K q.p := inferInstance
      rw [← h2]
      exact this
    obtain ⟨-, Θ, -, -, hker, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        hf2 K hK2
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 hlt
    exact ⟨x, hx, hx1⟩
  by_cases h3 : q.p = 3
  · have hchar : CharP K ReeTag.G2.prime := by
      have : CharP K q.p := inferInstance
      rw [show ReeTag.G2.prime = 3 from rfl, ← h3]
      exact this
    have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, h3]
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form q.exponent_pos K hK3
    have : NeZero (2 * q.exponent) := ⟨by have := q.exponent_pos; omega⟩
    have : IsCyclic (Multiplicative (ZMod (2 * q.exponent))) := inferInstance
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient
      (A := Multiplicative (ZMod (2 * q.exponent))) e Θ hker hp D hD.2 hlt
    exact ⟨x, hx, hx1⟩
  · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
      q.prime_p h2 q.exponent_pos K hK .G2 (Or.inr ⟨rfl, h3⟩)
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 hlt
    exact ⟨x, hx, hx1⟩

end Bridge

end CFSG.HardMathSupport.Timmesfeld.DefChar
