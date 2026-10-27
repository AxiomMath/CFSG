module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.Adapters.TauCetiExceptional.BridgeAll
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem exists_inner_of_elemAbelian_adjointE (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (D : Subgroup (MulAut (adjointGroup τ K)))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ inner (adjointGroup τ K), x ≠ 1 := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨Φ, -, hΦker, hΦcard⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  have hcop : Nat.Coprime p ((Nat.card K - 1) ^ τ.rank) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
  have hkerq : Nat.card Φ.ker ∣ (Nat.card K - 1) ^ τ.rank := by
    have hsurj : Function.Surjective
        (((QuotientGroup.mk' (inner (adjointGroup τ K))).comp
          (rootDiagAutHom τ K)).rangeRestrict) :=
      MonoidHom.rangeRestrict_surjective _
    have h1 := Subgroup.card_dvd_of_surjective hsurj
    rw [← hΦker] at h1
    refine h1.trans ?_
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]
  have hE2 : exactE τ ∣ 2 := by
    rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  let Ψ : D →* RingAut K :=
    (MonoidHom.fst _ _).comp (Φ.comp ((QuotientGroup.mk' (inner (adjointGroup τ K))).comp D.subtype))
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxp : (x : MulAut (adjointGroup τ K)) ^ p = 1 := hexp x x.2
    set y := Φ (QuotientGroup.mk' (inner (adjointGroup τ K)) (x : MulAut (adjointGroup τ K)))
      with hy
    have hy1 : y.1 = 1 := hx
    have hyp : y ^ p = 1 := by
      rw [hy, ← map_pow, ← map_pow, hxp, map_one, map_one]
    have hz : y.2 = 1 := by
      have h1 : y.2 ^ p = 1 := by
        have := congrArg Prod.snd hyp
        simpa using this
      have h2 : orderOf y.2 ∣ exactE τ := by
        have := orderOf_dvd_natCard y.2
        have hne : exactE τ ≠ 0 := by rcases hτ with rfl | rfl | rfl <;> simp [exactE]
        have h3 : Nat.card (Multiplicative (ZMod (exactE τ))) = exactE τ := by
          have : NeZero (exactE τ) := ⟨hne⟩
          rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        rwa [h3] at this
      have h4 : orderOf y.2 ∣ p := orderOf_dvd_of_pow_eq_one h1
      have h5 : orderOf y.2 ∣ 2 := h2.trans hE2
      have h6 : orderOf y.2 ∣ Nat.gcd p 2 := Nat.dvd_gcd h4 h5
      have h7 : Nat.gcd p 2 = 1 := by
        rw [Nat.gcd_comm]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (fun h =>
          hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
      rw [h7] at h6
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)
    have hymem : QuotientGroup.mk' (inner (adjointGroup τ K)) (x : MulAut (adjointGroup τ K)) ∈
        Φ.ker := by
      rw [MonoidHom.mem_ker]
      exact Prod.ext hy1 hz
    have hord1 : orderOf (QuotientGroup.mk' (inner (adjointGroup τ K))
        (x : MulAut (adjointGroup τ K))) ∣ (Nat.card K - 1) ^ τ.rank :=
      (Subgroup.orderOf_dvd_natCard Φ.ker hymem).trans hkerq
    have hord2 : orderOf (QuotientGroup.mk' (inner (adjointGroup τ K))
        (x : MulAut (adjointGroup τ K))) ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxp, map_one])
    have hord : orderOf (QuotientGroup.mk' (inner (adjointGroup τ K))
        (x : MulAut (adjointGroup τ K))) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hord2 hord1
    have hxin : (x : MulAut (adjointGroup τ K)) ∈ inner (adjointGroup τ K) :=
      (QuotientGroup.eq_one_iff (N := inner (adjointGroup τ K)) _).1 (orderOf_eq_one_iff.1 hord)
    exact Subtype.ext (hno x ⟨x.2, hxin⟩)
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hcyc : IsCyclic D := isCyclic_of_injective Ψ hinj
  have hexpD : Monoid.exponent D ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (hexp a a.2)
  rw [IsCyclic.exponent_eq_card] at hexpD
  have := Nat.le_of_dvd hp.pos hexpD
  omega

noncomputable def adjointEquivQuotient {τ : Tag} {K : Type} [Field K] [Finite K] :
    adjointGroup τ K ≃* AdjointQuotient τ K :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (adjointGroup τ K)))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_adjointGroup_eq_bot],
     QuotientGroup.mk_surjective⟩

theorem exists_inner_of_bridge_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex} (hbr : CFSG.TauCetiBridge.UntwistedBridge τ c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (S : Type) [Group S]
    (e0 : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p = q.p) (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) :
    ∃ x ∈ D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, x ≠ 1 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hq2 : q.p ≠ 2 := hpq ▸ hp2
  obtain ⟨eB⟩ := hbr q hv hq2 (GaloisField q.p q.exponent) (by rw [hKq]; simp [TauCeti.PrimePower.card_def])
  let e : S ≃* adjointGroup τ (GaloisField q.p q.exponent) :=
    e0.trans (eB.symm.trans adjointEquivQuotient.symm)
  set φ : MulAut S ≃* MulAut (adjointGroup τ (GaloisField q.p q.exponent)) :=
    MulAut.congr e with hφ
  have hndvd : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    intro h
    have h1 : p ∣ q.p ^ q.exponent := by
      rw [hpq]; exact dvd_pow_self _ q.exponent_pos.ne'
    rw [hKq] at h
    have h2 : p ∣ q.p ^ q.exponent - (q.p ^ q.exponent - 1) := Nat.dvd_sub h1 h
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    rw [Nat.sub_sub_self hpos] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := exists_inner_of_elemAbelian_adjointE hτ hp hp2 hndvd
    (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by
      rw [hcardD]
      simpa using Nat.pow_lt_pow_right hp.one_lt (show 1 < 3 by norm_num))
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

section


theorem defCharOuterRankFamE6 : DefCharOuterRankFam .E6 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E (Or.inl rfl) CFSG.TauCetiBridge.chevalleyBridges.e6 q hv S e0 hp
    hp2 hpq D hD hcard

theorem defCharOuterRankFamE7 : DefCharOuterRankFam .E7 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E (Or.inr (Or.inl rfl)) CFSG.TauCetiBridge.chevalleyBridges.e7 q hv
    S e0 hp hp2 hpq D hD hcard

theorem defCharOuterRankFamE8 : DefCharOuterRankFam .E8 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E (Or.inr (Or.inr rfl)) CFSG.TauCetiBridge.chevalleyBridges.e8 q hv
    S e0 hp hp2 hpq D hD hcard

end

end CFSG.HardMathSupport.Timmesfeld.DefChar
