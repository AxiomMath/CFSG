module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_inner_of_cyclic_hom {C Q : Type} [Group C] [Group Q] [IsCyclic Q]
    (Θ : MulAut C →* Q) {p : ℕ} (hp : p.Prime)
    (hker : ∀ x : MulAut C, Θ x = 1 → x ^ p = 1 → x ∈ inner C)
    (D : Subgroup (MulAut C)) (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ inner C, x ≠ 1 := by
  classical
  let α : D →* Q := Θ.comp D.subtype
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    have : (x : D) ^ p = 1 := Subtype.ext (hexp x x.2)
    rw [← map_pow, this, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card D = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hrle : Nat.card α.range ≤ p := Nat.le_of_dvd hp.pos hexpα
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle
    have h1 : Nat.card D ≤ p * 1 := by
      rw [hsplit]
      exact Nat.mul_le_mul hrle (by omega)
    omega
  have : Finite α.ker := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hxD : (d : MulAut C) ∈ D := d.2
  exact ⟨d, ⟨hxD, hker d hdk (hexp d hxD)⟩, fun h => hd1' (Subtype.ext h)⟩

theorem exists_inner_transport {S C : Type} [Group S] [Group C] (e : S ≃* C) {p : ℕ}
    (hp : p.Prime) (D : Subgroup (MulAut S)) (hcard : Nat.card D = p ^ 3)
    (hD : ∀ a ∈ D, a ^ p = 1)
    (H : ∀ D' : Subgroup (MulAut C), (∀ a ∈ D', a ^ p = 1) → p < Nat.card D' →
      ∃ x ∈ D' ⊓ inner C, x ≠ 1) :
    ∃ x ∈ D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, x ≠ 1 := by
  set φ := MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := H (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hD a ha, map_one])
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

theorem defCharOuterRankFamTrialityD4 : DefCharOuterRankFam .trialityD4 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  subst hpq
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, -, ⟨eC⟩⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hp2 hf K hK3 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  exact exists_inner_transport e hp D hcard (fun a ha => hD.2 a ha)
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx _ => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact this)
      D' hexp hc)

theorem pow_card_sub_one_compatDiagAutHom_E6 {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    (compatDiagAutHom TwistTag.E6 K σ.toRingHom u) ^ (Nat.card K - 1) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [← map_pow]
  have hu : u ^ (Nat.card K - 1) = 1 := by
    funext a
    refine Units.ext (Subtype.ext ?_)
    have h0 : ((u a : orbitField TwistTag.E6 K σ.toRingHom a) : K) ≠ 0 :=
      (Units.ne_zero (orbitFieldUnit TwistTag.E6 σ.toRingHom (u a)))
    have h := FiniteField.pow_card_sub_one_eq_one _ h0
    rw [← Nat.card_eq_fintype_card] at h
    simp only [Pi.pow_apply, Pi.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
      SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact h
  rw [hu, map_one]

theorem mem_inner_of_mem_inn_sup_diag_E6 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) {x : MulAut (twistedE6RootGroup K σ)}
    (hx : x ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hxp : x ^ p = 1) : x ∈ twistedE6Inn K σ := by
  classical
  have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (twistedE6RootGroup K σ)
  obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  set z := compatDiagAutHom TwistTag.E6 K σ.toRingHom u with hz
  let π := QuotientGroup.mk' (twistedE6Inn K σ)
  have hπy : π y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  have hπz : π z = π x := by
    rw [← hyz, map_mul, hπy, one_mul]
  have h1 : orderOf (π z) ∣ p := by
    rw [hπz]; exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxp, map_one])
  have h2 : orderOf (π z) ∣ Nat.card K - 1 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_card_sub_one_compatDiagAutHom_E6 σ u,
      map_one])
  have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpK
  have h3 : orderOf (π z) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : π x = 1 := by rw [← hπz]; exact orderOf_eq_one_iff.1 h3
  exact (QuotientGroup.eq_one_iff x).1 h4

theorem defCharOuterRankFamTwistedE6 : DefCharOuterRankFam .twistedE6 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  subst hpq
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hpK : ¬ q.p ∣ Nat.card K - 1 := by
    intro h
    have h1 : q.p ∣ Nat.card K := by
      rw [hK2]; exact dvd_pow (dvd_pow_self _ q.exponent_pos.ne') (by norm_num)
    have hpos : 1 ≤ Nat.card K := Nat.card_pos
    have h2 := (Nat.dvd_add_right h).1 (by rwa [Nat.sub_add_cancel hpos])
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  exact exists_inner_transport e hp D hcard (fun a ha => hD.2 a ha)
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx hxp => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact mem_inner_of_mem_inn_sup_diag_E6 σ hp hpK this hxp)
      D' hexp hc)

end CFSG.HardMathSupport.Timmesfeld.DefChar
