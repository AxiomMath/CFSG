module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeFixed
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
public import CFSG.LieType.SeitzGeneration.ExtSeitzBridge
import CFSG.CharacterTheory.Semidihedral.FixedFieldData


public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Sec66T (fixSub)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.RankThree.PartOne.SEITZ2 (exists_conj_mem_of_plane_of_cyclic_outer)


section Certs


theorem reeG2_fixed_data {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : K ≃+* K} (hβ : orderOf β = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card (fixSubfield β) = 3 ^ (2 * b + 1) ∧
      ∃ _ : CharP (fixSubfield β) G2.prime,
        Nonempty (↥(fixSub (G2.reeGammaFieldAut K a β)) ≃* G2.reeGamma (fixSubfield β) b) := by
  classical
  obtain ⟨b, hbp, hk, hfix⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.smallRee_fixed_data_odd hK hp hp2 β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP (fixSubfield β) G2.prime := by
    have : Fintype (fixSubfield β) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (p := 3) (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hk])
  refine ⟨b, hbp, hk, hchar, ?_⟩
  have hFix : fixSub (G2.reeGammaFieldAut K a β) =
      (G2.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  exact ⟨(((fixSub (G2.reeGammaFieldAut K a β)).equivMapOfInjective
      (G2.reeGamma K a).subtype (G2.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfix))).trans
    ((G2.reeGamma (fixSubfield β) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := G2.tag) (fixSubfield β).subtype)).symm⟩


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]

theorem isCyclic_outer_reeG2 (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    IsCyclic (Outer (G2.reeGamma K a)) := by
  classical
  obtain ⟨σ₁, -, -, hσ₁top, -, hcyc, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 3 (2 * a + 1)
      Nat.prime_three (by omega) K hK
  let φ : (K ≃+* K) →* Outer (G2.reeGamma K a) :=
    (QuotientGroup.mk' (inner (G2.reeGamma K a))).comp (G2.reeGammaFieldAutHom K a)
  have hsurj : Function.Surjective φ := by
    intro o
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective o
    obtain ⟨x, τ, hα⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.smallReeOuterIsField a ha K hK α
    refine ⟨τ, ?_⟩
    show QuotientGroup.mk (G2.reeGammaFieldAutHom K a τ) = QuotientGroup.mk α
    rw [hα, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := inner (G2.reeGamma K a)) (MulAut.conj x)).2 ⟨x, rfl⟩,
      one_mul]
    rfl
  exact isCyclic_of_surjective φ hsurj


end Certs

@[expose] def SubfieldPairReeG2 :
    Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K G2.prime],
    Nat.card K = 3 ^ (2 * a + 1) → ∀ (β : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p → orderOf β = p →
      ∀ g : G2.reeGamma K a,
        (fixedSubgroup (G2.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
          fixedSubgroup (G2.reeGammaFieldAut K a β) →
        Subgroup.closure ((fixedSubgroup (G2.reeGammaFieldAut K a β) : Set (G2.reeGamma K a)) ∪
          ((fixedSubgroup (G2.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
            Set (G2.reeGamma K a))) = ⊤ ∨
          ¬ p ∣ Nat.card (fixedSubgroup (G2.reeGammaFieldAut K a β))

section Certs2


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]

theorem fieldAutData_reeG2 (hpair : SubfieldPairReeG2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    FieldAutData (G2.reeGamma K a) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (G2.reeGamma K a) := Subtype.finite
  have hcycOut := isCyclic_outer_reeG2 ha hK
  obtain ⟨-, -, -, -, -, hcycAut, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 3 (2 * a + 1)
      Nat.prime_three (by omega) K hK
  let : CommGroup (K ≃+* K) := hcycAut.commGroup
  refine fieldAutData_of_standard (⊤ : Subgroup (MulAut (G2.reeGamma K a)))
    {g | ∃ β : K ≃+* K, orderOf β = p ∧ g = G2.reeGammaFieldAut K a β} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane_of_cyclic_outer hp hcycOut E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    obtain ⟨-, δ, σ, hσord, hδ, -⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp
        (by omega) α hαp (fun ⟨g, hg⟩ => hout g hg.symm)
    refine ⟨δ⁻¹, Subgroup.mem_top _, G2.reeGammaFieldAut K a σ, ⟨σ, hσord, rfl⟩, ?_⟩
    rw [inv_inv, ← hδ]
    group
  · rintro _ ⟨β, hβ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    have hzp := zpowers_ringEquiv_eq_of_orderOf Nat.prime_three (by omega : 1 ≤ 2 * a + 1) hK hβ hτ
    exact fixedSubgroup_eq_of_zpowers_eq (G2.reeGammaFieldAutHom K a) hzp
  · rintro _ ⟨β, hβ, rfl⟩ _ x hx hc
    obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := reeG2_fixed_data hK hp (by omega) hβ
    have hz : eC ⟨x, hx⟩ ∈ Subgroup.center (G2.reeGamma (fixSubfield β) b) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, hy⟩ : ∃ y : ↥(fixSub (G2.reeGammaFieldAut K a β)), eC y = g :=
        ⟨eC.symm g, by simp⟩
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc y.1 y.2).symm
    have hcen := (small_Ree_fixed_group_center_trivial b (fixSubfield β) hbcard).1
    rw [hcen, Subgroup.mem_bot] at hz
    have h1 : (⟨x, hx⟩ : ↥(fixSub (G2.reeGammaFieldAut K a β))) = 1 :=
      eC.injective (by rw [hz, map_one])
    exact congrArg Subtype.val h1
  · rintro _ ⟨β, hβ, rfl⟩ d - hne
    obtain ⟨x, τ, hd⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.smallReeOuterIsField a ha K hK d
    set R := fixedSubgroup (G2.reeGammaFieldAut K a β) with hR
    have hcomm : G2.reeGammaFieldAut K a τ * G2.reeGammaFieldAut K a β *
        (G2.reeGammaFieldAut K a τ)⁻¹ = G2.reeGammaFieldAut K a β := by
      have h := congrArg (G2.reeGammaFieldAutHom K a)
        (show τ * β * τ⁻¹ = β by rw [mul_comm τ β, mul_assoc, mul_inv_cancel, mul_one])
      rw [map_mul, map_mul, map_inv] at h
      simpa only [ReeTag.reeGammaFieldAutHom_apply] using h
    have hτR : R.map (G2.reeGammaFieldAut K a τ).toMonoidHom = R := by
      rw [hR, ← fixedSubgroup_conj, hcomm]
    have hmap : R.map d.toMonoidHom = R.map (MulAut.conj x).toMonoidHom := by
      rw [hd]
      calc R.map (MulAut.conj x * G2.reeGammaFieldAut K a τ).toMonoidHom
          = (R.map (G2.reeGammaFieldAut K a τ).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
            rw [Subgroup.map_map]; rfl
        _ = R.map (MulAut.conj x).toMonoidHom := by rw [hτR]
    rw [hmap] at hne ⊢
    exact hpair a ha K hK β p hp hp5 hβ x hne

theorem exists_reeG2_model {m : ℕ} {K : Type} [Group K] (hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.reeG2 m)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (_ : CharP X G2.prime),
      1 ≤ m ∧ Nat.card X = 3 ^ (2 * m + 1) ∧ Nonempty (K ≃* G2.reeGamma X m) := by
  have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m hiso
  obtain ⟨hv, -⟩ := hiso
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  obtain ⟨hFin, -, -, -, hmain⟩ := small_Ree_model_Schreier K 3 (2 * m + 1) hmodel
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hmodel
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP X G2.prime := by
    have : Fintype X := Fintype.ofFinite X
    exact charP_of_card_eq_prime_pow (p := 3) (f := 2 * m + 1) (by
      rw [← Nat.card_eq_fintype_card, hXcard])
  have ham : a = m := by omega
  subst ham
  obtain ⟨E⟩ := hmain a X hfa hXcard ⟨e2⟩
  exact ⟨X, inferInstance, inferInstance, hchar, hm1, hXcard, ⟨E⟩⟩

open CFSG.LieType.SeitzGeneration in
theorem seitzExcOuterNarrowReeG2_of_pair (hpair : SubfieldPairReeG2) :
    SeitzExcOuterNarrowReeG2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨m, hm⟩⟩
  subst hm
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 : p ≠ 3 := by
      have := hpd
      rwa [show (⟨TauCeti.LieTypeIndex.reeG2 m, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = 3
        from TauCeti.LieTypeIndex.characteristic_reeG2 m] at this
    have := hp.two_le
    have := hp.eq_one_or_self_of_dvd 2
    omega
  obtain ⟨X, _, _, _, ha, hX, ⟨e⟩⟩ := exists_reeG2_model (K := Cat ⟨.reeG2 m, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have := (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple ha X hX).2.1
  have hsimple : IsSimpleGroup (Cat ⟨.reeG2 m, hv⟩) := MulEquiv.isSimpleGroup e
  have hfin : Finite (Cat ⟨.reeG2 m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hel : IsElementaryAbelian p ↥E := isElementaryAbelian_of_isElemAbelian hE
  have hnab := exists_noncommuting_of_isElementaryAbelian_aut hel hc
  have hd : FieldAutData (Cat ⟨.reeG2 m, hv⟩) p :=
    (fieldAutData_reeG2 hpair hp hp5 ha hX).of_mulEquiv e hp
  rw [planeGen_iff_closure_fixUnion]
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc
    (fun hall => hout fun φ hφ => (hall φ hφ).elim fun g hg => ⟨g, hg.symm⟩)

end Certs2

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc
