module

public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LieType.SeitzGeneration.ExcParabolicModel
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Parab
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Adapters.TauCetiExceptional.ReeBridge

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.BorelTits
open scoped Pointwise

section Ree

variable
  {K : Type} [Field K] [Finite K] {a : ℕ}

theorem exists_conj_le_proper_reeGamma (t : ReeTag) [CharP K t.prime]
    {A R : Subgroup (ModGL t.tag K)} (hAΓ : A ≤ t.reeGamma K a) (hRΓ : R ≤ t.reeGamma K a)
    (hR : R ≠ ⊥) (hRp : IsPGroup t.prime R)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag K))) :
    ∃ y ∈ t.reeGamma K a, ∃ Q : Subgroup (ModGL t.tag K), t.reeFixedBorel K a ≤ Q ∧
      Q ≤ t.reeGamma K a ∧ Q ≠ t.reeGamma K a ∧ A.map (MulAut.conj y).toMonoidHom ≤ Q := by
  have := finite_modGL (τ := t.tag) (K := K)
  have : Fact (Nat.Prime t.prime) := ⟨by cases t <;> decide⟩
  have hH : Holds ↥(t.reeGamma K a) t.prime := by
    have h := holds_reeFixedGroup t K a
    rwa [← reeGamma_eq_reeFixedGroup] at h
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  obtain ⟨T, hT⟩ := (large_Ree_Sylow_opposition t a K w₀ hw₀).1
  have hU : R.subgroupOf (t.reeGamma K a) ≠ ⊥ := fun h =>
    hR ((Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le hRΓ)
  have hUp : IsPGroup t.prime ↥(R.subgroupOf (t.reeGamma K a)) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRΓ).symm
  have hB : (t.reeFixedBorel K a).subgroupOf (t.reeGamma K a) ≤
      Subgroup.normalizer ((T : Subgroup ↥(t.reeGamma K a)) : Set ↥(t.reeGamma K a)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1
      (reeFixedBorel_le_normalizer_reeFixedPosUnipotent (Subgroup.mem_subgroupOf.1 hb)) x
  obtain ⟨g, Q, hQ, hBQ, hNQ⟩ := exists_conj_normalizer_le_proper_of_holds hH T hB hU hUp
  set Q' : Subgroup (ModGL t.tag K) := Q.map (t.reeGamma K a).subtype with hQ'
  have hBQ' : t.reeFixedBorel K a ≤ Q' := fun b hb =>
    ⟨⟨b, (Subgroup.mem_inf.1 hb).2⟩, hBQ (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hQ'ne : Q' ≠ t.reeGamma K a := by
    intro h
    refine hQ (eq_top_iff.2 fun x _ => ?_)
    have hx : (x : ModGL t.tag K) ∈ Q' := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  refine ⟨(g : ModGL t.tag K), g.2, Q', hBQ', Subgroup.map_subtype_le Q, hQ'ne, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hy
  have hxN : (⟨x, hAΓ hx⟩ : ↥(t.reeGamma K a)) ∈
      Subgroup.normalizer ((R.subgroupOf (t.reeGamma K a) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hAR hx) z
  exact ⟨_, hNQ ⟨_, hxN, rfl⟩, rfl⟩

section G2

variable [CharP K G2.prime]

theorem eq_reeFixedBorel_of_ne_reeGamma_G2 {Q : Subgroup (ModGL G2.tag K)}
    (hBQ : G2.reeFixedBorel K a ≤ Q) (hQΓ : Q ≤ G2.reeGamma K a) (hne : Q ≠ G2.reeGamma K a) :
    Q = G2.reeFixedBorel K a := by
  obtain ⟨hQ, -⟩ := ree_Borel_overgroup_classification G2 a K Q hBQ hQΓ
  have hsub : ∀ j k : Fin G2.fixedOrbitCount, j = k := by decide
  by_cases h : ∃ j : Fin G2.fixedOrbitCount,
      canonicalRep (coxeterSystem G2.tag) K (G2.fixedOrbitElement j) ∈ Q
  · exfalso
    obtain ⟨j, hj⟩ := h
    obtain ⟨hΓ, -⟩ := ree_Borel_overgroup_classification G2 a K (G2.reeGamma K a)
      reeFixedBorel_le_reeGamma le_rfl
    have hall : ∀ k : Fin G2.fixedOrbitCount,
        canonicalRep (coxeterSystem G2.tag) K (G2.fixedOrbitElement k) ∈ Q := fun k =>
      hsub k j ▸ hj
    have hle : G2.reeParabolic K a {k | canonicalRep (coxeterSystem G2.tag) K
        (G2.fixedOrbitElement k) ∈ G2.reeGamma K a} ≤ Q :=
      sup_le hBQ ((Subgroup.closure_le _).2 (by rintro _ ⟨k, -, rfl⟩; exact hall k))
    exact hne (le_antisymm hQΓ (hΓ.le.trans hle))
  · push Not at h
    have hJ : {j : Fin G2.fixedOrbitCount | canonicalRep (coxeterSystem G2.tag) K
        (G2.fixedOrbitElement j) ∈ Q} = ∅ := Set.eq_empty_of_forall_notMem fun j hj => h j hj
    rw [hJ, reeParabolic_empty] at hQ
    exact hQ

theorem isCyclic_of_isPGroup_le_reeFixedBorel_G2 (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    [Fact p.Prime] (hp3 : p ≠ 3) {A : Subgroup (ModGL G2.tag K)}
    (hAB : A ≤ G2.reeFixedBorel K a) (hA : IsPGroup p A) : IsCyclic A := by
  have hnormal : ((G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeFixedBorel K a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer reeFixedPosUnipotent_le_reeFixedBorel).2
      reeFixedBorel_le_normalizer_reeFixedPosUnipotent
  obtain ⟨⟨φ, -⟩, -⟩ := small_Ree_positive_torus_action a K hK
  have hH : IsCyclic ↥(G2.reeFixedTorus K a) := isCyclic_of_surjective φ.toMonoidHom φ.surjective
  let f : ↥(G2.reeFixedTorus K a) →* ↥(G2.reeFixedBorel K a) ⧸
      (G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeFixedBorel K a) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion reeFixedTorus_le_reeFixedBorel)
  have hf : Function.Surjective f := fun q => by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    have hb : (b : ModGL G2.tag K) ∈ (G2.reeFixedTorus K a : Set (ModGL G2.tag K)) *
        (G2.reeFixedPosUnipotent K a : Set (ModGL G2.tag K)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (reeFixedTorus_le_reeFixedBorel.trans
        reeFixedBorel_le_normalizer_reeFixedPosUnipotent), ← reeFixedBorel_eq_sup]
      exact b.2
    obtain ⟨h, hh, u, hu, hhu⟩ := hb
    refine ⟨⟨h, hh⟩, ?_⟩
    have e : b = Subgroup.inclusion reeFixedTorus_le_reeFixedBorel ⟨h, hh⟩ *
        ⟨u, reeFixedPosUnipotent_le_reeFixedBorel hu⟩ := Subtype.ext hhu.symm
    rw [e, QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.2 hu)]
    rfl
  have hQ : IsCyclic (↥(G2.reeFixedBorel K a) ⧸
      (G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeFixedBorel K a)) :=
    isCyclic_of_surjective f hf
  let g : ↥A →* ↥(G2.reeFixedBorel K a) ⧸
      (G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeFixedBorel K a) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hAB)
  have hdisj : Disjoint A (G2.reeFixedPosUnipotent K a) :=
    IsPGroup.disjoint_of_ne p 3 hp3 A _ hA
      ((isPGroup_posUnipotent G2.prime G2.tag).to_le inf_le_left)
  refine isCyclic_of_injective g ((injective_iff_map_eq_one g).2 fun x hx => ?_)
  have hxN : Subgroup.inclusion hAB x ∈
      (G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeFixedBorel K a) :=
    (QuotientGroup.eq_one_iff _).1 hx
  have hxU : (x : ModGL G2.tag K) ∈ G2.reeFixedPosUnipotent K a := Subgroup.mem_subgroupOf.1 hxN
  exact Subtype.ext (Subgroup.disjoint_def.1 hdisj x.2 hxU)

theorem rootInvariantGeneration_reeGamma_G2 (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    [Fact p.Prime] (hp3 : p ≠ 3) : RootInvariantGeneration (G2.reeGamma K a) 3 p := by
  intro A R hAΓ hA hcard hRΓ hRp hR hAR
  exfalso
  have := hA
  have := finite_modGL (τ := G2.tag) (K := K)
  obtain ⟨y, -, Q, hBQ, hQΓ, hQne, hAQ⟩ := exists_conj_le_proper_reeGamma G2 hAΓ hRΓ hR hRp hAR
  have hQB := eq_reeFixedBorel_of_ne_reeGamma_G2 hBQ hQΓ hQne
  have hA'p : IsPGroup p (A.map (MulAut.conj y).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  have hcyc := isCyclic_of_isPGroup_le_reeFixedBorel_G2 hK hp3 (hQB ▸ hAQ) hA'p
  have : IsElementaryAbelian p (A.map (MulAut.conj y).toMonoidHom) := IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj y).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact hcard
  have hdvd : Nat.card (A.map (MulAut.conj y).toMonoidHom) ∣ p := by
    rw [← hcyc.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p p _
  have hle := Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd
  nlinarith [(Fact.out : p.Prime).two_le]

end G2

theorem exists_reeGamma_equiv_cat_G2 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (_ : CharP X G2.prime),
      Nat.card X = 3 ^ (2 * m + 1) ∧ Nonempty (Cat ⟨.reeG2 m, hv⟩ ≃* G2.reeGamma X m) := by
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have hmodel : ReeTitsModel (Cat ⟨.reeG2 m, hv⟩) .twistedG2 3 (2 * m + 1) :=
    ⟨⟨Nat.prime_three, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨GaloisField 3 (2 * m + 1), inferInstance, inferInstance, hK, ⟨φ.symm⟩⟩⟩
  obtain ⟨-, -, -, -, hmain⟩ := small_Ree_model_Schreier _ 3 (2 * m + 1) hmodel
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hmodel
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP X G2.prime := by
    have : Fintype X := Fintype.ofFinite X
    exact charP_of_card_eq_prime_pow (p := 3) (f := 2 * m + 1) (by
      rw [← Nat.card_eq_fintype_card, hXcard])
  have ham : a = m := by omega
  subst ham
  obtain ⟨E⟩ := hmain a X hfa hXcard ⟨e2⟩
  exact ⟨X, inferInstance, inferInstance, hchar, hXcard, ⟨E⟩⟩

theorem seitzExcParabolicFor_reeG2 : SeitzExcParabolicFor IsReeG2Index := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨m, rfl⟩, R, hR1, hRp, hRn⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := exists_reeGamma_equiv_cat_G2 hv
  have hp3 : p ≠ 3 := by simpa using hpd
  exact planeGen_of_native e (center_reeGamma_G2_eq_bot hX)
    (rootInvariantGeneration_reeGamma_G2 hX hp3) hE hc hin ⟨R, hR1, by simpa using hRp, hRn⟩

end Ree


end CFSG.LieType.SeitzGeneration
