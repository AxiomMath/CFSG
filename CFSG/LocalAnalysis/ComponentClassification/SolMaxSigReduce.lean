module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Pair

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

theorem altFour_sq_mul : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 →
    a * b * (a * b) = 1 := by
  decide

@[expose] def altFourKlein : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {σ | σ * σ = 1}
  mul_mem' {a b} ha hb := altFour_sq_mul a b ha hb
  one_mem' := mul_one 1
  inv_mem' {a} ha := by
    change a⁻¹ * a⁻¹ = 1
    rw [← mul_inv_rev, show a * a = 1 from ha, inv_one]

theorem card_altFourKlein : Nat.card altFourKlein = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (p := (· ∈ altFourKlein))
    (q := fun σ => σ * σ = 1) (fun _ => Iff.rfl)), Nat.card_eq_fintype_card]
  decide

theorem isKleinFour_of_card {G : Type*} [Group G] (h4 : Nat.card G = 4) (hsq : ∀ g : G, g * g = 1) :
    IsKleinFour G := by
  have hdvd : Monoid.exponent G ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by rw [sq]; exact hsq g
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have : Subsingleton G := Monoid.exp_eq_one_iff.mp h
    have h1 := Nat.card_unique (α := G)
    omega
  · exact h

theorem isKleinFour_prod : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  isKleinFour_of_card (by rw [Nat.card_prod]; simp [Nat.card_eq_fintype_card, ZMod.card])
    (by decide)

theorem exists_lift_two_subgroup {G Q : Type*} [Group G] [Group Q] [Finite G] (f : G →* Q)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) (V : Subgroup Q)
    (hV : IsPGroup 2 V) :
    ∃ P : Subgroup G, P.map f = V ∧ ∀ x ∈ P, f x = 1 → x = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ := V.comap f with hP₀
  let f₀ : P₀ →* V := (f.comp P₀.subtype).codRestrict V fun x => x.2
  have hf₀ : Function.Surjective f₀ := by
    rintro ⟨v, hv⟩
    obtain ⟨g, rfl⟩ := hf v
    exact ⟨⟨g, hv⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 P₀) := inferInstance
  have himg : (S : Subgroup P₀).map f₀ = ⊤ := by
    have hV' : IsPGroup 2 (⊤ : Subgroup V) := hV.of_equiv Subgroup.topEquiv.symm
    have h1 := (Sylow.mapSurjective hf₀ S).3 hV' le_top
    rw [Sylow.coe_mapSurjective] at h1
    exact h1.symm
  have hSk : ∀ x ∈ (S : Subgroup P₀), f₀ x = 1 → x = 1 := by
    intro x hx hx1
    have hxk : x ∈ (S : Subgroup P₀) ⊓ f₀.ker := ⟨hx, hx1⟩
    have hcop : Nat.Coprime (Nat.card (S : Subgroup P₀)) (Nat.card f₀.ker) := by
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      rw [hk]
      have hk' : Nat.card f₀.ker = Nat.card f.ker := by
        refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(x : P₀), ?_⟩) ⟨?_, ?_⟩)
        · rw [MonoidHom.mem_ker]
          exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
        · intro a b hab
          exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
        · rintro ⟨g, hg⟩
          have hgV : g ∈ P₀ := by
            show f g ∈ V
            rw [MonoidHom.mem_ker.mp hg]
            exact one_mem V
          refine ⟨⟨⟨g, hgV⟩, ?_⟩, rfl⟩
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (MonoidHom.mem_ker.mp hg)
      rw [hk']
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hker)
    rw [disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)] at hxk
    exact hxk
  refine ⟨(S : Subgroup P₀).map P₀.subtype, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact x.2
    · intro hq
      have hq' : (⟨q, hq⟩ : V) ∈ (S : Subgroup P₀).map f₀ := himg ▸ mem_top _
      obtain ⟨x, hx, hxq⟩ := hq'
      exact ⟨(x : G), ⟨x, hx, rfl⟩, congrArg Subtype.val hxq⟩
  · rintro _ ⟨x, hx, rfl⟩ hx1
    have := hSk x hx (Subtype.ext hx1)
    rw [this]
    rfl

theorem exists_four_subgroup_of_alt {X : Type} [Group X] [Finite X] (J : Subgroup X) {n : ℕ}
    (hn : 4 ≤ n) (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) :
    ∃ E : Subgroup X, E ≤ J ∧ Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      ∃ D : Finset (Fin n), D.card = 4 ∧ ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hn) with hDdef
  have hD : D.card = 4 := by rw [hDdef, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcardD : Fintype.card ↥D = 4 := by rw [Fintype.card_coe, hD]
  let ψ : alternatingGroup ↥D ≃* alternatingGroup (Fin 4) :=
    (Fintype.equivFinOfCardEq hcardD).altCongrHom
  set V : Subgroup (alternatingGroup (Fin n)) :=
    (altFourKlein.map ψ.symm.toMonoidHom).map (alternatingGroup.ofSubtype D) with hVdef
  have hVsupp : ∀ σ ∈ V, ∀ ω ∉ D, (σ : Equiv.Perm (Fin n)) ω = ω := by
    rintro _ ⟨τ, -, rfl⟩ ω hω
    have h1 := (alternatingGroup.mem_range_ofSubtype_iff D (alternatingGroup.ofSubtype D τ)).mp
      ⟨τ, rfl⟩
    by_contra hc
    exact hω (h1 (Equiv.Perm.mem_support.mpr hc))
  have hinj : Function.Injective
      ((alternatingGroup.ofSubtype D).comp ψ.symm.toMonoidHom) :=
    alternatingGroup.ofSubtype_injective.comp ψ.symm.injective
  have hVe : V ≃* altFourKlein := by
    rw [hVdef, Subgroup.map_map]
    exact (altFourKlein.equivMapOfInjective _ hinj).symm
  have hV4 : Nat.card V = 4 := by rw [Nat.card_congr hVe.toEquiv, card_altFourKlein]
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hVsq : ∀ σ ∈ V, σ * σ = 1 := by
    rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    have hτ' : τ * τ = 1 := hτ
    rw [← map_mul, ← map_mul, hτ', map_one, map_one]
  let f : J →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 J))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 J))
  have hfker : f.ker = pPrimeCore 2 J := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (pPrimeCore 2 J) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : Odd (Nat.card f.ker) := by
    rw [hfker]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨P, hPV, hPinj⟩ := exists_lift_two_subgroup f hf hker V hV2
  have hPcard : Nat.card P = 4 := by
    have h1 : Function.Injective (f.comp P.subtype) := by
      intro a b hab
      have hab' : f ((a : J) * (b : J)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr hab
      have := hPinj _ (mul_mem a.2 (inv_mem b.2)) hab'
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have h2 : (f.comp P.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPV]
    rw [← hV4, ← h2]
    exact Nat.card_congr (MonoidHom.ofInjective h1).toEquiv
  refine ⟨P.map J.subtype, map_subtype_le P, ?_, D, hD, fun x hx ω hω => ?_⟩
  · have hE4 : Nat.card (P.map J.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective J.subtype_injective, hPcard]
    have hEsq : ∀ g : P.map J.subtype, g * g = 1 := by
      rintro ⟨_, ⟨p, hp, rfl⟩⟩
      apply Subtype.ext
      have hfp : f p ∈ V := hPV ▸ mem_map_of_mem f hp
      have h1 : f (p * p) = 1 := by rw [map_mul, hVsq _ hfp]
      have := hPinj _ (mul_mem hp hp) h1
      change (p : X) * p = 1
      rw [← Subgroup.coe_mul, this]
      rfl
    have := isKleinFour_of_card hE4 hEsq
    have := isKleinFour_prod
    exact IsKleinFour.nonempty_mulEquiv
  · obtain ⟨p, hp, hpx⟩ := hx
    have hpx' : p = x := Subtype.ext hpx
    subst hpx'
    have hfp : f p ∈ V := hPV ▸ mem_map_of_mem f hp
    exact hVsupp _ hfp ω hω

@[expose] def SignalizerCompletionTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X) (n : ℕ), Sol78.IsSolomonPair t J n →
    ∀ (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X), E ≤ J →
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      (∃ D : Finset (Fin n), D.card = 4 ∧ ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω =
          ω) →
    ∀ y : X, orderOf y = 2 → y ∈ centralizer (E : Set X) →
      y ∈ UnbalancedLayer.coreActionKernel J → y ∉ J →
      Sol78.signalizerCompletion E (E ⊔ zpowers y) = ⊥

theorem signalizerTrivialityInput_of_completion (hmax : SolAltLit.MaximalAltComponentInput)
    (h36 : SignalizerCompletionTrivial) : SolAltLit.SignalizerTrivialityInput := by
  intro X _ _ _ hna hK hz hU t₀ K₀ m h₀ hm hm9
  obtain ⟨t, J, n, hP⟩ := Sol78.exists_isSolomonPair hmax hna hK hz hU ⟨t₀, K₀, m, h₀, hm, hm9⟩
  have hP' := hP
  obtain ⟨hJ, hn, hn9, hmaxn, -, -⟩ := hP'
  obtain ⟨e⟩ := hJ.2.2.2
  obtain ⟨E, hEJ, hE, hD⟩ := exists_four_subgroup_of_alt J (by omega) e
  refine ⟨t, J, n, hJ, hn, hn9, hmaxn, e, E, hEJ, hE, hD, fun y hy hyE hyK hyJ b hb hb1 => ?_⟩
  have hW := h36 X hna hK hz hU t J n hP e E hEJ hE hD y hy hyE hyK hyJ
  rw [eq_bot_iff, ← hW]
  exact le_iSup₂_of_le (f := fun (c : X) (_ : c ∈ E ⊔ zpowers y) =>
    ⨆ (_ : c ≠ 1), SolAltLit.thetaFunctor E c) b hb (le_iSup_of_le hb1 le_rfl)

end CFSG.ComponentClassification.SolMax
