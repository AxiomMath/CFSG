module

public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedE6CommonField
public import CFSG.LieType.Chevalley.RankOneFaithful
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedGS

namespace DihedralTwisted

theorem nonempty_mulEquiv_graphFixedRootGroup' {T : Type} [Group T] (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = (p ^ f) ^ t.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    (e : T ≃* DerivedCentralQuotient (twistedFixedGroup t K σ)) :
    Nonempty (T ≃* graphFixedRootGroup t K σ) := by
  have hperf := (finite_fixed_root_group_perfect t hp hf K hcard σ hσ).2.2.1
  have hZ : Subgroup.center (graphFixedRootGroup t K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ.injective)
  have hZ' : Subgroup.center ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL t.tag K) ∈ graphFixedRootGroup t K σ := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : graphFixedRootGroup t K σ) ∈
        Subgroup.center (graphFixedRootGroup t K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL t.tag K) ∈ ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg
        (Subtype.val : ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ → ModGL t.tag K)
        (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2
      (Subtype.ext (congrArg (Subtype.val : graphFixedRootGroup t K σ → ModGL t.tag K) hcen))
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf)))⟩

section Odd

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem orbitRankOneHom_neg_one {a : Fin t.foldedTag.rank} (h : (t.orbit a).card = 1) :
    orbitRankOneHom t K σ a (-1) = torusElt t.tag K (t.orbitMin a) (-1) := by
  have hneg : (-1 : SL2 (orbitField t K σ a)) = HSL (-1) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_HSL]
  rw [hneg, orbitRankOneHom_apply, h]
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    pow_zero, Equiv.Perm.one_apply, map_HSL, rankOneHom_HSL]
  congr 1

theorem ringChar_subfield_ne_two (hK : ringChar K ≠ 2) (L : Subfield K) : ringChar L ≠ 2 := by
  intro h
  have : CharP L 2 := ringChar.of_eq h
  have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
  have h2' : (2 : K) = 0 := by
    have := congrArg L.subtype h2
    rwa [map_ofNat, map_zero] at this
  exact Ring.two_ne_zero hK h2'

theorem exists_sl2_hom_graphFixedRootGroup (hK : ringChar K ≠ 2) {a : Fin t.foldedTag.rank}
    (h : (t.orbit a).card = 1) :
    ∃ φ : SL2 (orbitField t K σ a) →* graphFixedRootGroup t K σ, φ (-1) ≠ 1 := by
  refine ⟨(orbitRankOneHom t K σ a).codRestrict _
    fun g => range_orbitRankOneHom_le a ⟨g, rfl⟩, fun h1 => ?_⟩
  have h1' := congrArg Subtype.val h1
  simp only [MonoidHom.codRestrict_apply, OneMemClass.coe_one] at h1'
  rw [orbitRankOneHom_neg_one h] at h1'
  exact torusElt_neg_one_ne_one hK _ h1'

end Odd

theorem isElementaryAbelian_top_of_sq {G : Type*} [CommGroup G] (h : ∀ x : G, x ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 (⊤ : Subgroup G) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])

theorem sq_eq_one_of_two_eq_zero {K : Type} [Field K] (h2 : (2 : K) = 0) {L : Subfield K}
    (x : Multiplicative L) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [toAdd_pow, toAdd_one, two_nsmul, Subfield.coe_add, ← two_mul, h2, zero_mul]
  rfl

theorem three_le_pRank_of_injective {T C D : Type*} [Group T] [Finite T] [Group C]
    [CommGroup D] (hD : ∀ x : D, x ^ 2 = 1) {r : ℕ} (hcard : Nat.card D = 2 ^ r)
    (φ : D →* C) (hφ : Function.Injective φ) (E : C ≃* T) : r ≤ pRank 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isElementaryAbelian_top_of_sq hD
  let ψ : D →* T := E.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := E.injective.comp hφ
  have hEl := CFSG.IsElementaryAbelian.map (A := (⊤ : Subgroup D)) (p := 2) ψ
  have hcard' : Nat.card ((⊤ : Subgroup D).map ψ) = 2 ^ r := by
    rw [Subgroup.card_map_of_injective hψ, Subgroup.card_top, hcard]
  exact RankOneCenter.le_pRank_of_subgroup hEl hcard'

section Two

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def orbitXRootHom (t : TwistTag) (a : Fin t.foldedTag.rank) :
    Multiplicative (orbitField t K σ a) →* graphFixedRootGroup t K σ :=
  ((adjointGroup t.tag K).subtype.comp (orbitXAdjHom t σ a)).codRestrict _ fun c =>
    graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a c.toAdd)

theorem coe_orbitXRootHom (t : TwistTag) (a : Fin t.foldedTag.rank)
    (c : Multiplicative (orbitField t K σ a)) :
    (orbitXRootHom σ t a c : ModGL t.tag K) = orbitX t K σ a c.toAdd :=
  rfl

theorem orbitXRootHom_injective (t : TwistTag) (a : Fin t.foldedTag.rank) :
    Function.Injective (orbitXRootHom σ t a) := fun c c' h => by
  have h' : (orbitX t K σ a c.toAdd : ModGL t.tag K) = orbitX t K σ a c'.toAdd :=
    congrArg (fun g : graphFixedRootGroup t K σ => (g : ModGL t.tag K)) h
  exact Multiplicative.toAdd.injective (orbitX_injective σ a (Subtype.ext h'))

theorem coe_orbitX_E6_zero (c : orbitField TwistTag.E6 K σ ⟨0, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨0, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K ⟨0, by decide⟩ c * xUnit Tag.E6 K ⟨5, by decide⟩ (σ c) := by
  rw [coe_orbitX]
  have hc : (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 := by decide
  have hm : TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  rw [hc, List.range_succ, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, pow_zero, pow_one, hm]
  rfl

theorem coe_orbitX_E6_three (d : orbitField TwistTag.E6 K σ ⟨3, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨3, by decide⟩ d : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K ⟨1, by decide⟩ d := by
  rw [coe_orbitX_of_card_eq_one (by decide)]
  have hm : TwistTag.E6.orbitMin ⟨3, by decide⟩ = ⟨1, by decide⟩ := by decide
  rw [hm]
  rfl

@[expose] def e6PairHom :
    Multiplicative (orbitField TwistTag.E6 K σ ⟨0, by decide⟩) ×
        Multiplicative (orbitField TwistTag.E6 K σ ⟨3, by decide⟩) →*
      graphFixedRootGroup TwistTag.E6 K σ :=
  MonoidHom.noncommCoprod (orbitXRootHom σ TwistTag.E6 ⟨0, by decide⟩)
    (orbitXRootHom σ TwistTag.E6 ⟨3, by decide⟩) fun c d => Subtype.ext (by
      change (orbitX TwistTag.E6 K σ ⟨0, by decide⟩ c.toAdd : ModGL TwistTag.E6.tag K) *
          orbitX TwistTag.E6 K σ ⟨3, by decide⟩ d.toAdd =
        (orbitX TwistTag.E6 K σ ⟨3, by decide⟩ d.toAdd : ModGL TwistTag.E6.tag K) *
          orbitX TwistTag.E6 K σ ⟨0, by decide⟩ c.toAdd
      exact (commute_orbitX_E6 (fun i hi j hj => by
        revert hi hj
        fin_cases i <;> fin_cases j <;> decide) c.toAdd d.toAdd).eq)

theorem e6PairHom_injective : Function.Injective (e6PairHom σ) := by
  let α : Fin 3 → Fin Tag.E6.rank → ℤ :=
    ![Pi.single ⟨0, by decide⟩ 1, Pi.single ⟨5, by decide⟩ 1, Pi.single ⟨1, by decide⟩ 1]
  have hα : Function.Injective α := by decide
  have hpos : ∀ i, IsRoot Tag.E6 (α i) ∧ 0 < height (α i) := fun i => by
    fin_cases i <;> exact ⟨isRoot_single _ _, by simp [α, height_single]⟩
  have key : ∀ cd, (e6PairHom σ cd : ModGL TwistTag.E6.tag K) =
      (List.ofFn fun i => pinnedX Tag.E6 K (α i)
        (![(cd.1.toAdd : K), σ cd.1.toAdd, (cd.2.toAdd : K)] i)).prod := by
    intro cd
    change (orbitX TwistTag.E6 K σ ⟨0, by decide⟩ cd.1.toAdd : ModGL TwistTag.E6.tag K) *
      orbitX TwistTag.E6 K σ ⟨3, by decide⟩ cd.2.toAdd = _
    rw [coe_orbitX_E6_zero, coe_orbitX_E6_three]
    simp [α, List.ofFn_succ, pinnedX_single]
    exact mul_assoc _ _ _
  intro cd cd' h
  have h' :=
    congrArg (fun g : graphFixedRootGroup TwistTag.E6 K σ => (g : ModGL TwistTag.E6.tag K)) h
  rw [key, key] at h'
  have hγ := (positive_root_product_injectivity Tag.E6 K α hα hpos).2 h'
  have h0 := congrFun hγ 0
  have h2 := congrFun hγ 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    at h0 h2
  exact Prod.ext (Multiplicative.toAdd.injective (Subtype.ext h0))
    (Multiplicative.toAdd.injective (Subtype.ext h2))

end Two

theorem twisted_exclusion (t : TwistTag) {a₀ : Fin t.foldedTag.rank} (ha₀ : (t.orbit a₀).card = 1)
    (htwo : ∀ {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ}, 1 ≤ f → (2 : K) = 0 →
      (∀ a, Nat.card (orbitField t K σ a) = (2 ^ f) ^ (t.orbit a).card) →
      ∃ (D : Type) (_ : CommGroup D) (r : ℕ) (φ : D →* graphFixedRootGroup t K σ),
        (∀ x : D, x ^ 2 = 1) ∧ Nat.card D = 2 ^ r ∧ 3 ≤ r ∧ Function.Injective φ)
    {T : Type} [Group T] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hT : TwistedChevalleyModel T t (p ^ f)) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hT
  obtain ⟨E⟩ := nonempty_mulEquiv_graphFixedRootGroup' t hp hf hcard hσ e
  have : Finite T := Finite.of_equiv _ E.symm.toEquiv
  obtain ⟨hrank, hQ8⟩ :=
    ComponentClassification.SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs
      ⟨P, ⟨eP⟩⟩
  have hm := t.order_pos
  have hchar : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
      (hcard.trans (pow_mul p f t.order).symm)
  obtain ⟨σ', hσ', -, hL, -⟩ := finite_graph_field_parameter_fields t hp hf K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  rw [hσσ'] at hL
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    obtain ⟨D, _, r, φ, hD, hDcard, hr, hφ⟩ := htwo σ hf h2 hL
    have hle := three_le_pRank_of_injective hD hDcard φ hφ E.symm
    omega
  ·
    have hkchar : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    obtain ⟨φ, hφ⟩ := exists_sl2_hom_graphFixedRootGroup (σ := σ) hkchar ha₀
    obtain ⟨H, ⟨eH⟩⟩ := SymplecticExclusion.exists_quaternion_of_sl2_hom
      (ringChar_subfield_ne_two hkchar _) (E.symm.toMonoidHom.comp φ) (by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Ne, map_eq_one_iff _ E.symm.injective]
        exact hφ)
    exact hQ8 ⟨H, ⟨eH⟩⟩

theorem twisted_exclusion_D4 {T : Type} [Group T] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hT : TwistedChevalleyModel T .D4 (p ^ f)) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  refine twisted_exclusion .D4 (a₀ := ⟨1, by decide⟩) (by decide) (fun {K} _ _ σ f hf h2 hL => ?_)
    hp hf hT s hs P
  refine ⟨Multiplicative (orbitField TwistTag.D4 K σ ⟨0, by decide⟩), inferInstance, f * 3,
    orbitXRootHom σ TwistTag.D4 ⟨0, by decide⟩, sq_eq_one_of_two_eq_zero h2, ?_, by omega,
    orbitXRootHom_injective σ _ _⟩
  rw [Nat.card_congr Multiplicative.toAdd, hL, ← pow_mul]
  rfl

theorem twisted_exclusion_E6 {T : Type} [Group T] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hT : TwistedChevalleyModel T .E6 (p ^ f)) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  refine twisted_exclusion .E6 (a₀ := ⟨2, by decide⟩) (by decide) (fun {K} _ _ σ f hf h2 hL => ?_)
    hp hf hT s hs P
  refine ⟨Multiplicative (orbitField TwistTag.E6 K σ ⟨0, by decide⟩) ×
      Multiplicative (orbitField TwistTag.E6 K σ ⟨3, by decide⟩), inferInstance, f * 3,
    e6PairHom σ, fun x => Prod.ext (sq_eq_one_of_two_eq_zero h2 _)
      (sq_eq_one_of_two_eq_zero h2 _), ?_, by omega, e6PairHom_injective σ⟩
  have h0 : (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 := by decide
  have h3 : (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 := by decide
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    hL, hL, h0, h3, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

end DihedralTwisted

open DihedralTwisted

theorem dihedral_sylow_graph_twisted_exceptional_model_exclusion {T : Type} [Group T]
    {t : Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (ht : t = .twistedE6 ∨ t = .trialityD4)
    (hT : ChevalleyExceptionalModel T t p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  obtain ⟨⟨hp, hf, -⟩, hmodel⟩ := hT
  rcases ht with rfl | rfl
  · exact twisted_exclusion_E6 hp hf hmodel s hs P
  · exact twisted_exclusion_D4 hp hf hmodel s hs P

end CFSG.ComponentClassification.UnbalancingLocal
