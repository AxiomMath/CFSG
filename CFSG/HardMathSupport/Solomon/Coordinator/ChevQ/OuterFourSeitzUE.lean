module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzD4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem unitarySU_eq_gramSU_one (h : UnitaryFieldData p f K) (n : ℕ) :
    unitarySU p f K n = gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  unitarySU_eq_gramSU h n

@[expose] noncomputable def unitaryPSUEquivPrimeFormOne' (h : UnitaryFieldData p f K) (n : ℕ) :
    unitaryPSU h n ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU_one h n)) (by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU_one h n)).symm z, ⟨c, hcN, hcn, hz⟩,
        MulEquiv.apply_symm_apply _ _⟩)

@[expose] noncomputable def statedProjEquivPrimeFormOne (h : UnitaryFieldData p f K) {n : ℕ}
    (hn : 1 ≤ n) :
    StatedProj (StatedSU n (p ^ f) K) ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  (unitaryPSUEquiv h hn).symm.trans (unitaryPSUEquivPrimeFormOne' h n)

theorem mem_gramSU_one_of_mem (h : UnitaryFieldData p f K) {n : ℕ} {g : GL (Fin n) K}
    (hg : g ∈ StatedSU n (p ^ f) K) :
    g ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hg' : g ∈ unitarySU p f K n := hg
  rwa [unitarySU_eq_gramSU_one h n] at hg'

theorem mem_statedSU_of_mem_gramSU (h : UnitaryFieldData p f K) {n : ℕ} {g : GL (Fin n) K}
    (hg : g ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    g ∈ StatedSU n (p ^ f) K := by
  rw [← unitarySU_eq_gramSU_one h n] at hg
  exact hg

theorem statedProjEquivPrimeFormOne_mk (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n)
    (g : StatedSU n (p ^ f) K) :
    statedProjEquivPrimeFormOne h hn (QuotientGroup.mk g) =
      (QuotientGroup.mk (⟨(g : GL (Fin n) K), mem_gramSU_one_of_mem h g.2⟩ :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have h1 : (unitaryPSUEquiv h hn).symm (QuotientGroup.mk g) = unitaryProj h n g :=
    (MulEquiv.symm_apply_eq _).2 (unitaryPSUEquiv_unitaryProj h hn g).symm
  unfold statedProjEquivPrimeFormOne
  rw [MulEquiv.trans_apply, h1]
  rfl

theorem isEntrywiseProj_congr_primeFormFieldHom (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n)
    (σ : K ≃+* K) :
    IsEntrywiseProj (StatedSU n (p ^ f) K) σ
      (MulAut.congr (statedProjEquivPrimeFormOne h hn).symm
        (primeFormFieldHom h isPrimeFormGram_one σ)) := by
  intro g
  have hmem : glAut σ (g : GL (Fin n) K) ∈ StatedSU n (p ^ f) K :=
    mem_statedSU_of_mem_gramSU h
      (glAut_mem_gramSU h isPrimeFormGram_one σ (mem_gramSU_one_of_mem h g.2))
  refine ⟨⟨glAut σ (g : GL (Fin n) K), hmem⟩, ?_, ?_⟩
  · apply Units.ext
    rw [coe_glAut]
    rfl
  · show (statedProjEquivPrimeFormOne h hn).symm (primeFormFieldHom h isPrimeFormGram_one σ
      (statedProjEquivPrimeFormOne h hn (QuotientGroup.mk g))) = _
    rw [MulEquiv.symm_apply_eq, statedProjEquivPrimeFormOne_mk, statedProjEquivPrimeFormOne_mk]
    change primeFormFieldAut h isPrimeFormGram_one σ _ = _
    rw [primeFormFieldAut_mk]
    rfl

end Unitary

@[expose] def U6EightDiagCubes : Prop :=
  ∀ (K : Type) [Field K] (h : UnitaryFieldData 2 3 K)
    (E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)))),
    IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
    E ≤ primeFormD h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) →
    ¬ E ≤ (MulAut.conj : primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))).range →
    seitzHyperGamma 3 E = ⊤

theorem fieldAutU_of_fieldFactor_ne_one {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 3 K) (hK : Nat.card K = (2 ^ 3) ^ 2)
    (eS : S ≃* StatedProj (StatedSU 6 (2 ^ 3) K)) (φ : MulAut S) (hφ3 : φ ^ 3 = 1)
    (hΘ : primeFormFieldFactor h isPrimeFormGram_one (by norm_num) (by norm_num)
      (MulAut.congr (eS.trans (statedProjEquivPrimeFormOne h (by norm_num))) φ) ≠ 1) :
    FieldAutU 6 S φ := by
  set V := statedProjEquivPrimeFormOne h (n := 6) (by norm_num) with hV
  set β := MulAut.congr (eS.trans V) φ with hβ
  set Θ := primeFormFieldFactor h (n := 6) isPrimeFormGram_one (by norm_num) (by norm_num) with hΘd
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hφ3, map_one]
  have hβ1 : β ≠ 1 := fun h1 => hΘ (by rw [h1, map_one])
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  have hσ3 : (Θ β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hσord : orderOf (Θ β) = 3 := orderOf_eq_prime hσ3 hΘ
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h
      (n := 6) (by norm_num) (by norm_num) Nat.prime_three (by norm_num) β hβord (Θ β) rfl hσord
  refine ⟨K, inferInstance, inferInstance, eS, Θ β,
    MulAut.congr V.symm (primeFormConjHom h _ M)⁻¹, hK, hΘ, ?_, ?_⟩
  · rw [hσord]
    decide
  · have hcomp : MulAut.congr eS φ = MulAut.congr V.symm β := by
      rw [hβ]
      refine MulEquiv.ext fun x => ?_
      simp [MulAut.congr_apply]
    have hconj : MulAut.congr V.symm (primeFormConjHom h _ M)⁻¹ * MulAut.congr eS φ *
        (MulAut.congr V.symm (primeFormConjHom h _ M)⁻¹)⁻¹ =
        MulAut.congr V.symm (primeFormFieldHom h isPrimeFormGram_one (Θ β)) := by
      rw [hcomp, ← hM]
      simp only [map_mul, map_inv, inv_inv]
    rw [hconj]
    exact isEntrywiseProj_congr_primeFormFieldHom h (n := 6) (by norm_num) (Θ β)

section MainU6

set_option linter.unusedSectionVars false


theorem seitz2310FourFreeAt_u6_of (hL : SeitzHyperLie fun d p _ => SeitzGoodIndex p d.1)
    (hD : U6EightDiagCubes) : Seitz2310FourFreeAt IsU6EightIndex (FieldAutU 6) := by
  intro S _ _ d hS hd E hEel hEcard hno
  obtain ⟨d₀, hv⟩ := d
  cases d₀ with
  | twistedA r q =>
    obtain ⟨rfl, hq⟩ := hd
    obtain ⟨e⟩ := hS
    have hmod := CFSG.Models.lieModel_twistedA 5 q hv e
    have hc' : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 5 q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA 5 q
    rw [hc', hf, hq.1, hq.2] at hmod
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmod
    swap
    · omega
    have hpd : (3 : ℕ) ≠ (TauCeti.LieTypeIndex.twistedA 5 q).characteristic := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedA, hq.1]
      norm_num
    by_cases hinn : E ≤ (MulAut.conj : S →* MulAut S).range
    ·
      haveI : IsSimpleGroup S := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity S 6 2 3 hcl).2
      have hnab : ∃ a b : S, a * b ≠ b * a := by
        refine exists_noncomm_of_four_dvd ?_
        rw [card_of_twistedA hv hq e]
        simp only [ordTwistedA]
        decide +kernel
      have hgood : SeitzGoodIndex 3 (.twistedA 5 q) :=
        Or.inr (Or.inr (Or.inr (show FourIndex (.twistedA 5 q) from ⟨hq, Or.inr rfl⟩)))
      have hlist : ¬ P1ThreeLieList 3 ⟨.twistedA 5 q, hv⟩ := by
        intro hl
        obtain ⟨-, q', -, -, h | h⟩ := SeitzBridgeAux.p1_cases hpd hl hgood
        · cases h
        · simp only [TauCeti.LieTypeIndex.twistedA.injEq] at h
          omega
      exact SeitzHyperGoodInAux.seitzHyperGamma_eq_top_of_inner hL Nat.prime_three (by norm_num)
        inferInstance hnab ⟨.twistedA 5 q, hv⟩ e hpd hlist hgood hEel hEcard hinn
    ·
      obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hcl
      have hU : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
      set V := statedProjEquivPrimeFormOne hU (n := 6) (by norm_num) with hV
      set eP : S ≃* primeFormP hU ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := eS.trans V
        with heP
      refine seitzHyperGamma_eq_top_of_congr eP ?_
      obtain ⟨hE'el, hE'c⟩ := map_congr_data eP hEel hEcard
      refine hD K hU _ hE'el hE'c ?_ (fun h => hinn (le_range_conj_of_map_congr eP h))
      rintro _ ⟨φ, hφ, rfl⟩
      rw [← ker_primeFormFieldFactor hU isPrimeFormGram_one (n := 6) (by norm_num) (by norm_num),
        MonoidHom.mem_ker]
      by_contra hΘ
      exact hno φ hφ (fieldAutU_of_fieldFactor_ne_one hU hK eS φ (hEel.2 φ hφ) hΘ)
  | _ => exact hd.elim

end MainU6

section TwistedE6

set_option linter.unusedSectionVars false


@[expose] def TwE6EightDiagCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 3) ^ 2 → ∀ σ : K ≃+* K,
    (∀ c, σ c = c ^ (2 ^ 3)) →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ E ≤ twistedE6Inn K σ →
      seitzHyperGamma 3 E = ⊤

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def derivedCentralQuotientEquivE6 {σ : K ≃+* K}
    (hperf : ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ = twistedE6RootGroup K σ)
    (hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥) :
    DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom) ≃*
      twistedE6RootGroup K σ :=
  have hZ' : Subgroup.center ↥⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : twistedE6RootGroup K σ) ∈ Subgroup.center (twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL TwistTag.E6.tag K) ∈ ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
          twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg (Subtype.val : ↥⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
        twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ → ModGL TwistTag.E6.tag K)
        (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (Subtype.ext
      (congrArg (Subtype.val : twistedE6RootGroup K σ → ModGL TwistTag.E6.tag K) hcen))
  (QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf))

theorem derivedCentralQuotientEquivE6_mk {σ : K ≃+* K}
    (hperf : ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ = twistedE6RootGroup K σ)
    (hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥)
    (g : ↥⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆) :
    derivedCentralQuotientEquivE6 hperf hZ (QuotientGroup.mk g) =
      ⟨(g : ModGL TwistTag.E6.tag K), hperf ▸ g.2⟩ := by
  unfold derivedCentralQuotientEquivE6
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem sixteen_aut_ne_one_and_cube (hK : Nat.card K = (2 ^ 3) ^ 2) {ε : K ≃+* K}
    (hε : ∀ c, ε c = c ^ 16) : ε ≠ 1 ∧ ε ^ 3 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 64 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  have hpow : ∀ c : K, c ^ 64 = c := fun c => by
    have := FiniteField.pow_card c
    rwa [hcard] at this
  refine ⟨fun h1 => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hord : orderOf u = 63 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, Nat.card_eq_fintype_card,
        hcard]
    have h16 : (u : K) ^ 16 = u := by rw [← hε, h1]; rfl
    have h15 : u ^ 15 = 1 := by
      have h' : u ^ 16 = u := Units.ext (by rw [Units.val_pow_eq_pow_val, h16])
      calc u ^ 15 = u ^ 16 * u⁻¹ := by group
        _ = 1 := by rw [h', mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one h15
    rw [hord] at this
    norm_num at this
  · refine RingEquiv.ext fun c => ?_
    rw [pow_three]
    show ε (ε (ε c)) = c
    rw [hε, hε, hε, ← pow_mul, ← pow_mul]
    have : c ^ (16 * 16 * 16) = (c ^ 64) ^ 64 := by rw [← pow_mul]
    rw [this, hpow, hpow]

theorem fieldAutTwE6_of_theta_ne_one {S : Type} [Group S] (hK : Nat.card K = (2 ^ 3) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 3))
    (hperf : ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ = twistedE6RootGroup K σ)
    (hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥)
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (hfa : ∀ (δ : K ≃+* K) (g : twistedE6RootGroup K σ),
      ((fieldActor σ δ g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        Units.map (entrywiseHom δ.toRingHom) g)
    (eC : S ≃* twistedE6RootGroup K σ) (φ : MulAut S) (hφ3 : φ ^ 3 = 1)
    (hΘφ : Θ (MulAut.congr eC φ) ≠ 1) : ∃ r : ℕ, FieldAutTwE6 S (φ ^ r) := by
  set W := derivedCentralQuotientEquivE6 hperf hZ with hW
  set β := MulAut.congr eC φ with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hφ3, map_one]
  obtain ⟨d, hd, -, r, ε, hε, ψ, hψ⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_of_prime_order Nat.prime_two
      (f := 3) (by norm_num) K (by rw [hK]; norm_num) σ hσ Θ hΘ Nat.prime_three (by norm_num) β
      hβ3 hΘφ
  have hd1 : d = 1 := by omega
  subst hd1
  have hε' : ∀ c, ε c = c ^ 16 := fun c => by rw [hε]; norm_num
  obtain ⟨hε1, hε3⟩ := sixteen_aut_ne_one_and_cube hK hε'
  refine ⟨r, K, inferInstance, inferInstance, σ.toRingHom, eC.trans W.symm, ε,
    MulAut.congr W.symm ψ, hK, fun c => hσ c, hε1, ?_, fun g => ?_⟩
  · rw [orderOf_eq_prime hε3 hε1]
    decide
  have hgC : (g : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ := hperf ▸ g.2
  have hmem : Units.map (entrywiseHom ε.toRingHom) (g : ModGL TwistTag.E6.tag K) ∈
      ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom, twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ := by
    have key : ∀ x, x ∈ twistedE6RootGroup K σ → x ∈ ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
        twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ := fun x hx => hperf ▸ hx
    refine key _ ?_
    have h := (fieldActor (t := TwistTag.E6) σ ε (⟨g, hgC⟩ : twistedE6RootGroup K σ)).2
    rwa [hfa] at h
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩
  have hcomp : MulAut.congr W.symm ψ * MulAut.congr (eC.trans W.symm) (φ ^ r) *
      (MulAut.congr W.symm ψ)⁻¹ = MulAut.congr W.symm (fieldActor σ ε) := by
    have h1 : MulAut.congr (eC.trans W.symm) (φ ^ r) = MulAut.congr W.symm (β ^ r) := by
      rw [hβ, ← map_pow]
      refine MulEquiv.ext fun x => ?_
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
        MulEquiv.symm_symm]
    rw [h1, ← hψ]
    simp only [map_mul, map_inv]
  rw [hcomp]
  show W.symm (fieldActor σ ε (W (QuotientGroup.mk g))) = _
  rw [MulEquiv.symm_apply_eq, hW, derivedCentralQuotientEquivE6_mk, derivedCentralQuotientEquivE6_mk]
  exact Subtype.ext (hfa ε ⟨g, hgC⟩)

theorem seitz2310FourFreeAt_twE6_of (hL : SeitzHyperLie fun d p _ => SeitzGoodIndex p d.1)
    (hD : TwE6EightDiagCubes) : Seitz2310FourFreeAt IsTwE6EightIndex FieldAutTwE6 := by
  intro S _ _ d hS hd E hEel hEcard hno
  obtain ⟨d₀, hv⟩ := d
  cases d₀ with
  | twistedE6 q =>
    obtain ⟨e⟩ := hS
    have hq : IsTwoPow q 3 := hd
    obtain ⟨K, _, _, σq, e', hK, hσq⟩ := exists_mulEquiv_twE6 hv hq e
    have hpd : (3 : ℕ) ≠ (TauCeti.LieTypeIndex.twistedE6 q).characteristic := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6, hq.1]
      norm_num
    by_cases hinn : E ≤ (MulAut.conj : S →* MulAut S).range
    ·
      have hm : ChevalleyExceptionalModel S .twistedE6 2 3 :=
        ⟨⟨Nat.prime_two, by norm_num, rfl⟩, K, inferInstance, inferInstance, hK, σq, hσq, ⟨e'⟩⟩
      haveI : IsSimpleGroup S := (CFSG.LieType.Simplicity.fam_2e6_simplicity S 2 3 hm).2
      have hnab : ∃ a b : S, a * b ≠ b * a := by
        refine exists_noncomm_of_four_dvd ?_
        rw [card_of_twE6 hv hq e]
        simp only [ordTwistedE6]
        decide +kernel
      have hgood : SeitzGoodIndex 3 (.twistedE6 q) :=
        Or.inr (Or.inr (Or.inr (show FourIndex (.twistedE6 q) from hq)))
      have hlist : ¬ P1ThreeLieList 3 ⟨.twistedE6 q, hv⟩ := by
        intro hl
        obtain ⟨-, q', -, -, h | h⟩ := SeitzBridgeAux.p1_cases hpd hl hgood
        · cases h
        · cases h
      exact SeitzHyperGoodInAux.seitzHyperGamma_eq_top_of_inner hL Nat.prime_three (by norm_num)
        inferInstance hnab ⟨.twistedE6 q, hv⟩ e hpd hlist hgood hEel hEcard hinn
    ·
      obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two (f := 3)
        (by norm_num) K (by rw [hK]; rfl)
      have hσσq : σ.toRingHom = σq := RingHom.ext fun c => by
        rw [hσq]
        exact hσ c
      subst hσσq
      obtain ⟨-, -, -, -, -, -, hfa, -, ⟨Θ, hΘ, -, hker, -⟩, -, hperf, hZ, -⟩ :=
        twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two
          (by norm_num : 1 ≤ 3) K hK σ hσ
      set eC : S ≃* twistedE6RootGroup K σ := e'.trans (derivedCentralQuotientEquivE6 hperf hZ)
        with heC
      refine seitzHyperGamma_eq_top_of_congr eC ?_
      obtain ⟨hE'el, hE'c⟩ := map_congr_data eC hEel hEcard
      refine hD K hK σ hσ _ hE'el hE'c ?_ (fun h => hinn (le_range_conj_of_map_congr eC h))
      rintro _ ⟨φ, hφ, rfl⟩
      rw [← hker, MonoidHom.mem_ker]
      by_contra hΘφ
      obtain ⟨r, hr⟩ := fieldAutTwE6_of_theta_ne_one hK σ hσ hperf hZ Θ hΘ hfa eC φ
        (hEel.2 φ hφ) hΘφ
      exact hno (φ ^ r) (E.pow_mem hφ r) hr
  | _ => exact hd.elim

end TwistedE6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz
