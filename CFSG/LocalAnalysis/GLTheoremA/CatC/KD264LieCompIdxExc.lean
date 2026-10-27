module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOutF4
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutG2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4B2Two
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightTorBase
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace ExcUntw

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

section Defs

@[expose] def RationalCatalogue {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧
    CatalogueOver (ringChar L) (S.D.q ^ j) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def ExcUntwRationalCatalogueAt (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          RationalCatalogue S i

@[expose] def ExcUntwRationalCatalogue : Prop :=
  ∀ (τ : Tag), (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ExcUntwRationalCatalogueAt τ

end Defs

section Inndiag

theorem exists_inndiag_of_mem_inner {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (β : MulAut ↥(adjointGroup τ K)) (hβinn : β ∈ inner ↥(adjointGroup τ K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1 := by
  obtain ⟨g, rfl⟩ := hβinn
  have hgp : g ^ p = 1 := by
    have : MulAut.conj (g ^ p) = MulAut.conj 1 := by rw [map_pow, hβp, map_one]
    exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
  refine ⟨(g : ModGL τ K), adjointGroup_le_inndiagGroup g.2, fun c => ?_, ?_, ?_⟩
  · simp [MulAut.conj_apply]
  · rw [← Subgroup.coe_pow, hgp]
    rfl
  · intro h1
    apply hβ1
    have : g = 1 := Subtype.ext h1
    rw [this, map_one]

theorem exists_inndiag_of_mem_innAutDerived_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (β : MulAut ↥(adjointGroup τ K)) (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1 := by
  classical
  obtain ⟨Θ, -, -, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  have hcomm : ∀ x y : RingAut K × Multiplicative (ZMod (exactE τ)), x * y = y * x := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩
    exact Prod.ext (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K x1 y1) (mul_comm x2 y2)
  have hinner : inner ↥(adjointGroup τ K) ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    refine (hker _).2 ⟨g, 1, fun h => ?_⟩
    simp [rootDiagUnit_one, MulAut.conj_apply]
  have hle : innAutDerived ↥(adjointGroup τ K) ≤ Θ.ker :=
    sup_le hinner (CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_commutator_le_ker Θ hcomm)
  obtain ⟨g, a, hga⟩ := (hker β).1 (hle hβmem)
  have hw : (g : ModGL τ K) * rootDiagUnit τ a ∈ inndiagGroup τ K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  have hβw : ∀ c : adjointGroup τ K, (β c : ModGL τ K) =
      ((g : ModGL τ K) * rootDiagUnit τ a) * c * ((g : ModGL τ K) * rootDiagUnit τ a)⁻¹ := by
    intro c
    rw [hga c]
    group
  obtain ⟨h', hh', hβh', hh'p⟩ := exists_inndiag_pow_eq_one hτ hp β hβp hw hβw
  refine ⟨h', hh', hβh', hh'p, ?_⟩
  rintro rfl
  apply hβ1
  refine MulEquiv.ext fun c => Subtype.ext ?_
  rw [hβh' c]
  simp

theorem exists_inndiag_of_mem_innAutDerived_F4 {K : Type} [Field K]
    [Finite K] {p : ℕ} (β : MulAut ↥(adjointGroup .F4 K))
    (hβmem : β ∈ innAutDerived ↥(adjointGroup .F4 K)) (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup .F4 K, (∀ c : adjointGroup .F4 K, (β c : ModGL .F4 K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  exact exists_inndiag_of_mem_inner β
    (CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_innAutDerived_le_inner_F4 hℓ f.pos hK hβmem)
    hβp hβ1

theorem exists_inndiag_of_mem_innAutDerived_G2 {K : Type} [Field K] [Finite K]
    (hK3 : 3 ≤ Nat.card K) {p : ℕ} (β : MulAut ↥(adjointGroup .G2 K))
    (hβmem : β ∈ innAutDerived ↥(adjointGroup .G2 K)) (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup .G2 K, (∀ c : adjointGroup .G2 K, (β c : ModGL .G2 K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  refine exists_inndiag_of_mem_inner β ?_ hβp hβ1
  by_cases h3 : ringChar K = 3
  · haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := by
      have : CharP K (ringChar K) := ringChar.charP K
      rw [h3] at this
      exact this
    have hK' : Nat.card K = 3 ^ (f : ℕ) := by rw [hK, h3]
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      G2_three_exact_automorphism_normal_form f.pos K hK'
    have hle : innAutDerived ↥(adjointGroup .G2 K) ≤ Θ.ker := by
      refine sup_le ?_
        (CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_commutator_le_ker Θ fun a b => mul_comm a b)
      rw [hker]
      exact le_rfl
    have := hle hβmem
    rw [hker] at this
    exact this
  · have hK4 : 4 ≤ Nat.card K := by
      by_contra h4
      have hK3' : Nat.card K = 3 := by omega
      apply h3
      have hdvd : ringChar K ∣ 3 := by
        rw [← hK3', hK]
        exact dvd_pow_self _ f.ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hdvd
    exact CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outg2_innAutDerived_le_inner h3 hK4 hβmem

end Inndiag

section Reduction

theorem compIdxAt_adjointGroup {τ : Tag} (hres : ExcUntwRationalCatalogueAt τ)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K)
    (hinn : ∀ β : MulAut ↥(adjointGroup τ K), β ∈ innAutDerived ↥(adjointGroup τ K) →
      β ^ p = 1 → β ≠ 1 → ∃ h ∈ inndiagGroup τ K,
        (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ p = 1 ∧ h ≠ 1)
    {d : TauCeti.LieTypeIndex} (hdc : d.characteristic = ringChar K)
    (hdf : fieldSize d = Nat.card K) : CompIdxAt p d ↥(adjointGroup τ K) := by
  classical
  intro β hβmem hβp hβ1 J hJ
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := hinn β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := fun h' => hpK (by rw [hK, ← h']; exact dvd_pow_self p f.ne_zero)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h' | h' | h'
    · subst h'
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
        (hG2 rfl)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h'])
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr1, hFr2⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ hp hpK hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := by
    intro hτG2
    rw [hSq]
    by_cases hp5 : 5 ≤ p
    · exact Or.inl hp5
    · right
      have hp3 : p = 3 := by
        have h2 := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · rfl
        · exact absurd hp (by norm_num)
      have h3 := hG2 hτG2
      by_contra h4
      have hK3 : Nat.card K = 3 := by omega
      exact hpK (by rw [hK3, hp3])
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  obtain ⟨j, hj, hcat⟩ := hres (AlgebraicClosure K) p₀ S
    ⟨Fr, fun c => by rw [hSq]; exact hFr1 c, hFr2⟩ p hp hp2 a hT hap h1 i hqs
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  obtain ⟨i', ⟨φ⟩, hidx⟩ := hcat.of_mulEquiv eJ.symm
  refine ⟨i', ⟨φ⟩, compRelC_of_idxOver hj ?_⟩
  rw [hdc, hdf, ← hSq, ← hℓL]
  exact hidx

end Reduction

section Generic

@[expose] def InnerRecogOver (ℓ Q : ℕ) (C : Type) [Group C] : Prop :=
  commutator C = ⊤ ∧ CatalogueOver ℓ Q C

theorem commutator_eq_top_of_surjective_innerRecog {X Y : Type*} [Group X] [Group Y]
    (hX : commutator X = ⊤) (g : X →* Y) (hg : Function.Surjective g) : commutator Y = ⊤ := by
  have h1 := congrArg (Subgroup.map g) hX
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective g hg] at h1
  rw [commutator_def]
  exact h1

theorem InnerRecogOver.of_mulEquiv {ℓ Q : ℕ} {X Y : Type} [Group X] [Group Y]
    (h : InnerRecogOver ℓ Q X) (e : X ≃* Y) : InnerRecogOver ℓ Q Y :=
  ⟨commutator_eq_top_of_surjective_innerRecog h.1 e.toMonoidHom e.surjective, h.2.of_mulEquiv e⟩

theorem InnerRecogOver.of_range {ℓ Q : ℕ} {X G : Type} [Group X] [Group G]
    (h : InnerRecogOver ℓ Q X) (Ψ : X →* G) (hker : Ψ.ker ≤ Subgroup.center X)
    {H : Subgroup G} (hrange : Ψ.range = H) : InnerRecogOver ℓ Q ↥H := by
  have hmem : ∀ x, Ψ x ∈ H := fun x => hrange ▸ ⟨x, rfl⟩
  let g : X →* ↥H := Ψ.codRestrict H hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ Ψ.range := hrange ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hgk : g.ker ≤ Subgroup.center X := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  exact ⟨commutator_eq_top_of_surjective_innerRecog h.1 g hg, h.2.of_surjective h.1 g hg hgk⟩

theorem innerRecogOver_sp (E : Type) [Field E] [Fintype E] (m : ℕ) (hm : 2 ≤ m)
    (hne : (m, Fintype.card E) ≠ (2, 2)) :
    InnerRecogOver (ringChar E) (Fintype.card E) ↥(CFSG.Assembly.LowTwoRank.StatedSp m E) :=
  ⟨(spFactorFacts_holds E m hm hne).perfect, catalogueOver_sp E m hm hne⟩

end Generic

section Cover

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {ta : Fin τ.rank → Lˣ}

theorem ratCat_of_innerRecogOver (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      InnerRecogOver (ringChar L) (Nat.card ↥K) ↥(componentRootSpan K (rootCharHom ta) i)) :
    RationalCatalogue S i := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  have hrecσ := hrec (fixSubfield σ) hfin hcard
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom ta) i,
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hrecσ.1)
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  have h := (hrecσ.of_range f hker hRf).2
  rw [hcard] at h
  exact ⟨_, hs0, h⟩

end Cover

section Bridges

open CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports

theorem nonempty_ringEquiv_fixedField_excU {K : Type} [Field K] [Fintype K]
    (d : TauCeti.ValidLieTypeIndex) (hK : Fintype.card K = d.fieldOrder) :
    Nonempty (K ≃+* ↥d.fixedField) := by
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype d.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card (α := d.fixedField), TauCeti.ValidLieTypeIndex.card_fixedField]
    exact hK
  exact ⟨FiniteField.ringEquivOfCardEq hcard⟩

theorem catalogueIdx_statedProj_plus {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 4 ≤ n) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (StatedProj (StatedOmega (StatedQuadPlus n K)) ≃* i.Group) ∧
      IdxOver (ringChar K) (Fintype.card K) i := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : TauCeti.PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (TauCeti.LieTypeIndex.D n q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField_excU (K := K) ⟨.D n q, hv⟩ (by
    simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, hcard])
  refine ⟨.lie ⟨.D n q, hv⟩,
    ⟨(statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) (glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q
        hv).symm⟩, Or.inl ⟨TauCeti.LieTypeIndex.characteristic_D n q, ?_, by simp [suzRee]⟩⟩
  simp [fieldSize, q, TauCeti.PrimePower.card_def, hcard]

theorem catalogueIdx_statedProj_odd {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 3 ≤ n)
    (h2 : ringChar K ≠ 2) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (StatedProj (StatedOmega (StatedQuadOdd n K)) ≃* i.Group) ∧
      IdxOver (ringChar K) (Fintype.card K) i := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : TauCeti.PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (TauCeti.LieTypeIndex.B n q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField_excU (K := K) ⟨.B n q, hv⟩ (by
    simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, hcard])
  refine ⟨.lie ⟨.B n q, hv⟩,
    ⟨(statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadOdd_comp φ)) (glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hv h2
        hn).symm⟩, Or.inl ⟨TauCeti.LieTypeIndex.characteristic_B n q, ?_, by simp [suzRee]⟩⟩
  simp [fieldSize, q, TauCeti.PrimePower.card_def, hcard]

theorem catalogueOver_of_lieModel_plus {X : Type} [Group X] {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .POmegaPlus n p f) :
    CatalogueOver p (p ^ f) X := by
  have hadm := h.admissible
  have hn4 : 4 ≤ n := hadm.2.2
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨-, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    haveI : Fintype K := Fintype.ofFinite K
    have hring : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
    obtain ⟨i, ⟨φ⟩, hi⟩ := catalogueIdx_statedProj_plus (K := K) n hn4
    refine ⟨i, ⟨e.trans φ⟩, ?_⟩
    rw [hring, ← Nat.card_eq_fintype_card, hK] at hi
    exact hi
  all_goals simp [CFSG.Blueprint.chevalleyExceptionalTags, CFSG.Blueprint.reeTitsTags] at ht

theorem catalogueOver_of_lieModel_podd {X : Type} [Group X] {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .POmegaOdd n p f) :
    CatalogueOver p (p ^ f) X := by
  have hadm := h.admissible
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hp2 : p ≠ 2 := hadm.2.2.2
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨-, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    haveI : Fintype K := Fintype.ofFinite K
    have hring : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
    obtain ⟨i, ⟨φ⟩, hi⟩ := catalogueIdx_statedProj_odd (K := K) n hn3 (by rw [hring]; exact hp2)
    refine ⟨i, ⟨e.trans φ⟩, ?_⟩
    rw [hring, ← Nat.card_eq_fintype_card, hK] at hi
    exact hi
  all_goals simp [CFSG.Blueprint.chevalleyExceptionalTags, CFSG.Blueprint.reeTitsTags] at ht

theorem catalogueOver_of_lieModel_E6 {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .E6 0 p f) :
    CatalogueOver p (p ^ f) X := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [CFSG.Blueprint.classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q
      (TauCeti.LieTypeIndex.valid_E6 q) K (by rw [hK, TauCeti.PrimePower.card_def])
    exact ⟨.lie ⟨.E6 q, TauCeti.LieTypeIndex.valid_E6 q⟩, ⟨e.trans b⟩,
      Or.inl ⟨TauCeti.LieTypeIndex.characteristic_E6 q,
        by simp [fieldSize, q, TauCeti.PrimePower.card_def], by simp [suzRee]⟩⟩
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · exact absurd ht (by decide)

theorem catalogueOver_of_lieModel_E7 {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .E7 0 p f) :
    CatalogueOver p (p ^ f) X := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [CFSG.Blueprint.classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q
      (TauCeti.LieTypeIndex.valid_E7 q) K (by rw [hK, TauCeti.PrimePower.card_def])
    exact ⟨.lie ⟨.E7 q, TauCeti.LieTypeIndex.valid_E7 q⟩, ⟨e.trans b⟩,
      Or.inl ⟨TauCeti.LieTypeIndex.characteristic_E7 q,
        by simp [fieldSize, q, TauCeti.PrimePower.card_def], by simp [suzRee]⟩⟩
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · exact absurd ht (by decide)

theorem catalogueOver_of_lieModel_E8 {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .E8 0 p f) :
    CatalogueOver p (p ^ f) X := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [CFSG.Blueprint.classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hv : (TauCeti.LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv K
      (by rw [hK, TauCeti.PrimePower.card_def])
    exact ⟨.lie ⟨.E8 q, hv⟩, ⟨e.trans b⟩,
      Or.inl ⟨TauCeti.LieTypeIndex.characteristic_E8 q,
        by simp [fieldSize, q, TauCeti.PrimePower.card_def], by simp [suzRee]⟩⟩
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · exact absurd ht (by decide)

end Bridges

section DE

open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem innerRecogOver_D {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecogOver p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, catalogueOver_of_lieModel_plus hmodel⟩

theorem innerRecogOver_E6 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 6, edgeE 6 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecogOver p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e6_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, catalogueOver_of_lieModel_E6 hmodel⟩

theorem innerRecogOver_E7 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 7, edgeE 7 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecogOver p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e7_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, catalogueOver_of_lieModel_E7 hmodel⟩

theorem innerRecogOver_E8 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 8 → ι)
    (hgram : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 8, edgeE 8 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecogOver p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 8) hgram hframe
  have hadm : StatedLieAdmissible .E8 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e8_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, catalogueOver_of_lieModel_E8 hmodel⟩

variable {τ : Tag}

theorem ratCat_of_tree (K : KacData τ) {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hTor : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (v : WeylGroup τ) {n : ℕ} (l : Fin n → Option (Fin τ.rank))
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [Field K'] [Finite K'] (p f : ℕ), p.Prime → 0 < f →
      Nat.card K' = p ^ f →
      InnerRecogOver p (p ^ f)
        ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l)))) :
    RationalCatalogue S i := by
  classical
  refine ratCat_of_innerRecogOver S hTor i hinner (fun K' hK' _ => ?_)
  set β : Option (Fin τ.rank) → Fin τ.rank → ℤ := fun x => v • K.extRoot x with hβ
  have hsmulcombo : ∀ n' : Option (Fin τ.rank) → ℕ, v • K.combo n' = ∑ x, (n' x : ℤ) • β x := by
    intro n'
    unfold KacData.combo
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm v ((n' x : ℕ) : ℤ) (K.extRoot x)
  have hset : (fun α => v • α) '' K.rootsOf (Set.range l) = rootsOfFam β (Set.range l) := by
    ext γ
    constructor
    · rintro ⟨γ₀, ⟨hr0, n', hn', hγ⟩, rfl⟩
      refine ⟨IsRoot.smul hr0 v, n', hn', ?_⟩
      rcases hγ with rfl | rfl
      · exact Or.inl (hsmulcombo n')
      · exact Or.inr (by show v • (-K.combo n') = _; rw [smul_neg, hsmulcombo])
    · rintro ⟨hr, n', hn', hγ⟩
      refine ⟨v⁻¹ • γ, ⟨IsRoot.smul hr v⁻¹, n', hn', ?_⟩, smul_inv_smul v γ⟩
      rcases hγ with rfl | rfl
      · left
        rw [← hsmulcombo, inv_smul_smul]
      · right
        rw [smul_neg, ← hsmulcombo, inv_smul_smul]
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan τ K' (rootsOfFam β (Set.range l)) := by
    show rootSpan τ K' (componentRoots (rootCharHom a) i) = _
    rw [hroots, hset]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardK⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardK
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  rw [hK'card]
  exact hrec ↥K' (ringChar L) f hprime f.pos hK'card

theorem ratCat_of_dClass (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
    (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  refine ratCat_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact innerRecogOver_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)

theorem ratCat_of_eClass (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
    (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 6 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = eRootCount c.length →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hlen : ∀ P ∈ trees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  classical
  obtain ⟨v, n, l, hn6, hQ, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount htrees
      (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp i h6 hn
  refine ratCat_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  have hgr : ∀ c d : Fin n, c ≠ d → ¬ edgeE n c d → ¬ edgeE n d c →
      iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
    intro c d hcd h1 h2
    show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
    rw [iform_smul]
    exact hnon c d hcd h1 h2
  have hfr := treeFrames K hframes v l (edgeE n) hE (F := K')
  have hroot : ∀ b, IsRoot τ ((fun x => v • K.extRoot x) b) :=
    fun b => IsRoot.smul (K.isRoot_extRoot b) v
  rcases hQ with rfl | rfl | rfl
  · exact innerRecogOver_E6 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact innerRecogOver_E7 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact innerRecogOver_E8 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr

theorem ratCat_of_inner_nonA_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact ratCat_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i hD.1
      hD.2 hinner
  · exact ratCat_of_eClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_ecount e6_etrees e6_elen (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp
      i hE.1 hE.2 hinner

theorem ratCat_of_inner_nonA_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact ratCat_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner
  · exact ratCat_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_ecount e7_etrees e7_elen (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner

theorem ratCat_of_inner_nonA_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact ratCat_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner
  · exact ratCat_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_ecount e8_etrees e8_elen (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner

end DE

section F4

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi exists_b2Hom hom_block_eq blk spBlock)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_le_sup)
open CFSG.SeitzReduction.SymplecticPilot (isSimpleGroup_commutator_statedSp_two)
open scoped Matrix

theorem innerRecogOver_of_spRange {p f m : ℕ} (hp : p.Prime) (hf : 0 < f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) (hm : 2 ≤ m) (hne : (m, Nat.card K) ≠ (2, 2))
    {G : Type} [Group G] (Ψ : StatedSp m K →* G)
    (hker : Ψ.ker ≤ Subgroup.center (StatedSp m K)) {H : Subgroup G} (hrange : Ψ.range = H) :
    InnerRecogOver p (p ^ f) ↥H := by
  haveI : Fintype K := Fintype.ofFinite K
  have hch : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
  have hne' : (m, Fintype.card K) ≠ (2, 2) := by rwa [← Nat.card_eq_fintype_card]
  have h := (innerRecogOver_sp K m hm hne').of_range Ψ hker hrange
  rwa [hch, ← Nat.card_eq_fintype_card, hK] at h

theorem innerRecogOver_f4_B2 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) (hK3 : 3 ≤ Nat.card K) :
    InnerRecogOver p (p ^ f) ↥(subsystemGroup .F4 K f4LeviB2) := by
  classical
  obtain ⟨W, hW⟩ : ∃ W, SymplecticBlockStandardPair K W
      (rankOne (f4Datum K).rootGroup (f4Node 1)) (rankOne (f4Datum K).rootGroup (f4Node 2)) := by
    by_cases hp2 : p = 2
    · subst hp2
      haveI : CharP K 2 := by
        have := ringChar_eq_of_natCard_eq_pow hp hK hf
        rw [← this]
        haveI : Fintype K := Fintype.ofFinite K
        exact ringChar.charP K
      have hK4 : 4 ≤ Nat.card K := by
        rw [hK] at hK3 ⊢
        rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · interval_cases f
          omega
        · calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      exact f4_spPair_even hK4
    · obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
        (Dv := (f4Datum K).divisible) rfl
      obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
      have hE := f4_chevalleyExtras K O C hC
      exact exists_symplecticBlockStandardPair_rankOne_of_isQuasisimple
        (isQuasisimple_statedSp_two hK3) (two_ne_zero_of_natCard_eq_pow hp hp2 hf hK) hE rfl
        (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12
  have hle := symplecticBlockStandardPair_le_sup hW
  obtain ⟨θ, c, hrange, hker, -, -, hU, hV⟩ := hW
  have hUW : rankOne (f4Datum K).rootGroup (f4Node 1) ≤ W := by
    rw [← hU, ← hrange]
    exact Subgroup.map_le_range _ _
  have hVW : rankOne (f4Datum K).rootGroup (f4Node 2) ≤ W := by
    rw [← hV, ← hrange]
    exact Subgroup.map_le_range _ _
  have hWeq : W = rankOne (f4Datum K).rootGroup (f4Node 1) ⊔
      rankOne (f4Datum K).rootGroup (f4Node 2) := le_antisymm hle (sup_le hUW hVW)
  refine innerRecogOver_of_spRange hp hf hK le_rfl (fun h => ?_)
    ((adjointGroup .F4 K).subtype.comp θ) ?_ ?_
  · have : Nat.card K = 2 := (Prod.mk.inj h).2
    omega
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, hWeq, map_subtype_sup_b2]

theorem innerRecogOver_f4_C3_fam {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 0 < f) (hK : Nat.card K = p ^ f) :
    InnerRecogOver p (p ^ f) ↥(subsystemGroup .F4 K f4LeviC3) := by
  classical
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨ψ0, hψ0a, hψ0b⟩ : ∃ ψ : SL(3, K) →* adjointGroup .F4 K,
      ψ.comp (blk K 0) = ρF (f4Node 2) ∧ ψ.comp (blk K 1) = ρF (f4Node 3) := by
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 2) (j := f4Node 3)
      (k := f4Node 1) f4Node_two_ne_three f4_cartan_23 f4_cartan_32 f4_sl3_witness
    exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 2)) (hρFv (f4Node 3))⟩
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 K →* adjointGroup .F4 K,
      φ.comp (spBlock K 1) = ρF (f4Node 1) ∧ φ.comp (spBlock K 0) = ρF (f4Node 2) := by
    obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    exact ⟨φ, hb1, hb0⟩
  obtain ⟨Ψ, hker, hrange, -⟩ := ClassicalInvolution.Q3.Q3V.weakCT_symplectic_subgroup_of_family
    hadm le_rfl hK (G := adjointGroup .F4 K)
    (fun k => rankOne (f4Datum K).rootGroup (c3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact (f4_commutes_rankOne_one_three b hb a ha).symm)
    (fun k => ρF (c3Node k)) (fun k => ⟨hρFi _, hρFr _⟩)
    (fun _ _ => ψ0)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0a)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0b)
    φ hφl hφs
  refine innerRecogOver_of_spRange hp hf hK (by norm_num) (by simp)
    ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_c3]

theorem innerRecogOver_f4_B3_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    InnerRecogOver 2 (2 ^ 1) ↥(subsystemGroup .F4 K f4LeviB3) := by
  classical
  haveI : CharP K 2 := by
    have := ringChar_eq_of_natCard_eq_pow Nat.prime_two (f := 1) (by rw [hK]; norm_num) Nat.one_pos
    rw [← this]
    haveI : Fintype K := Fintype.ofFinite K
    exact ringChar.charP K
  have hsq := CompsPF4Small.sq_eq_self_of_card_two hK
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hadm : StatedLieAdmissible .PSp 3 2 1 := ⟨Nat.prime_two, le_rfl, by norm_num, by simp⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨ψ0, hψ0a, hψ0b⟩ : ∃ ψ : SL(3, K) →* adjointGroup .F4 K,
      ψ.comp (blk K 0) = ρF (f4Node 1) ∧ ψ.comp (blk K 1) = ρF (f4Node 0) := by
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 1) (j := f4Node 0)
      (k := f4Node 2) f4Node_zero_ne_one.symm f4_cartan_10 f4_cartan_01
      CompsPF4Small.f4_sl3_witness_10_copy
    exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 1)) (hρFv (f4Node 0))⟩
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 K →* adjointGroup .F4 K,
      φ.comp (spBlock K 1) = ρF (f4Node 2) ∧ φ.comp (spBlock K 0) = ρF (f4Node 1) := by
    obtain ⟨φ₀, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    refine ⟨φ₀.comp (CFSG.RankThree.PartTwo.KFacts.sp4Graph K).toMonoidHom, ?_, ?_⟩
    · rw [MonoidHom.comp_assoc, CompsPF4Small.sp4Graph_comp_spBlock_one, hb0]
    · rw [MonoidHom.comp_assoc, CompsPF4Small.sp4Graph_comp_spBlock_zero hsq, hb1]
  obtain ⟨Ψ, hker, hrange, -⟩ := ClassicalInvolution.Q3.Q3V.weakCT_symplectic_subgroup_of_family
    hadm le_rfl hK' (G := adjointGroup .F4 K)
    (fun k => rankOne (f4Datum K).rootGroup (b3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact f4_commutes_rankOne_zero_two a ha b hb)
    (fun k => ρF (b3Node k)) (fun k => ⟨hρFi _, hρFr _⟩)
    (fun _ _ => ψ0)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0a)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0b)
    φ hφl hφs
  refine innerRecogOver_of_spRange Nat.prime_two Nat.one_pos hK' (by norm_num) (by simp)
    ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_b3]

theorem innerRecogOver_f4_B3_even {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 0 < f)
    (hK : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K) :
    InnerRecogOver 2 (2 ^ f) ↥(subsystemGroup .F4 K f4LeviB3) := by
  obtain ⟨W, hW⟩ := f4_linearPair (K := K) (i := f4Node 0) (j := f4Node 1) (k := f4Node 2)
    f4Node_zero_ne_one f4_cartan_01 f4_cartan_10 f4_sl3_witness_01
  obtain ⟨Wsp, hsp⟩ := f4_spPair_even_swap (K := K) hK4
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_even_subgroup hadm le_rfl hK hK4
    (U := fun k => rankOne (f4Datum K).rootGroup (b3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact f4_commutes_rankOne_zero_two a ha b hb)
    (fun i j hij hj => by
      obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
      exact ⟨W, hW⟩)
    (fun i j hi hj => by
      obtain ⟨rfl, rfl⟩ := fin3_end_cases i j hi hj
      exact ⟨Wsp, hsp⟩)
  refine innerRecogOver_of_spRange Nat.prime_two hf hK (by norm_num) (by simp)
    ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_b3]

theorem innerRecogOver_f4_B3_odd_any {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    InnerRecogOver p (p ^ f) ↥(subsystemGroup .F4 K f4LeviB3) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  obtain ⟨hqs, hlie⟩ :=
    CompsPF4Small.b3Frame_model hp hp2 hK (two_ne_zero_of_natCard_eq_pow hp hp2 hf hK)
  set Gs := ⨆ k, rankOne (f4Datum K).rootGroup (b3Node k) with hGs
  refine (InnerRecogOver.of_range (X := ↥Gs)
    ⟨hqs.1.commutator_eq_top, catalogueOver_of_lieModel_podd hlie⟩
    ((adjointGroup .F4 K).subtype.comp Gs.subtype) ?_ ?_)
  · intro x hx
    have : x = 1 := Subtype.ext (Subtype.ext (MonoidHom.mem_ker.mp hx))
    rw [this]
    exact Subgroup.one_mem _
  · rw [MonoidHom.range_comp, Gs.range_subtype, map_subtype_iSup_b3]

theorem innerRecogOver_f4_levi_any {J : Set (Fin (Tag.rank .F4))}
    (hJ : J = f4LeviB3 ∨ J = f4LeviC3) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 0 < f) (hK : Nat.card K = p ^ f) :
    InnerRecogOver p (p ^ f) ↥(subsystemGroup .F4 K J) := by
  rcases hJ with rfl | rfl
  · by_cases hp2 : p = 2
    · subst hp2
      haveI : CharP K 2 := by
        have := ringChar_eq_of_natCard_eq_pow Nat.prime_two hK hf
        rw [← this]
        haveI : Fintype K := Fintype.ofFinite K
        exact ringChar.charP K
      by_cases hK4 : 4 ≤ Nat.card K
      · exact innerRecogOver_f4_B3_even hf hK hK4
      · have hK2 := CompsPF4Small.card_eq_two_of_lt_four hf hK hK4
        have hf1 : f = 1 := by
          rw [hK] at hK2
          exact (Nat.pow_eq_self_iff (by norm_num : 1 < 2)).1 hK2
        subst hf1
        exact innerRecogOver_f4_B3_two hK2
    · exact innerRecogOver_f4_B3_odd_any hp hp2 hK
  · exact innerRecogOver_f4_C3_fam hp hf hK

theorem innerRecogOver_rootSpan_smul {τ : Tag} {K : Type} [Field K] (v : WeylGroup τ)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {p Q : ℕ}
    (h : InnerRecogOver p Q ↥(rootSpan τ K S)) :
    InnerRecogOver p Q ↥(rootSpan τ K ((fun α => v • α) '' S)) := by
  have hmap := (canonical_weyl_root_transport τ K).1 v S hS
  refine h.of_mulEquiv ?_
  exact ((rootSpan τ K S).equivMapOfInjective
    (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).injective).trans
    (MulEquiv.subgroupCongr hmap)

theorem ratCat_of_f4Levi_class_any {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  classical
  refine ratCat_of_innerRecogOver S hTor i hinner (fun K' hfin _ => ?_)
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan Tag.F4 K' ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    show rootSpan Tag.F4 K' (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardf⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardf
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf]
  have hrec := innerRecogOver_f4_levi_any hJ hprime f.pos hK'card
  have hsub : subsystemGroup Tag.F4 ↥K' J = rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 J) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) ↥K'
  rw [hsub] at hrec
  rw [hK'card]
  exact innerRecogOver_rootSpan_smul v (fun α hα => hα.1) hrec

theorem ratCat_of_f4B2_class {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :
    RationalCatalogue S i := by
  classical
  refine ratCat_of_innerRecogOver S hTor i hinner (fun K' hfin hcardK' => ?_)
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan Tag.F4 K' ((fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2) := by
    show rootSpan Tag.F4 K' (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardf⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardf
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf]
  have h3 : 3 ≤ Nat.card ↥K' := hcardK' ▸ hQ
  have hrec := innerRecogOver_f4_B2 hprime f.pos hK'card h3
  have hsub : subsystemGroup Tag.F4 ↥K' f4LeviB2 =
      rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 f4LeviB2) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := f4LeviB2) ↥K'
  rw [hsub] at hrec
  rw [hK'card]
  exact innerRecogOver_rootSpan_smul v (fun α hα => hα.1) hrec

theorem ratCat_of_f4B2_two {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 3)
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalCatalogue S i := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨K', hfin, C, D, hC, hD, hcard, f, hf1, hker, hf2⟩ :=
    exists_inner_cover_derived_two S hT i hinner hQ
  haveI : Fintype ↥K' := Fintype.ofFinite _
  have hcard' : Fintype.card ↥K' = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hch : ringChar L = 2 := by
    have h2 := ringChar_eq_of_natCard_eq_pow Nat.prime_two (K := ↥K') (f := 1)
      (by rw [hcard]; norm_num) Nat.one_pos
    rw [← ringChar_subfield' K', h2]
  have hQ2 : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 := by
    obtain ⟨r, e, hr, -, he, hq⟩ := exists_char_pow S
    have h2 : 2 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
      rw [hq, ← pow_mul]
      exact le_trans hr.two_le (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
    omega
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum ↥K').isFiniteType
    (Dv := (f4Datum ↥K').divisible) rfl
  obtain ⟨Cc, -, hCc⟩ := f4_commutatorFormula ↥K' O
  have hE := f4_chevalleyExtras ↥K' O Cc hCc
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 ↥K' →* adjointGroup .F4 ↥K',
      φ.comp (spBlock ↥K' 1) = ρF (f4Node 1) ∧ φ.comp (spBlock ↥K' 0) = ρF (f4Node 2) := by
    obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    exact ⟨φ, hb1, hb0⟩
  have hφrange : φ.range = rankOne (f4Datum ↥K').rootGroup (f4Node 1) ⊔
      rankOne (f4Datum ↥K').rootGroup (f4Node 2) := by
    rw [ClassicalInvolution.Q3.Q3V.range_eq_sup_of_spBlocks hφs hφl, hρFr, hρFr, sup_comm]
  set n := canonicalRep (coxeterSystem Tag.F4) ↥K' v with hn
  set ψ : StatedSp 2 ↥K' →* ModGL Tag.F4 ↥K' :=
    (MulAut.conj n).toMonoidHom.comp ((adjointGroup .F4 ↥K').subtype.comp φ) with hψ
  have hψrange : ψ.range = C := by
    have hmap := (canonical_weyl_root_transport Tag.F4 ↥K').1 v (parabolicRoots Tag.F4 f4LeviB2)
      (fun α hα => hα.1)
    have hsub : subsystemGroup Tag.F4 ↥K' f4LeviB2 =
        rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 f4LeviB2) :=
      CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := f4LeviB2) ↥K'
    have hCeq : C = rootSpan Tag.F4 ↥K' ((fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2) := by
      rw [hC]
      show rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i) = _
      rw [hroots]
    rw [hCeq, ← hmap, ← hsub, ← map_subtype_sup_b2, ← hφrange, hψ, MonoidHom.range_comp,
      MonoidHom.range_comp]
  set X' : Subgroup (StatedSp 2 ↥K') := commutator (StatedSp 2 ↥K') with hX'
  have hDmap : D = X'.map ψ := by
    rw [hD, ← hψrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hX', commutator_def]
  have hX : LieFactorData 2 ↥X' := spFourTwoFacts_holds ↥K' hcard'
  have hs : IsSimpleGroup ↥X' := isSimpleGroup_commutator_statedSp_two hcard
  have hXp : ⁅X', X'⁆ = X' := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hX.perfect)
  have hperfD : ⁅D, D⁆ = D := by
    rw [hDmap, ← Subgroup.map_commutator, hXp]
  have hRf := le_antisymm hf1 (hf2 hperfD)
  let ψX : ↥X' →* ↥D := (ψ.comp X'.subtype).codRestrict D (fun x => by
    rw [hDmap]
    exact ⟨x, x.2, rfl⟩)
  have hψXsurj : Function.Surjective ψX := by
    rintro ⟨y, hy⟩
    rw [hDmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hΦrange : (f.comp ψX).range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hψXsurj, ← MonoidHom.range_eq_map]
  have hR1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≠ ⊥ := by
    intro h
    have hsimple : IsSimpleGroup (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := hqs.2.1
    haveI := hsimple.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    apply hx
    have : g = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h g.1 g.2)
    rw [this]
    rfl
  set Φ : ↥X' →* ModGL Tag.F4 L := f.comp ψX with hΦ
  have hRΦ : rationalComponent S.ρ S.Γ (rootCharHom a) i = Φ.range := hRf.trans hΦrange.symm
  have hkerΦ : Φ.ker = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal Φ.ker with h | h
    · exact h
    · exfalso
      apply hR1
      rw [hRΦ, Subgroup.eq_bot_iff_forall]
      rintro _ ⟨x, rfl⟩
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
  let eR : ↥X' ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff Φ).1 hkerΦ)).trans
      (MulEquiv.subgroupCongr hRΦ.symm)
  have hcat := (catalogueOver_sp_four_two ↥K' hcard').of_mulEquiv eR
  refine ⟨_, hs0, ?_⟩
  rw [hch, hQ2]
  exact hcat

theorem ratCat_of_inner_nonA_F4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalCatalogue S i := by
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hnonA with ⟨v, hroots, -, -⟩ |
      ⟨v, J, hJ, hroots, -, -⟩
  · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · exact ratCat_of_f4B2_class S hT i v hroots hinner hQ
    · exact ratCat_of_f4B2_two S hT i v hroots hinner (not_le.1 hQ) hqs
  · exact ratCat_of_f4Levi_class_any S hT i v hJ hroots hinner

end F4

section Dispatch

@[expose] def ExcUntwOuterDCatalogueAt (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            2 * compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1)) →
        ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          RationalCatalogue S i

@[expose] def ExcUntwOuterDCatalogue : Prop :=
  ∀ (τ : Tag), (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ExcUntwOuterDCatalogueAt τ

@[expose] def ExcUntwOuterECatalogueAt (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        6 ≤ compRank (componentRoots (rootCharHom a) i) →
        (componentRoots (rootCharHom a) i).ncard =
          eRootCount (compRank (componentRoots (rootCharHom a) i)) →
        ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
          RationalCatalogue S i

@[expose] def ExcUntwOuterECatalogue : Prop :=
  ∀ (τ : Tag), (τ = .E7 ∨ τ = .E8) → ExcUntwOuterECatalogueAt τ

theorem excUntwRationalCatalogueAt_of_outer {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hD : (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ExcUntwOuterDCatalogueAt τ)
    (hE : (τ = .E7 ∨ τ = .E8) → ExcUntwOuterECatalogueAt τ) : ExcUntwRationalCatalogueAt τ := by
  intro L _ _ p₀ S hFr p hp hp2 a hT hap h1 i hq
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact ⟨_, (outer_componentOrbitLength_spec S hT i).1,
      catalogueOver_rationalComponent_typeA S hp hT hap h1 i hA hq⟩
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  ·
    cases τ with
    | G2 => exact (false_of_g2Class_nonAP hp S hpL hTp h1 i hA).elim
    | F4 => exact ratCat_of_inner_nonA_F4 hp hp2 S hT hap h1 i hA hinner hq
    | D4 => exact absurd hτ (by decide)
    | E6 => exact ratCat_of_inner_nonA_E6 S hp hpL hT hTp i hA hinner
    | E7 => exact ratCat_of_inner_nonA_E7 S hp hpL hT hTp i hA hinner
    | E8 => exact ratCat_of_inner_nonA_E8 S hp hpL hT hTp i hA hinner
  ·
    cases τ with
    | G2 => exact (false_of_g2Class_nonAP hp S hpL hTp h1 i hA).elim
    | F4 =>
      rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
      · exact (hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
      · exact (hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
    | D4 => exact absurd hτ (by decide)
    | E6 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
      have hshape := e6_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE'
      · exact (hA hA').elim
      · exact hD (Or.inl rfl) L p₀ S hFr p hp hp2 a hT hap h1 i hD' hinner hq
      · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim
    | E7 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
      have hshape := e7_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE'
      · exact (hA hA').elim
      · exact hD (Or.inr (Or.inl rfl)) L p₀ S hFr p hp hp2 a hT hap h1 i hD' hinner hq
      · exact hE (Or.inl rfl) L p₀ S p hp hp2 a hT hap h1 i hE'.1 hE'.2 hinner
    | E8 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
      have hshape := e8_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE'
      · exact (hA hA').elim
      · exact hD (Or.inr (Or.inr rfl)) L p₀ S hFr p hp hp2 a hT hap h1 i hD' hinner hq
      · exact hE (Or.inr rfl) L p₀ S p hp hp2 a hT hap h1 i hE'.1 hE'.2 hinner

theorem excUntwRationalCatalogue_of_outer (hD : ExcUntwOuterDCatalogue)
    (hE : ExcUntwOuterECatalogue) : ExcUntwRationalCatalogue := by
  intro τ hτ
  exact excUntwRationalCatalogueAt_of_outer hτ (hD τ) (hE τ)

end Dispatch

end ExcUntw

section Main

open ExcUntw CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration

theorem compIdxAt_excUntw_of_rationalCatalogueAt (d : TauCeti.ValidLieTypeIndex) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p ≠ d.1.characteristic)
    (hG2 : (∃ q, d.1 = .G2 q) → ExcUntwRationalCatalogueAt .G2)
    (hF4 : (∃ q, d.1 = .F4 q) → ExcUntwRationalCatalogueAt .F4)
    (hE6 : (∃ q, d.1 = .E6 q) → ExcUntwRationalCatalogueAt .E6)
    (hE7 : (∃ q, d.1 = .E7 q) → ExcUntwRationalCatalogueAt .E7)
    (hE8 : (∃ q, d.1 = .E8 q) → ExcUntwRationalCatalogueAt .E8)
    (hP : isExcUntwistedIdx d.1) : CompIdxAt p d.1 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  cases e with
  | G2 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    have hK3 : 3 ≤ Nat.card K := by
      rw [hK]
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpq : p ≠ q.p := by simpa using hpc
    exact compIdxAt_of_mulEquiv eK.symm (compIdxAt_adjointGroup (hG2 ⟨q, rfl⟩) (τ := .G2)
      (Or.inl rfl) (fun _ => hK3) hp hp2 (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
      (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_G2 hK3 β hβ hβp hβ1)
      (by simp [hchar]) (by rw [hK]; rfl))
  | F4 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpq : p ≠ q.p := by simpa using hpc
    exact compIdxAt_of_mulEquiv eK.symm (compIdxAt_adjointGroup (hF4 ⟨q, rfl⟩) (τ := .F4)
      (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide)) hp hp2
      (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
      (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_F4 β hβ hβp hβ1)
      (by simp [hchar]) (by rw [hK]; rfl))
  | E6 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpq : p ≠ q.p := by simpa using hpc
    exact compIdxAt_of_mulEquiv eK.symm (compIdxAt_adjointGroup (hE6 ⟨q, rfl⟩) (τ := .E6)
      (Or.inr (Or.inr (Or.inl rfl))) (fun h => absurd h (by decide)) hp hp2
      (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
      (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_E (Or.inl rfl) hp β hβ hβp hβ1)
      (by simp [hchar]) (by rw [hK]; rfl))
  | E7 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpq : p ≠ q.p := by simpa using hpc
    exact compIdxAt_of_mulEquiv eK.symm (compIdxAt_adjointGroup (hE7 ⟨q, rfl⟩) (τ := .E7)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun h => absurd h (by decide)) hp hp2
      (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
      (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inl rfl)) hp β hβ
        hβp hβ1)
      (by simp [hchar]) (by rw [hK]; rfl))
  | E8 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpq : p ≠ q.p := by simpa using hpc
    exact compIdxAt_of_mulEquiv eK.symm (compIdxAt_adjointGroup (hE8 ⟨q, rfl⟩) (τ := .E8)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (fun h => absurd h (by decide)) hp hp2
      (by rw [hK]; exact not_dvd_card_of_ne hp hpq)
      (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inr rfl)) hp β hβ
        hβp hβ1)
      (by simp [hchar]) (by rw [hK]; rfl))
  | _ => exact absurd hP (by simp [isExcUntwistedIdx])

theorem lieCompIdx_excUntwisted_of_rationalCatalogue (hres : ExcUntwRationalCatalogue) :
    LieCompIdx isExcUntwistedIdx := fun d _ hp hp2 hpc hP =>
  compIdxAt_excUntw_of_rationalCatalogueAt d hp hp2 hpc
    (fun _ => hres .G2 (Or.inl rfl)) (fun _ => hres .F4 (Or.inr (Or.inl rfl)))
    (fun _ => hres .E6 (Or.inr (Or.inr (Or.inl rfl))))
    (fun _ => hres .E7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (fun _ => hres .E8 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hP

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
