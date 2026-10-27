module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSpor
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem pPrimeCore_fixedPoints_eq_bot_of_mulAut {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (h : ∀ i : MulAut S, orderOf i = 2 → CFSG.oddCore (centralizer ({i} : Set (MulAut S))) = ⊥)
    {σ : MulAut S} (hσ : orderOf σ = 2) : pPrimeCore 2 ↥(fixedPoints σ) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hκ := CatLeaf.mulAut_conj_injective_of_simple hna
  set C := centralizer ({σ} : Set (MulAut S)) with hCdef
  have hZ : center S = ⊥ := CatLeaf.center_eq_bot_of_simple hna
  have hmem : ∀ s : S, MulAut.conj s ∈ C ↔ σ s = s := fun s =>
    Hin.conj_mem_centralizer_iff hZ σ s
  let φ : ↥(fixedPoints σ) →* C :=
    ((MulAut.conj : S →* MulAut S).comp (fixedPoints σ).subtype).codRestrict C
      fun x => (hmem x).mpr x.2
  have hφ : Function.Injective φ := fun x y hxy =>
    Subtype.ext (hκ (congrArg (fun z : C => (z : MulAut S)) hxy))
  have hrange : φ.range = (OuterAutomorphisms.inner S).subgroupOf C := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨s, hs⟩
      have hsC : MulAut.conj s ∈ C := hs ▸ c.2
      exact ⟨⟨s, (hmem s).mp hsC⟩, Subtype.ext hs⟩
  have hN : ((OuterAutomorphisms.inner S).subgroupOf C).Normal := by
    have := OuterAutomorphisms.inner_normal S
    infer_instance
  have hcore := CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2
    ((OuterAutomorphisms.inner S).subgroupOf C) hN.isSubnormal
  have hC2 : pPrimeCore 2 C = ⊥ := by
    rw [← Sporadic.HeldB.oddCore_eq_pPrimeCore_two']
    exact h σ hσ
  rw [hC2, bot_subgroupOf] at hcore
  let e : ↥(fixedPoints σ) ≃* ↥((OuterAutomorphisms.inner S).subgroupOf C) :=
    (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)
  rw [← Sporadic.HeldB.oddCore_eq_pPrimeCore_two']
  apply Sporadic.HeldB.oddCore_eq_bot_of_mulEquiv e
  rw [Sporadic.HeldB.oddCore_eq_pPrimeCore_two']
  exact hcore

theorem mulAut_oddCore_eq_bot {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier s) (i : MulAut S)
    (hi : orderOf i = 2) : CFSG.oddCore (centralizer ({i} : Set (MulAut S))) = ⊥ := by
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hna
  have hκ := CatLeaf.mulAut_conj_injective_of_simple hna
  let eI : CFSG.generalizedFitting (MulAut S) ≃* S :=
    (MulEquiv.subgroupCongr hF).trans (MonoidHom.ofInjective hκ).symm
  have : IsSimpleGroup (CFSG.generalizedFitting (MulAut S)) := eI.isSimpleGroup
  have hnc : ∃ a b : CFSG.generalizedFitting (MulAut S), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eI.symm x, eI.symm y, fun h => hxy (eI.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact hs (MulAut S) inferInstance hnc ⟨eI.trans e⟩ i hi

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem pPrimeCore_bar_eq_bot (h : Config G p m τ K) {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) (e : G ⧸ center G ≃* NativeSporadic.Carrier s) :
    pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥ := by
  have := h.simple_bar
  exact pPrimeCore_fixedPoints_eq_bot_of_mulAut h.nonabelian_bar
    (fun i hi => mulAut_oddCore_eq_bot hs h.nonabelian_bar e i hi) h.orderOf_bar

theorem exists_small (h : Config G p m τ K) (hO : pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥) :
    ∃ B : Subgroup ↥(fixedPoints (quotAut τ)), IsComponent B ∧ SmallCentralQuotient ↥B := by
  obtain ⟨hB, hL⟩ := h.isComponent_bar hO
  refine ⟨_, hB, Or.inl ⟨p, m, h.prime, h.ne_two, h.one_le, by have := h.seven_le; omega, ?_⟩⟩
  have hs := isSimpleGroup_of_lieModel_psl2 hL
  have hZ := CatLeaf.center_eq_bot_of_simple (nonabelian_of_lieModel_psl2 hL)
  exact GSThmB.OddQuot.lieModel_of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hL

end Config

theorem exists_isComponent_congr {Y : Type} [Group Y] {H H' : Subgroup Y} (hH : H = H')
    {B : Subgroup ↥H} (hB : IsComponent B) (hs : SmallCentralQuotient ↥B) :
    ∃ B' : Subgroup ↥H', IsComponent B' ∧ SmallCentralQuotient ↥B' := by
  subst hH
  exact ⟨B, hB, hs⟩

theorem rowFor_spor_of_comps {s : TauCeti.SporadicName}
    (hodd : CatalogueU.SporadicOddCoreFree s)
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => ¬ SmallCentralQuotient Y)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 →
        α ∉ OuterAutomorphisms.inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) fun Y _ => ¬ SmallCentralQuotient Y) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y s := by
  intro G _ _ p m τ K h ⟨e⟩
  exfalso
  have hsimp := h.simple_bar
  obtain ⟨B, hB, hsB⟩ := h.exists_small (h.pPrimeCore_bar_eq_bot hodd e)
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
  by_cases hinn : quotAut τ ∈ innAut (G ⧸ center G)
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (Hin.conj_injective_of_center hZ) t, ht]
      exact h.orderOf_bar
    have heq : fixedPoints (quotAut τ) = centralizer ({t} : Set (G ⧸ center G)) := by
      rw [Hin.centralizer_eq_fixedPoints_conj, ht]
    obtain ⟨B', hB', hs'⟩ := exists_isComponent_congr heq hB hsB
    exact hin _ ⟨e⟩ t ht2 B' hB' hs'
  · have hsq : quotAut τ * quotAut τ = 1 := by
      have := pow_orderOf_eq_one (quotAut τ)
      rwa [h.orderOf_bar, pow_two] at this
    have heq : fixedPoints (quotAut τ) = Sporadic.Schreier.fixSub (quotAut τ) :=
      (Hin.fixSub_eq_fixedPoints _).symm
    obtain ⟨B', hB', hs'⟩ := exists_isComponent_congr heq hB hsB
    exact hout _ hsimp h.nonabelian_bar ⟨e⟩ _ hsq hinn B' hB' hs'

end CFSG.ComponentClassification.HarrisLit.N36
