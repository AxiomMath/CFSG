module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCartanAdj
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.RecipeExcLang CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise commutatorElement


theorem mem_of_pow_three_mul_conj {G : Type*} [Group G] {H : Subgroup G}
    (hcomm : commutator G ≤ H) {δ φ : G}
    (h3 : δ ^ 3 ∈ H) (h2 : δ * (φ * δ * φ⁻¹) ∈ H) : δ ∈ H := by
  classical
  haveI hH : H.Normal := Subgroup.Normal.of_commutator_le G hcomm
  have hc : ⁅φ, δ⁆ ∈ H := by
    have h := (Subgroup.commutator_le.mp hcomm φ (Subgroup.mem_top φ) δ
      (Subgroup.mem_top δ))
    simpa using h
  have h2' : δ * (⁅φ, δ⁆ * δ) ∈ H := by
    have e : φ * δ * φ⁻¹ = ⁅φ, δ⁆ * δ := by
      rw [commutatorElement_def]; group
    rwa [e] at h2
  have hconj : δ * ⁅φ, δ⁆ * δ⁻¹ ∈ H :=
    Subgroup.Normal.conj_mem hH ⁅φ, δ⁆ hc δ
  have h2H : δ ^ 2 ∈ H := by
    have h1 : δ ^ 2 = (δ * ⁅φ, δ⁆ * δ⁻¹)⁻¹ * (δ * (⁅φ, δ⁆ * δ)) := by group
    rw [h1]
    exact mul_mem (inv_mem hconj) h2'
  have hδ : δ = δ ^ 3 * (δ ^ 2)⁻¹ := by group
  rw [hδ]
  exact mul_mem h3 (inv_mem h2H)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] [CharP K 2]

private theorem pow_three_eq_one_of_cartan {A : Matrix ι ι ℤ} (hdet : A.det = 3)
    {x : ι → Kˣ} (hx : ∀ j, ∏ i, x i ^ A i j = 1) : ∀ j, x j ^ 3 = 1 := by
  intro j
  have h := zpow_det_eq_one_of_prod_zpow_eq_one hx j
  rw [hdet] at h
  simpa using h

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
  {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem center_pow_three_eq_one_of_cartan_det_eq_three [CharP L 2]
    (i : KernelComponent χ)
    (hdet : (Matrix.of fun β γ : simpleRoots (componentRoots χ i) =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 3)
    (z : ↥(componentRootSpan L χ i))
    (hz : z ∈ Subgroup.center (componentRootSpan L χ i)) :
    (z : ModGL τ L) ^ 3 = 1 := by
  classical
  obtain ⟨x, hx, hxz⟩ := CFSG.StandardType.LayerCycRoot.exists_mem_ker_of_mem_center
    (K := L) (χ := χ) (i := i) hz
  have hx3 : x ^ 3 = 1 := by
    funext β
    have hx' : CFSG.StandardType.LayerCycRoot.cartanHom (componentRoots χ i) x = 1 :=
      MonoidHom.mem_ker.mp hx
    exact pow_three_eq_one_of_cartan hdet (x := x) (fun j => by
      have := congrFun hx' j
      simpa [CFSG.StandardType.LayerCycRoot.cartanHom_apply, Pi.one_apply] using this) β
  calc (z : ModGL τ L) ^ 3
      = ((CFSG.StandardType.LayerCycRoot.torusDiagHom L).comp
          (CFSG.StandardType.LayerCycRoot.simpleCorootHom (componentRoots χ i)) x) ^ 3 := by
        rw [← hxz]
    _ = ((CFSG.StandardType.LayerCycRoot.torusDiagHom L).comp
          (CFSG.StandardType.LayerCycRoot.simpleCorootHom (componentRoots χ i))) (x ^ 3) := by
        rw [map_pow]
    _ = 1 := by rw [hx3, map_one]

variable {p : ℕ} (S : LangSetup τ L p)

theorem frobGL_step [CharP L 2] (g : ModGL τ L) :
    frobGL (frobeniusEquiv L 2) (S.D.step g) =
      S.D.step (frobGL (frobeniusEquiv L 2) g) := by
  classical
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  have hσc : ∀ c : L, (frobeniusEquiv L 2).toRingHom c = c ^ 2 := fun c => by
    change (frobeniusEquiv L 2 : L ≃+* L) c = c ^ 2
    rw [frobeniusEquiv_apply, frobenius_def]
  have hσP : Units.map (entrywiseHom (frobeniusEquiv L 2).toRingHom) P = P := by
    obtain rfl | ⟨t, ht, hPt⟩ := hP
    · simp
    · cases ht
      rw [hPt]
      exact units_map_entrywiseHom_diagramMap (t := t) (K := L) (σ := frobeniusEquiv L 2)
  have hσn : Units.map (entrywiseHom (frobeniusEquiv L 2).toRingHom) S.D.n = S.D.n := by
    obtain ⟨w, hw⟩ := S.D.n_weyl
    have h := CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8Lift.units_map_entrywiseHom_canonicalRep
      (frobeniusEquiv L 2).toRingHom w
    simpa only [hw] using h
  have hcomp : (frobeniusEquiv L 2).toRingHom.comp Fr =
      Fr.comp (frobeniusEquiv L 2).toRingHom := by
    ext c
    simp only [RingHom.comp_apply]
    rw [hσc, hFr, hFr, hσc, ← pow_mul, ← pow_mul, mul_comm]
  have hσΦ : ∀ g, Units.map (entrywiseHom (frobeniusEquiv L 2).toRingHom) (S.D.Φ g) =
      S.D.Φ (Units.map (entrywiseHom (frobeniusEquiv L 2).toRingHom) g) := by
    intro g
    rw [hΦ g, hΦ (Units.map (entrywiseHom (frobeniusEquiv L 2).toRingHom) g)]
    rw [map_mul, map_mul, map_inv, hσP]
    congr 2
    calc Units.map (entrywiseHom (frobeniusEquiv L 2).toRingHom) (Units.map (entrywiseHom Fr) g)
        = Units.map (entrywiseHom ((frobeniusEquiv L 2).toRingHom.comp Fr)) g := by
          apply Units.ext
          change entrywise (frobeniusEquiv L 2).toRingHom
              (entrywise Fr (g : Module.End L (RootModule τ L))) =
            entrywise ((frobeniusEquiv L 2).toRingHom.comp Fr)
              (g : Module.End L (RootModule τ L))
          exact entrywise_entrywise (frobeniusEquiv L 2).toRingHom Fr _
      _ = Units.map (entrywiseHom (Fr.comp (frobeniusEquiv L 2).toRingHom)) g := by rw [hcomp]
      _ = Units.map (entrywiseHom Fr) (Units.map (entrywiseHom (frobeniusEquiv L 2).toRingHom) g) := by
          apply Units.ext
          change entrywise (Fr.comp (frobeniusEquiv L 2).toRingHom)
              (g : Module.End L (RootModule τ L)) =
            entrywise Fr (entrywise (frobeniusEquiv L 2).toRingHom
              (g : Module.End L (RootModule τ L)))
          exact (entrywise_entrywise Fr (frobeniusEquiv L 2).toRingHom _).symm
  calc frobGL (frobeniusEquiv L 2) (S.D.step g)
      = frobGL (frobeniusEquiv L 2) (S.D.n * S.D.Φ g * S.D.n⁻¹) := rfl
    _ = frobGL (frobeniusEquiv L 2) S.D.n * frobGL (frobeniusEquiv L 2) (S.D.Φ g) *
          (frobGL (frobeniusEquiv L 2) S.D.n)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = S.D.n * S.D.Φ (frobGL (frobeniusEquiv L 2) g) * S.D.n⁻¹ := by
          rw [hσn, hσΦ g]
    _ = S.D.step (frobGL (frobeniusEquiv L 2) g) := rfl

theorem frobGL_mem_model [CharP L 2] {g : ModGL τ L} (hg : g ∈ S.D.model) :
    frobGL (frobeniusEquiv L 2) g ∈ S.D.model := by
  obtain ⟨hgA, hgF⟩ := S.D.mem_model.1 hg
  refine S.D.mem_model.2 ⟨entrywise_mem_adjointGroup (frobeniusEquiv L 2) hgA, ?_⟩
  calc S.D.step (frobGL (frobeniusEquiv L 2) g)
      = frobGL (frobeniusEquiv L 2) (S.D.step g) := (frobGL_step S g).symm
    _ = frobGL (frobeniusEquiv L 2) g := by
        change frobGL (frobeniusEquiv L 2) (S.D.n * S.D.Φ g * S.D.n⁻¹) =
          frobGL (frobeniusEquiv L 2) g
        rw [hgF]

theorem frobGL_mem_Gamma [CharP L 2] {g : ModGL τ L} (hg : g ∈ S.Γ) :
    frobGL (frobeniusEquiv L 2) g ∈ S.Γ := by
  change g ∈ ⁅S.D.model, S.D.model⁆ at hg
  change frobGL (frobeniusEquiv L 2) g ∈ ⁅S.D.model, S.D.model⁆
  have hmap : (⁅S.D.model, S.D.model⁆).map
      (frobGL (frobeniusEquiv L 2)) ≤ ⁅S.D.model, S.D.model⁆ := by
    have hM : S.D.model.map (frobGL (frobeniusEquiv L 2)) ≤ S.D.model := by
      rintro _ ⟨x, hx, rfl⟩
      exact frobGL_mem_model S hx
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hM hM
  exact hmap ⟨g, hg, rfl⟩

theorem frobGL_mem_rationalSpan [CharP L 2] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {g : ModGL τ L}
    (hg : g ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i) :
    frobGL (frobeniusEquiv L 2) g ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  exact Subgroup.mem_inf.2 ⟨frobGL_mem_rootSpan (frobeniusEquiv L 2) h1,
    frobGL_mem_Gamma S h2⟩

theorem frobGL_mem_rationalComponent [CharP L 2] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {g : ModGL τ L}
    (hg : g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    frobGL (frobeniusEquiv L 2) g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  change g ∈ ⁅rationalSpan S.ρ S.Γ (rootCharHom a) i,
    rationalSpan S.ρ S.Γ (rootCharHom a) i⁆ at hg
  change frobGL (frobeniusEquiv L 2) g ∈ ⁅rationalSpan S.ρ S.Γ (rootCharHom a) i,
    rationalSpan S.ρ S.Γ (rootCharHom a) i⁆
  have hmap : (⁅rationalSpan S.ρ S.Γ (rootCharHom a) i,
      rationalSpan S.ρ S.Γ (rootCharHom a) i⁆).map
      (frobGL (frobeniusEquiv L 2)) ≤
      ⁅rationalSpan S.ρ S.Γ (rootCharHom a) i,
        rationalSpan S.ρ S.Γ (rootCharHom a) i⁆ := by
    have hM : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map
        (frobGL (frobeniusEquiv L 2)) ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
      rintro _ ⟨x, hx, rfl⟩
      exact frobGL_mem_rationalSpan S i hx
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hM hM
  exact hmap ⟨g, hg, rfl⟩


private theorem exists_unit_sq_ne_one (L : Type) [Field L] [Infinite L] :
    ∃ s : Lˣ, s ^ 2 ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  refine ⟨Units.mk0 a ha.1, fun h => ?_⟩
  have h2 : a ^ 2 = 1 := by
    have := congrArg Units.val h
    simpa using this
  rcases sq_eq_one_iff.mp h2 with h1 | h1
  · exact ha.2.1 h1
  · exact ha.2.2 h1

theorem frobGL_center_mem_torus [CharP L 2] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {z : ModGL τ L}
    (hzS : z ∈ componentRootSpan L (rootCharHom a) i)
    (hz : ∀ x ∈ componentRootSpan L (rootCharHom a) i, x * z = z * x) :
    z ∈ torusGroup τ L := by
  haveI : Infinite L := IsAlgClosed.instInfinite
  exact unionTorus_le_torusGroup
    (central_mem_unionTorus (χ := rootCharHom a) (i := i)
      (exists_unit_sq_ne_one L)
      (componentRootSpan_le_unionRootSpan (Set.mem_singleton i) hzS) hz)

theorem frobGL_center_eq_sq [CharP L 2] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {z : ModGL τ L}
    (hzS : z ∈ componentRootSpan L (rootCharHom a) i)
    (hz : ∀ x ∈ componentRootSpan L (rootCharHom a) i, x * z = z * x) :
    frobGL (frobeniusEquiv L 2) z = z ^ 2 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (frobGL_center_mem_torus i hzS hz)
  apply Units.ext
  change entrywise (frobeniusEquiv L 2).toRingHom
      (rootDiag l : Module.End L (RootModule τ L)) =
    ((rootDiagUnit τ l : ModGL τ L) ^ 2 : Module.End L (RootModule τ L))
  rw [entrywise_rootDiag]
  change rootDiag (fun i => Units.map (frobeniusEquiv L 2).toRingHom.toMonoidHom (l i)) =
    (rootDiag l) ^ 2
  rw [pow_two, rootDiag_mul_rootDiag]
  congr 1
  funext j
  apply Units.ext
  change (frobeniusEquiv L 2 : L ≃+* L) (l j : L) = ((l * l) j : L)
  rw [frobeniusEquiv_apply, frobenius_def, pow_two]
  rfl

theorem det_cartan_eq_three_of_rank_six
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (σ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hbij : Set.BijOn σ Ψ Ψ)
    (hform : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (σ γ) (σ δ) = iform γ δ)
    (hneg : ∀ γ ∈ Ψ, σ (-γ) = -σ γ)
    (hni : ¬ twistInner Ψ σ)
    (h6 : compRank Ψ = 6) (h72 : Ψ.ncard = 72) :
    (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 3 := by
  classical
  have hf : IsIsometry Ψ σ := ⟨hbij, hform, hneg⟩
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hf' : IsIsometry Ψ fun γ => σ (w • γ) := hf.comp_smul hΨ hw
  have hΨne : Ψ.Nonempty := by
    rcases Ψ.eq_empty_or_nonempty with rfl | hne
    · exfalso
      have : compRank (∅ : Set (Fin τ.rank → ℤ)) = 0 := by simp [compRank]
      rw [this] at h6
      omega
    · exact hne
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (diagramGraph_simpleRoots_connected hΨ hΨne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcardΔ]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨σ (w • (β : Fin τ.rank → ℤ)), hf'.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := by
    intro β γ h
    have h' : σ (w • (β : Fin τ.rank → ℤ)) = σ (w • (γ : Fin τ.rank → ℤ)) :=
      congrArg Subtype.val h
    exact Subtype.ext (hf'.bijOn.injOn (simpleRoots_subset β.2) (simpleRoots_subset γ.2) h')
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ' : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσ'def
  have hσ' : ∀ j, σ (w • (e.symm j : Fin τ.rank → ℤ)) = e.symm (σ' j) := fun j => by
    rw [hσ'def]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, hπe, Equiv.ofBijective_apply, hπ]
  have hσ'M : ∀ i j, t.cartanMatrix (σ' i) (σ' j) = t.cartanMatrix i j := by
    intro i j
    have h1 := he' (e.symm (σ' i)) (e.symm (σ' j))
    have h2 := he' (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, ← hσ', ← hσ']
    exact corootPair_isometry hf' (simpleRoots_subset (e.symm i).2)
      (simpleRoots_subset (e.symm j).2)
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    apply hni
    have hfix : ∀ β ∈ simpleRoots Ψ, σ (w • β) = β := by
      intro β hβ
      have h : σ' (e ⟨β, hβ⟩) = e ⟨β, hβ⟩ := by
        have := congrArg (fun g : Equiv.Perm (Fin t.rank) => g (e ⟨β, hβ⟩)) h1
        simpa using this
      have h2 : e.symm (e ⟨β, hβ⟩) = ⟨β, hβ⟩ := Equiv.symm_apply_apply e _
      have h3 := hσ' (e ⟨β, hβ⟩)
      rw [h2] at h3
      have h4' : e.symm (σ' (e ⟨β, hβ⟩)) = ⟨β, hβ⟩ := by
        rw [h, Equiv.symm_apply_apply]
      rw [h4'] at h3
      exact h3
    obtain ⟨u, hu, hσu⟩ := exists_smul_eq_of_isIsometry hΨ hf hw hfix
    exact ⟨u, componentWeylGroup_le Ψ hu, hσu⟩
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  · have hok : rigidOK t = true := List.all_eq_true.1 Certificates.certificate13659.1 t hmem
    exact absurd (eq_one_of_sepB hok hσ'M) hσ'1
  · have hok : countOK t = true := List.all_eq_true.1 Certificates.certificate13659.2 t hmem
    have hN : Ψ.ncard = t.numRoots := by
      rw [ncard_eq_ncard_orbit hΨ e he', ncard_orbit_of_orbitOK hok]
    have hrank6 : t.rank = 6 := by rw [← hrank, h6]
    have hnum : t.numRoots = 72 := by rw [← hN, h72]
    have htE6 : t = .E6 := by
      simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [TauCeti.DynkinType.rank_A, TauCeti.DynkinType.rank_B,
        TauCeti.DynkinType.rank_C, TauCeti.DynkinType.rank_D, TauCeti.DynkinType.rank_E6,
        TauCeti.DynkinType.rank_E7, TauCeti.DynkinType.rank_E8,
        TauCeti.DynkinType.numRoots_A, TauCeti.DynkinType.numRoots_B,
        TauCeti.DynkinType.numRoots_C, TauCeti.DynkinType.numRoots_D,
        TauCeti.DynkinType.numRoots_E6, TauCeti.DynkinType.numRoots_E7,
        TauCeti.DynkinType.numRoots_E8]
    have hmat : (Matrix.of fun β γ : simpleRoots Ψ =>
        corootPair (β : Fin τ.rank → ℤ) γ) =
        Matrix.submatrix (TauCeti.DynkinType.cartanMatrix t) e e := by
      ext β γ
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      exact he' β γ
    rw [hmat, Matrix.det_submatrix_equiv_self]
    subst htE6
    rw [TauCeti.DynkinType.cartanMatrix_E6, ← cartanE_eq]
    exact det_cartan_E6

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
