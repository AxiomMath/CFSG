module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityPermModule
public import CFSG.LieType.Chevalley.GraphFixedData

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

@[expose] def d4OuterSwap : Equiv.Perm (Fin TwistTag.D4.tag.rank) :=
  (Equiv.swap 1 3 : Equiv.Perm (Fin 4))

theorem d4OuterSwap_cartan (i j : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.tag.cartan (d4OuterSwap i) (d4OuterSwap j) = TwistTag.D4.tag.cartan i j := by
  have h : ∀ i j : Fin 4, (Tag.D4.cartan : Matrix (Fin 4) (Fin 4) ℤ) (Equiv.swap (1 : Fin 4) 3 i)
      (Equiv.swap (1 : Fin 4) 3 j) = (Tag.D4.cartan : Matrix (Fin 4) (Fin 4) ℤ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  exact h i j

theorem d4Perm_mul_outerSwap_mul :
    TwistTag.D4.perm * d4OuterSwap * TwistTag.D4.perm = d4OuterSwap := by
  have h : (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) * Equiv.swap 1 3 *
      (Equiv.swap 0 1 * Equiv.swap 1 3) = Equiv.swap 1 3 := by decide
  exact h

theorem d4OuterSwap_mul_self : d4OuterSwap * d4OuterSwap = 1 := by
  have h : (Equiv.swap 1 3 : Equiv.Perm (Fin 4)) * Equiv.swap 1 3 = 1 := by decide
  exact h

theorem cartan_mul_perm {τ : Tag} {π π' : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)
    (hπ' : ∀ i j, τ.cartan (π' i) (π' j) = τ.cartan i j) :
    ∀ i j, τ.cartan ((π * π') i) ((π * π') j) = τ.cartan i j := fun i j => by
  simp only [Equiv.Perm.mul_apply]
  rw [hπ, hπ']

theorem conj_conj_eq_of_mul_mul_eq {G : Type*} [Group G] (a b g : G) (h : a * b * a = b) :
    a * (b * (a * g * a⁻¹) * b⁻¹) * a⁻¹ = b * g * b⁻¹ := by
  have hinv : a⁻¹ * b⁻¹ * a⁻¹ = b⁻¹ := by
    have := congrArg (fun x => x⁻¹) h
    simpa [mul_assoc] using this
  calc a * (b * (a * g * a⁻¹) * b⁻¹) * a⁻¹
      = (a * b * a) * g * (a⁻¹ * b⁻¹ * a⁻¹) := by group
    _ = b * g * b⁻¹ := by rw [h, hinv]

section Orient


variable (K : Type) [Field K]

theorem diagramMap_mul_outerSwap_mul_diagramMap :
    diagramMap TwistTag.D4 K * permModuleMap d4OuterSwap_cartan K * diagramMap TwistTag.D4 K =
      permModuleMap d4OuterSwap_cartan K := by
  have hρ := TwistTag.cartan_perm TwistTag.D4
  have hρs := cartan_mul_perm hρ d4OuterSwap_cartan
  rw [diagramMap_eq_permModuleMap, permModuleMap_mul hρ K d4OuterSwap_cartan hρs,
    permModuleMap_mul hρs K hρ (cartan_mul_perm hρs hρ)]
  exact permModuleMap_congr _ K d4Perm_mul_outerSwap_mul d4OuterSwap_cartan

theorem permModuleMap_outerSwap_mul_self :
    permModuleMap d4OuterSwap_cartan K * permModuleMap d4OuterSwap_cartan K = 1 := by
  rw [permModuleMap_mul d4OuterSwap_cartan K d4OuterSwap_cartan
    (cartan_mul_perm d4OuterSwap_cartan d4OuterSwap_cartan),
    permModuleMap_congr _ K d4OuterSwap_mul_self (fun _ _ => rfl)]
  exact permModuleMap_one K _

theorem twistHom_conj_outerSwap {σ σ' : K →+* K} (hσ : σ.comp σ' = RingHom.id K)
    {g : ModGL TwistTag.D4.tag K} (hg : twistHom TwistTag.D4 K σ' g = g) :
    twistHom TwistTag.D4 K σ (MulAut.conj (permModuleMap d4OuterSwap_cartan K) g) =
      MulAut.conj (permModuleMap d4OuterSwap_cartan K) g := by
  have h1 : Units.map (entrywiseHom σ') g =
      (diagramMap TwistTag.D4 K)⁻¹ * g * diagramMap TwistTag.D4 K := by
    rw [twistHom_apply] at hg
    calc Units.map (entrywiseHom σ') g
        = (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
            Units.map (entrywiseHom σ') g * (diagramMap TwistTag.D4 K)⁻¹) *
            diagramMap TwistTag.D4 K := by group
      _ = (diagramMap TwistTag.D4 K)⁻¹ * g * diagramMap TwistTag.D4 K := by rw [hg]
  have h2 : Units.map (entrywiseHom σ) g =
      diagramMap TwistTag.D4 K * g * (diagramMap TwistTag.D4 K)⁻¹ := by
    have h3 : Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ') g) =
        Units.map (entrywiseHom σ) ((diagramMap TwistTag.D4 K)⁻¹ * g * diagramMap TwistTag.D4 K) :=
      congrArg _ h1
    rw [units_map_entrywiseHom_comp, hσ, map_mul, map_mul, map_inv,
      units_map_entrywiseHom_diagramMap] at h3
    have h4 : Units.map (entrywiseHom (RingHom.id K)) g = g :=
      Units.ext (entrywise_id (g : Module.End K (RootModule TwistTag.D4.tag K)))
    rw [h4] at h3
    calc Units.map (entrywiseHom σ) g
        = diagramMap TwistTag.D4 K * ((diagramMap TwistTag.D4 K)⁻¹ *
            Units.map (entrywiseHom σ) g * diagramMap TwistTag.D4 K) *
            (diagramMap TwistTag.D4 K)⁻¹ := by group
      _ = diagramMap TwistTag.D4 K * g * (diagramMap TwistTag.D4 K)⁻¹ := by rw [← h3]
  rw [twistHom_apply, units_map_entrywiseHom_conj_permModuleMap d4OuterSwap_cartan K, h2,
    MulAut.conj_apply, MulAut.conj_apply]
  exact conj_conj_eq_of_mul_mul_eq _ _ _ (diagramMap_mul_outerSwap_mul_diagramMap K)

theorem conj_outerSwap_mem_twistedFixedGroup {σ σ' : K →+* K} (hσ : σ.comp σ' = RingHom.id K)
    {g : ModGL TwistTag.D4.tag K} (hg : g ∈ twistedFixedGroup TwistTag.D4 K σ') :
    MulAut.conj (permModuleMap d4OuterSwap_cartan K) g ∈ twistedFixedGroup TwistTag.D4 K σ := by
  rw [mem_twistedFixedGroup_iff_twistHom] at hg ⊢
  refine ⟨?_, twistHom_conj_outerSwap K hσ hg.2⟩
  have h := Subgroup.mem_map_of_mem
    (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).toMonoidHom hg.1
  rwa [map_conj_permModuleMap_adjointGroup d4OuterSwap_cartan K] at h

theorem conj_outerSwap_conj_outerSwap (g : ModGL TwistTag.D4.tag K) :
    MulAut.conj (permModuleMap d4OuterSwap_cartan K)
        (MulAut.conj (permModuleMap d4OuterSwap_cartan K) g) = g := by
  rw [MulAut.conj_apply, MulAut.conj_apply]
  calc permModuleMap d4OuterSwap_cartan K * (permModuleMap d4OuterSwap_cartan K * g *
        (permModuleMap d4OuterSwap_cartan K)⁻¹) * (permModuleMap d4OuterSwap_cartan K)⁻¹
      = (permModuleMap d4OuterSwap_cartan K * permModuleMap d4OuterSwap_cartan K) * g *
        (permModuleMap d4OuterSwap_cartan K * permModuleMap d4OuterSwap_cartan K)⁻¹ := by group
    _ = g := by rw [permModuleMap_outerSwap_mul_self]; group

theorem map_conj_outerSwap_twistedFixedGroup {σ σ' : K →+* K} (h1 : σ.comp σ' = RingHom.id K)
    (h2 : σ'.comp σ = RingHom.id K) :
    (twistedFixedGroup TwistTag.D4 K σ').map
        (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).toMonoidHom =
      twistedFixedGroup TwistTag.D4 K σ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_outerSwap_mem_twistedFixedGroup K h1 hg
  · intro g hg
    exact ⟨MulAut.conj (permModuleMap d4OuterSwap_cartan K) g,
      conj_outerSwap_mem_twistedFixedGroup K h2 hg, conj_outerSwap_conj_outerSwap K g⟩

theorem map_conj_outerSwap_graphFixedPosUnipotent {σ σ' : K →+* K}
    (h1 : σ.comp σ' = RingHom.id K) (h2 : σ'.comp σ = RingHom.id K) :
    (graphFixedPosUnipotent TwistTag.D4 K σ').map
        (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).toMonoidHom =
      graphFixedPosUnipotent TwistTag.D4 K σ := by
  rw [graphFixedPosUnipotent, graphFixedPosUnipotent,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).injective,
    map_conj_permModuleMap_posUnipotent d4OuterSwap_cartan K,
    map_conj_outerSwap_twistedFixedGroup K h1 h2]

theorem map_conj_outerSwap_graphFixedNegUnipotent {σ σ' : K →+* K}
    (h1 : σ.comp σ' = RingHom.id K) (h2 : σ'.comp σ = RingHom.id K) :
    (graphFixedNegUnipotent TwistTag.D4 K σ').map
        (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).toMonoidHom =
      graphFixedNegUnipotent TwistTag.D4 K σ := by
  rw [graphFixedNegUnipotent, graphFixedNegUnipotent,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).injective,
    map_conj_permModuleMap_negUnipotent d4OuterSwap_cartan K,
    map_conj_outerSwap_twistedFixedGroup K h1 h2]

theorem map_conj_outerSwap_graphFixedRootGroup {σ σ' : K →+* K}
    (h1 : σ.comp σ' = RingHom.id K) (h2 : σ'.comp σ = RingHom.id K) :
    (graphFixedRootGroup TwistTag.D4 K σ').map
        (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).toMonoidHom =
      graphFixedRootGroup TwistTag.D4 K σ := by
  rw [graphFixedRootGroup, graphFixedRootGroup, Subgroup.map_sup,
    map_conj_outerSwap_graphFixedPosUnipotent K h1 h2,
    map_conj_outerSwap_graphFixedNegUnipotent K h1 h2]

noncomputable def graphFixedRootGroupOrient {σ σ' : K →+* K} (h1 : σ.comp σ' = RingHom.id K)
    (h2 : σ'.comp σ = RingHom.id K) :
    graphFixedRootGroup TwistTag.D4 K σ' ≃* graphFixedRootGroup TwistTag.D4 K σ :=
  (Subgroup.equivMapOfInjective _ (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).toMonoidHom
    (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).injective).trans
    (MulEquiv.subgroupCongr (map_conj_outerSwap_graphFixedRootGroup K h1 h2))

theorem exists_mulEquiv_graphFixedRootGroup_inv_D4 (σ₀ σ₁ : K ≃+* K) (h : ∀ c, σ₀ (σ₁ c) = c) :
    Nonempty (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom ≃*
      graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) :=
  ⟨graphFixedRootGroupOrient K (σ := σ₁.toRingHom) (σ' := σ₀.toRingHom)
    (RingHom.ext fun c => by
      change σ₁ (σ₀ c) = c
      exact σ₀.injective (by rw [h]))
    (RingHom.ext h)⟩

theorem exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4 [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 3) (σ₀ σ₁ : K ≃+* K) (h₀ : ∀ c, σ₀ c = c ^ (q ^ 2))
    (h₁ : ∀ c, σ₁ c = c ^ q) :
    Nonempty (graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom ≃*
      graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
  refine exists_mulEquiv_graphFixedRootGroup_inv_D4 K σ₀ σ₁ fun c => ?_
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = q ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [h₁, h₀, ← pow_mul, show q * q ^ 2 = q ^ 3 by ring, ← hq]
  exact FiniteField.pow_card c

end Orient

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
