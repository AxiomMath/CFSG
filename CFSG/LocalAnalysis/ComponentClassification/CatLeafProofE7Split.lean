module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Classes
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

theorem range_le_of_uSL_vSL {F : Type} [Field F] {G : Type*} [Group G] (φ : SL2 F →* G)
    {H : Subgroup G} (hu : ∀ c, φ (uSL c) ∈ H) (hv : ∀ c, φ (vSL c) ∈ H) : φ.range ≤ H := by
  rintro _ ⟨A, rfl⟩
  have hA : A ∈ Subgroup.closure (Set.range (LocalAnalysis.ComponentInitial.sl2Upper F) ∪
      Set.range (LocalAnalysis.ComponentInitial.sl2Lower F)) := by
    rw [LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  refine (Subgroup.closure_le (H.comap φ)).2 ?_ hA
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hu c
  · exact hv c

section Split

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem pow_apply_toReal_of_fix (θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ))
    {β : Fin τ.rank → ℤ} (hθ : θ (toReal β) = toReal β) (m : ℕ) :
    (θ ^ m) (toReal β) = toReal β := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hθ, ih]

theorem thetaOrbit_eq_singleton (θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ))
    {β : Fin τ.rank → ℤ} (hθ : θ (toReal β) = toReal β) : thetaOrbit θ β = {β} := by
  ext γ
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [pow_apply_toReal_of_fix θ hθ] at hm
    exact (toReal_injective hm).symm
  · rintro rfl
    exact ⟨0, by simp⟩

theorem orbitGroup_eq_map_pairSpan
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ : ∀ β ∈ D.simpleRootsJ, D.θ (toReal β) = toReal β) :
    D.orbitGroup = (pairSpan τ (frobeniusFixedField k p D.e) D.simpleRootsJ).map
      (baseChangeGL (frobeniusFixedField k p D.e).subtype) := by
  have hO : ∀ β ∈ D.simpleRootsJ, ({β} : Set (Fin τ.rank → ℤ)) ∈ D.orbits ∧
      orbitCard ({β} : Set (Fin τ.rank → ℤ)) = 1 ∧ orbitRoot ({β} : Set (Fin τ.rank → ℤ)) = β :=
    fun β hβ => ⟨⟨β, hβ, (thetaOrbit_eq_singleton D.θ (hθ β hβ)).symm⟩, Set.ncard_singleton β,
      lexLeast_mem (Set.finite_singleton β) (Set.singleton_nonempty β)⟩
  have hOm : ∀ O ∈ D.orbits, ∃ β ∈ D.simpleRootsJ, O = {β} := by
    rintro O ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, thetaOrbit_eq_singleton D.θ (hθ β hβ)⟩
  have hfield : ∀ (O : Set (Fin τ.rank → ℤ)), orbitCard O = 1 → ∀ c : k,
      c ∈ D.orbitField O ↔ c ∈ frobeniusFixedField k p D.e := by
    intro O h1 c
    change c ∈ frobeniusFixedField k p (D.e * orbitCard O) ↔ _
    rw [h1, mul_one]
  have hroot : ∀ β ∈ D.simpleRootsJ, IsRoot τ β := fun β hβ =>
    (D.mem_kernelRoots_of_mem_simpleRootsJ hβ).1
  have hmem : ∀ β ∈ D.simpleRootsJ, ∀ A,
      rootSL2 τ (frobeniusFixedField k p D.e) β A ∈
        pairSpan τ (frobeniusFixedField k p D.e) D.simpleRootsJ := fun β hβ A => by
    refine Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem hβ ?_)
    rw [← range_rootSL2_of_isRoot (hroot β hβ)]
    exact ⟨A, rfl⟩
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨O, hO', c, rfl | rfl⟩
    · obtain ⟨β, hβ, rfl⟩ := hOm O hO'
      obtain ⟨-, h1, hr⟩ := hO β hβ
      rw [D.orbitX_of_orbitCard_eq_one h1, hr]
      refine ⟨_, hmem β hβ (uSL ⟨c, (hfield _ h1 c).1 c.2⟩), ?_⟩
      rw [baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_uSL]
      rfl
    · obtain ⟨β, hβ, rfl⟩ := hOm O hO'
      obtain ⟨-, h1, hr⟩ := hO β hβ
      rw [D.orbitY_of_orbitCard_eq_one h1, hr]
      refine ⟨_, hmem β hβ (vSL ⟨c, (hfield _ h1 c).1 c.2⟩), ?_⟩
      rw [baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_vSL]
      rfl
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun β hβ => ?_
    rw [← range_rootSL2_of_isRoot (hroot β hβ)]
    obtain ⟨hOβ, h1, hr⟩ := hO β hβ
    refine range_le_of_uSL_vSL _ (fun c => ?_) (fun c => ?_)
    · have hc : (c : k) ∈ D.orbitField {β} := (hfield _ h1 c).2 c.2
      have hX := D.orbitX_of_orbitCard_eq_one h1 ⟨c, hc⟩
      rw [hr] at hX
      rw [Subgroup.mem_comap, baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_uSL]
      exact hX ▸ Subgroup.subset_closure ⟨{β}, hOβ, ⟨c, hc⟩, Or.inl rfl⟩
    · have hc : (c : k) ∈ D.orbitField {β} := (hfield _ h1 c).2 c.2
      have hY := D.orbitY_of_orbitCard_eq_one h1 ⟨c, hc⟩
      rw [hr] at hY
      rw [Subgroup.mem_comap, baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_vSL]
      exact hY ▸ Subgroup.subset_closure ⟨{β}, hOβ, ⟨c, hc⟩, Or.inr rfl⟩

theorem classOrbit_eq_singleton
    (D : OrthogonalSemilinearFixedRootDatum τ p k) (hθ : ∀ γ, D.θ (toReal γ) = toReal γ)
    (i : KernelComponent D.χ) : D.classOrbit i = {i} := by
  ext i'
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, α, ⟨hα, hαi⟩, β, ⟨hβ, hβi'⟩, h⟩
    rw [pow_apply_toReal_of_fix D.θ (hθ α)] at h
    obtain rfl := toReal_injective h
    exact hβi'.symm.trans hαi
  · intro h
    rw [h]
    exact D.self_mem_classOrbit i

end Split

theorem e7_pairSpan_oddLieCentralQuotient
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {S : Set (Fin (Tag.rank .E7) → ℤ)}
    (hS : S = ∅ ∨ S = Set.range e7SimpleRoot ∨ S = Set.range e7D6Root ∨ S = {e7Theta} ∨
      S = Set.range e7A7Root ∨ S = Set.range e7E6Root)
    (hq : IsQuasisimple (pairSpan .E7 K S)) : OddLieCentralQuotient p (pairSpan .E7 K S) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    rw [Subgroup.nontrivial_iff_ne_bot] at this
    exact this (by rw [pairSpan]; exact iSup_emptyset)
  · exact oddLieCentralQuotient_pairSpan_E7 hp hp2 hK
  · exact oddLieCentralQuotient_pairSpan_D6 hp hp2 hK
  · exact oddLieCentralQuotient_pairSpan_A1 hp hp2 hK hq
  · exact oddLieCentralQuotient_pairSpan_A7 hp hp2 hK
  · exact oddLieCentralQuotient_pairSpan_E6 hp hp2 hK

theorem e7_simple_inter_cases
    {χ : Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ} {m : ℕ}
    (hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) (hχ : χ = signMaskChar .E7 m)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7SimpleRoot ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7D6Root ∨
      simpleUnion χ ∩ componentRoots χ i = {e7Theta} ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7A7Root ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7E6Root := by
  rcases hm with rfl | rfl | rfl | rfl
  · rcases e7_simple_inter_zero hχ i with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases e7_simple_inter_one hχ i with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases e7_simple_inter_two hχ i with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases e7_simple_inter_three hχ i with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem e7_split_orbitGroup_oddLieCentralQuotient
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) {m : ℕ}
    (hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) (hχ : D.χ = signMaskChar .E7 m)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal γ) (J' : Set.range D.classOrbit)
    (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
  obtain ⟨i₀, hi₀⟩ := J'.2
  have hJ : ∀ i, i ∈ (J' : Set (KernelComponent D.χ)) ↔ i = i₀ := fun i => by
    rw [← hi₀, classOrbit_eq_singleton D hθ, Set.mem_singleton_iff]
  have hS : (D.withOrbit J').simpleRootsJ = simpleUnion D.χ ∩ componentRoots D.χ i₀ := by
    ext β
    constructor
    · rintro ⟨⟨i, -, hβi⟩, h, hJβ⟩
      exact ⟨Set.mem_iUnion.2 ⟨i, hβi⟩, h, (hJ _).1 hJβ⟩
    · rintro ⟨hβ, h, hβi⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hβ
      exact ⟨⟨i, Set.mem_univ _, hi⟩, h, (hJ _).2 hβi⟩
  have horb := orbitGroup_eq_map_pairSpan (D.withOrbit J') fun β _ => hθ β
  rw [hS] at horb
  have hK : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : Finite (frobeniusFixedField k p D.e) :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let e : (D.withOrbit J').orbitGroup ≃*
      pairSpan .E7 (frobeniusFixedField k p D.e) (simpleUnion D.χ ∩ componentRoots D.χ i₀) :=
    (MulEquiv.subgroupCongr horb).trans
      ((Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).symm)
  exact oddLieCentralQuotient_of_mulEquiv e
    (e7_pairSpan_oddLieCentralQuotient (Fact.out : p.Prime) D.odd hK
      (e7_simple_inter_cases hm hχ i₀) (LocalCores.isQuasisimple_of_mulEquiv e hq))

end CFSG.ComponentClassification.CatLeafProof
