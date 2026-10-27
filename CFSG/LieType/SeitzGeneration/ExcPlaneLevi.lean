module

public import CFSG.LieType.SeitzGeneration.ExcPlanePair
public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.HighestRoot Matrix CFSG.Open
  CFSG.PreuniquenessRankFour.Helpers


variable {τ : Tag} {K : Type} [Field K]

@[expose] def rootElementsOf (i : Fin τ.rank) : Set (adjointGroup τ K) :=
  {x | ∃ c : K, x = (rootOperatorFamily τ).eltElement (simpleRoot τ i) c ∨
    x = (rootOperatorFamily τ).eltElement (-simpleRoot τ i) c}

theorem sl2_hom_mem_closure {i : Fin τ.rank} (φ : SpecialLinearGroup (Fin 2) K →* adjointGroup τ K)
    (hu : ∀ c, φ (sl2Upper c) = (rootOperatorFamily τ).eltElement (simpleRoot τ i) c)
    (hl : ∀ c, φ (sl2Lower c) = (rootOperatorFamily τ).eltElement (-simpleRoot τ i) c)
    (g : SpecialLinearGroup (Fin 2) K) :
    φ g ∈ Subgroup.closure (rootElementsOf (K := K) i) := by
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod g
  have hU : ∀ c, φ (sl2Upper c) ∈ Subgroup.closure (rootElementsOf (K := K) i) := fun c =>
    Subgroup.subset_closure ⟨c, Or.inl (hu c)⟩
  have hL : ∀ c, φ (sl2Lower c) ∈ Subgroup.closure (rootElementsOf (K := K) i) := fun c =>
    Subgroup.subset_closure ⟨c, Or.inr (hl c)⟩
  rw [map_mul, map_mul, map_mul]
  exact mul_mem (mul_mem (mul_mem (hL e) (hU a)) (hL b)) (hU c)

theorem coe_eltElement_mem_rootSubgroup (β : Root τ) (c : K) :
    (((rootOperatorFamily τ).eltElement β c : adjointGroup τ K) : ModGL τ K) ∈
      rootSubgroup τ K β.1 := by
  have h := (rootOperatorFamily τ).eltElement_mem_rootSubgroup (K := K) β c
  rw [← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K β] at h
  exact Subgroup.mem_subgroupOf.1 h

theorem closure_rootElementsOf_le_levi {J : Set (Fin τ.rank)} {m : Fin τ.rank} (hm : m ∈ J) :
    Subgroup.closure (rootElementsOf (K := K) m) ≤
      (parabolicLevi τ K J).comap (adjointGroup τ K).subtype := by
  rw [Subgroup.closure_le]
  rintro _ ⟨c, rfl | rfl⟩
  · show (((rootOperatorFamily τ).eltElement (simpleRoot τ m) c : adjointGroup τ K) :
      ModGL τ K) ∈ parabolicLevi τ K J
    rw [(rootOperatorFamily τ).coe_eltElement, (rootOperatorFamily τ).eltUnit_simple]
    exact xUnit_mem_parabolicLevi hm c
  · show (((rootOperatorFamily τ).eltElement (-simpleRoot τ m) c : adjointGroup τ K) :
      ModGL τ K) ∈ parabolicLevi τ K J
    rw [(rootOperatorFamily τ).coe_eltElement, (rootOperatorFamily τ).eltUnit_neg_simple]
    exact yUnit_mem_parabolicLevi hm c

section Full


theorem commute_rootElementsOf (hτ : NoG2 τ) {i j : Fin τ.rank} (hij : i ≠ j)
    (hc : τ.cartan i j = 0) (hlong : ∀ m, τ.symmetrizer m m ≤ τ.symmetrizer i i)
    {x y : adjointGroup τ K} (hx : x ∈ rootElementsOf (K := K) i)
    (hy : y ∈ rootElementsOf (K := K) j) : Commute x y := by
  have hγ : IsRoot τ (Pi.single i 1) := isRoot_single τ i
  have hlong' : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform (Pi.single i 1) (Pi.single i 1) := by
    intro ε hε
    obtain ⟨m, hm⟩ := iform_self_of_isRoot hε
    rw [hm, iform_single_single]
    linarith [hlong m]
  have h0 : iform (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single i 1) = 0 := by
    rw [iform_single_right]
    have : ∑ m, τ.cartan i m * (Pi.single j 1 : Fin τ.rank → ℤ) m = 0 := by
      rw [Finset.sum_eq_single j (fun m _ hm => by simp [hm]) (by simp)]
      simp [hc]
    rw [this, mul_zero]
  have h0' : iform (-(Pi.single j 1) : Fin τ.rank → ℤ) (Pi.single i 1) = 0 := by
    rw [iform_comm, iform_neg_right, iform_comm, h0, neg_zero]
  have hne1 : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ Pi.single i 1 :=
    single_ne_single_of_ne (Ne.symm hij)
  have hne2 : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := single_ne_neg_single_of j i
  have hne3 : (-(Pi.single j 1) : Fin τ.rank → ℤ) ≠ Pi.single i 1 := fun h =>
    single_ne_neg_single_of i j h.symm
  have hne4 : (-(Pi.single j 1) : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := fun h =>
    hne1 (neg_injective h)
  obtain ⟨c, hxc⟩ := hx
  obtain ⟨d, hyd⟩ := hy
  suffices h : Commute (y : ModGL τ K) (x : ModGL τ K) from
    Subtype.ext (h.symm.eq)
  rcases hyd with rfl | rfl
  · have hmem := coe_eltElement_mem_rootSubgroup (K := K) (simpleRoot τ j) d
    obtain ⟨h1, h2⟩ := commute_pair_of_iform_eq_zero (K := K) hτ (isRoot_single τ j) hγ hlong'
      h0 hne1 hne2 _ hmem
    rcases hxc with rfl | rfl
    · exact h1 _ (coe_eltElement_mem_rootSubgroup (K := K) (simpleRoot τ i) c)
    · exact h2 _ (coe_eltElement_mem_rootSubgroup (K := K) (-simpleRoot τ i) c)
  · have hmem := coe_eltElement_mem_rootSubgroup (K := K) (-simpleRoot τ j) d
    obtain ⟨h1, h2⟩ := commute_pair_of_iform_eq_zero (K := K) hτ (IsRoot.neg (isRoot_single τ j))
      hγ hlong' h0' hne3 hne4 _ hmem
    rcases hxc with rfl | rfl
    · exact h1 _ (coe_eltElement_mem_rootSubgroup (K := K) (simpleRoot τ i) c)
    · exact h2 _ (coe_eltElement_mem_rootSubgroup (K := K) (-simpleRoot τ i) c)

theorem exists_commuting_sl2_pair (hτ : NoG2 τ) {i j k l : Fin τ.rank} (hij : i ≠ j)
    (hc : τ.cartan i j = 0) (hlong : ∀ m, τ.symmetrizer m m ≤ τ.symmetrizer i i)
    (hk : τ.cartan i k = -1) (hl : τ.cartan j l = -1) :
    ∃ φ ψ : SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
      Function.Injective ψ ∧ (∀ g h, Commute (φ g) (ψ h)) ∧
        (∀ g, (φ g : ModGL τ K) ∈ parabolicLevi τ K {i, j}) ∧
          ∀ h, (ψ h : ModGL τ K) ∈ parabolicLevi τ K {i, j} := by
  obtain ⟨φ, hφ, hφu, hφl⟩ := exists_sl2_hom (K := K) (rootOperatorFamily τ) hk
  obtain ⟨ψ, hψ, hψu, hψl⟩ := exists_sl2_hom (K := K) (rootOperatorFamily τ) hl
  have hφc := sl2_hom_mem_closure φ hφu hφl
  have hψc := sl2_hom_mem_closure ψ hψu hψl
  refine ⟨φ, ψ, hφ, hψ, fun g h => ?_, fun g => ?_, fun h => ?_⟩
  · have step2 : ∀ s ∈ rootElementsOf (K := K) j, Commute (φ g) s := by
      intro s hs
      have hle : Subgroup.closure (rootElementsOf (K := K) i) ≤ Subgroup.centralizer {s} := by
        rw [Subgroup.closure_le]
        intro x hx
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (commute_rootElementsOf hτ hij hc hlong hx hs).eq
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hφc g))
    have hle : Subgroup.closure (rootElementsOf (K := K) j) ≤ Subgroup.centralizer {φ g} := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (step2 s hs).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (hψc h))).symm
  · exact closure_rootElementsOf_le_levi (by simp) (hφc g)
  · exact closure_rootElementsOf_le_levi (by simp) (hψc h)

theorem exists_levi_plane [Finite K] (hτ : NoG2 τ) {i j k l : Fin τ.rank} (hij : i ≠ j)
    (hc : τ.cartan i j = 0) (hlong : ∀ m, τ.symmetrizer m m ≤ τ.symmetrizer i i)
    (hk : τ.cartan i k = -1) (hl : τ.cartan j l = -1) (hJ : ({i, j} : Set (Fin τ.rank)) ≠ Set.univ)
    {r f : ℕ} (hKr : Nat.card K = r ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card K * (Nat.card K ^ 2 - 1)) :
    ∃ A R : Subgroup (ModGL τ K), A ≤ adjointGroup τ K ∧ R ≤ adjointGroup τ K ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ R ≠ ⊥ ∧ IsPGroup r R ∧
        A ≤ Subgroup.normalizer (R : Set (ModGL τ K)) := by
  obtain ⟨φ, ψ, hφ, hψ, hcomm, hφL, hψL⟩ := exists_commuting_sl2_pair (K := K) hτ hij hc hlong hk hl
  obtain ⟨A₀, hA₀le, hA₀el, hA₀card⟩ := exists_plane_of_commuting_sl2 φ ψ hφ hψ hcomm hp hp2 hdvd
  have hAL : A₀.map (adjointGroup τ K).subtype ≤ parabolicLevi τ K {i, j} := by
    rintro _ ⟨a, ha, rfl⟩
    have hsup : φ.range ⊔ ψ.range ≤ (parabolicLevi τ K {i, j}).comap (adjointGroup τ K).subtype :=
      sup_le (by rintro _ ⟨g, rfl⟩; exact hφL g) (by rintro _ ⟨g, rfl⟩; exact hψL g)
    exact hsup (hA₀le ha)
  refine ⟨A₀.map (adjointGroup τ K).subtype, parabolicRadical τ K {i, j},
    Subgroup.map_subtype_le A₀, rootSpan_le_adjointGroup K _,
    elementary_abelian_map p hA₀el _, ?_, parabolicRadical_ne_bot hJ, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective, hA₀card]
  · refine IsPGroup.of_card (n := f * (parabolicRadicalRoots τ {i, j}).ncard) ?_
    rw [card_parabolicRadical, hKr, ← pow_mul]
  · exact hAL.trans ((parabolicLevi_le_parabolicSubgroup _).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical _))

end Full

end CFSG.LieType.SeitzGeneration
