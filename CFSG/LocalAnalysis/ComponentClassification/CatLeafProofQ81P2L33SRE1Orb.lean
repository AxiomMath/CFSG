module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Comp
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E1

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

section Classes

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem two_le_card_simpleRoots_of_iform (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β γ : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots χ) (hγ : γ ∈ kernelRoots χ)
    (h : iform β γ = 1) :
    2 ≤ (simpleRoots (componentRoots χ (⟦⟨β, hβ⟩⟧ : KernelComponent χ))).card := by
  set i : KernelComponent χ := ⟦⟨β, hβ⟩⟧ with hi
  have hβi : β ∈ componentRoots χ i := ⟨hβ, rfl⟩
  have hγi : γ ∈ componentRoots χ i := by
    refine ⟨hγ, mk_eq_of_iform_ne_zero (α := ⟨γ, hγ⟩) (β := ⟨β, hβ⟩) ?_⟩
    change iform γ β ≠ 0
    rw [iform_comm, h]
    exact one_ne_zero
  by_contra hlt
  obtain ⟨w₀, -, β₀, hβ₀, -⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i) hβi
  have hcard : (simpleRoots (componentRoots χ i)).card = 1 := by
    have hpos : 0 < (simpleRoots (componentRoots χ i)).card := Finset.card_pos.2 ⟨β₀, hβ₀⟩
    omega
  obtain ⟨β₁, hβ₁⟩ := Finset.card_eq_one.1 hcard
  have hsimple : ∀ δ ∈ simpleRoots (componentRoots χ i), δ = β₁ := fun δ hδ => by
    rw [hβ₁] at hδ
    exact Finset.mem_singleton.1 hδ
  have hr : IsRoot τ β₁ := simpleRoots_isRoot (hβ₁ ▸ Finset.mem_singleton_self β₁)
  have hW : ∀ w ∈ componentWeylGroup (componentRoots χ i), w • β₁ = β₁ ∨ w • β₁ = -β₁ := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β', hβ', rfl⟩ := hx
      obtain rfl := hsimple β' hβ'
      exact Or.inr (rootReflection_smul_self hr)
    | one => exact Or.inl (one_smul _ _)
    | mul x y _ _ hx hy =>
      rw [mul_smul]
      rcases hy with hy | hy
      · rw [hy]
        exact hx
      · rw [hy, smul_neg]
        rcases hx with hx | hx
        · exact Or.inr (by rw [hx])
        · exact Or.inl (by rw [hx, neg_neg])
    | inv x _ hx =>
      rcases hx with hx | hx
      · left
        calc x⁻¹ • β₁ = x⁻¹ • (x • β₁) := by rw [hx]
          _ = β₁ := inv_smul_smul x β₁
      · right
        have : x⁻¹ • (x • β₁) = x⁻¹ • -β₁ := by rw [hx]
        rw [inv_smul_smul, smul_neg] at this
        exact neg_eq_iff_eq_neg.1 this.symm
  have hpm : ∀ δ ∈ componentRoots χ i, δ = β₁ ∨ δ = -β₁ := by
    intro δ hδ
    obtain ⟨w, hw, β', hβ', rfl⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i) hδ
    obtain rfl := hsimple β' hβ'
    exact hW w hw
  have h2 : iform β₁ β₁ = 2 := by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hr
  have hneg : ∀ x y : Fin τ.rank → ℤ, iform x (-y) = -iform x y := fun x y => by
    rw [← neg_one_smul ℤ y, iform_smul_right]
    ring
  have hneg' : ∀ x y : Fin τ.rank → ℤ, iform (-x) y = -iform x y := fun x y => by
    rw [← neg_one_smul ℤ x, iform_smul_left]
    ring
  rcases hpm β hβi with rfl | rfl <;> rcases hpm γ hγi with rfl | rfl <;>
    simp only [hneg, hneg', h2, neg_neg] at h <;> omega

end Classes

section Datum


variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem three_le_q : 3 ≤ D.q := by
  have h2 := (Fact.out : p₀.Prime).two_le
  have hodd := D.odd
  have hpe : p₀ ≤ p₀ ^ D.e := Nat.le_self_pow (by have := D.one_le_e; omega) p₀
  show 3 ≤ p₀ ^ D.e
  omega

theorem isQuasisimple_orbitGroup_of_two_le (h : 2 ≤ D.simpleRootsJ.ncard) :
    CFSG.IsQuasisimple D.orbitGroup := by
  obtain ⟨-, -, h2, h1, -⟩ := orthogonal_semilinear_fixed_root_quasisimplicity D
  by_cases hc : 2 ≤ D.orbits.ncard
  · exact h2 hc
  have hSf : D.simpleRootsJ.Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨β, hβ⟩ := Set.nonempty_of_ncard_ne_zero (by omega : D.simpleRootsJ.ncard ≠ 0)
  have hfin : D.orbits.Finite := by
    have : D.orbits = (thetaOrbit D.θ) '' D.simpleRootsJ := by
      ext O
      exact ⟨fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩, fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩⟩
    rw [this]
    exact hSf.image _
  have hpos : 0 < D.orbits.ncard := (Set.ncard_pos hfin).2 ⟨_, D.thetaOrbit_mem_orbits hβ⟩
  obtain ⟨O, hO⟩ := Set.ncard_eq_one.1 (by omega : D.orbits.ncard = 1)
  have hOm : O ∈ D.orbits := by
    rw [hO]
    exact Set.mem_singleton O
  refine h1 O hO ?_
  have hsub : D.simpleRootsJ ⊆ O := by
    intro γ hγ
    have h' := D.thetaOrbit_mem_orbits hγ
    rw [hO, Set.mem_singleton_iff] at h'
    rw [← h']
    exact self_mem_thetaOrbit D.θ γ
  have hOpos : 0 < orbitCard O := D.orbitCard_pos hOm
  have hOf : O.Finite := Set.finite_of_ncard_pos hOpos
  have hOc : 2 ≤ orbitCard O := h.trans (Set.ncard_le_ncard hsub hOf)
  rw [D.card_orbitField hOm]
  have hq := three_le_q D
  calc 3 < 3 ^ 2 := by norm_num
    _ ≤ D.q ^ 2 := Nat.pow_le_pow_left hq 2
    _ ≤ D.q ^ orbitCard O := Nat.pow_le_pow_right (by omega) hOc

abbrev classJ {β : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots D.χ) : Set.range D.classOrbit :=
  ⟨D.classOrbit ⟦⟨β, hβ⟩⟧, _, rfl⟩

theorem two_le_ncard_simpleRootsJ {β γ : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots D.χ)
    (hγ : γ ∈ kernelRoots D.χ) (h : iform β γ = 1) :
    2 ≤ (D.withOrbit (classJ D hβ)).simpleRootsJ.ncard := by
  have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases D.tag_mem with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hcard := two_le_card_simpleRoots_of_iform hτ hβ hγ h
  set i : KernelComponent D.χ := ⟦⟨β, hβ⟩⟧ with hi
  have hsub : ((simpleRoots (componentRoots D.χ i) : Finset _) : Set (Fin τ.rank → ℤ)) ⊆
      (D.withOrbit (classJ D hβ)).simpleRootsJ := by
    intro δ hδ
    refine ⟨⟨i, Set.mem_univ _, hδ⟩, ?_⟩
    exact mem_unionRoots_iff.2 ⟨i, D.self_mem_classOrbit i, simpleRoots_subset hδ⟩
  have hfin : (D.withOrbit (classJ D hβ)).simpleRootsJ.Finite :=
    (D.withOrbit (classJ D hβ)).finite_roots.subset fun _ h => h.2
  calc 2 ≤ (simpleRoots (componentRoots D.χ i)).card := hcard
    _ = ((simpleRoots (componentRoots D.χ i) : Finset _) : Set (Fin τ.rank → ℤ)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

theorem orbitGroupC_isComponent (J' : Set.range D.classOrbit)
    (h : 2 ≤ (D.withOrbit J').simpleRootsJ.ncard) :
    (D.withOrbit J').orbitGroupC ≤ D.totalFixedGroup ∧
      ((D.withOrbit J').orbitGroupC.subgroupOf D.totalFixedGroup).IsSubnormal ∧
      GorensteinWalter.IsQuasisimple (D.withOrbit J').orbitGroupC := by
  have h1 : (D.withOrbit J').orbitGroupC ≤ (D.withOrbit J').fixedGroup :=
    (D.withOrbit J').orbitGroupC_le_fixedGroup
  have h2 : (D.withOrbit J').fixedGroup ≤ D.orbitFixedJoin :=
    D.fixedGroup_withOrbit_le_orbitFixedJoin J'
  have h3 : D.orbitFixedJoin ≤ D.kernelFixedGroup := D.orbitFixedJoin_le_kernelFixedGroup
  have h4 : D.kernelFixedGroup ≤ D.totalFixedGroup := D.kernelFixedGroup_le_totalFixedGroup
  have hsn : CFSG.Open.IsSubnormal (D.withOrbit J').orbitGroupC D.totalFixedGroup := by
    refine CFSG.Open.IsSubnormal.step h1 (D.withOrbit J').orbitGroupC_normal
      (CFSG.Open.IsSubnormal.step h2 ?_
        (CFSG.Open.IsSubnormal.step h3 ?_ (CFSG.Open.IsSubnormal.step h4 ?_
          (CFSG.Open.IsSubnormal.refl _))))
    · exact ⟨fun n hn g => mem_subgroupOf.2
        (D.conj_mem_fixedGroup_withOrbit (h3 g.2) (mem_subgroupOf.1 hn))⟩
    · exact ⟨fun n hn g => mem_subgroupOf.2
        (D.conj_mem_orbitFixedJoin g.2 (mem_subgroupOf.1 hn))⟩
    · exact ⟨fun n hn g => mem_subgroupOf.2
        (D.conj_mem_kernelFixedGroup g.2 (mem_subgroupOf.1 hn))⟩
  refine ⟨h1.trans (h2.trans (h3.trans h4)), isSubnormal_subgroupOf_of_open hsn, ?_⟩
  have hq := isQuasisimple_orbitGroup_of_two_le (D.withOrbit J') h
  exact gw_isQuasisimple_of_mulEquiv
    (subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup).symm
    (gw_isQuasisimple_of_isQuasisimple hq)

end Datum

end CFSG.ComponentClassification.HarrisLit.L33.SR.E1
