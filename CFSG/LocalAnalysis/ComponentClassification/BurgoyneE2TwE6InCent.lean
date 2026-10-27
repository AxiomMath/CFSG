module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Cent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Kernel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign CFSG.ComponentClassification.Burgoyne.E2.TwE7
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem commute_rootSL2_of_commute_orbitGroup
    {τ : Tag} (hτ : τ ≠ .G2) (D : OrthogonalSemilinearFixedRootDatum τ p k) (hq : 3 ≤ D.q)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2) {z : ModGL τ k}
    (hz : ∀ w ∈ D.orbitGroup, z * w = w * z) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ D.simpleRootsJ) (A : SL2 k) :
    z * rootSL2 τ k β A = rootSL2 τ k β A * z := by
  have hO : thetaOrbit D.θ β ∈ D.orbits := ⟨β, hβ, rfl⟩
  obtain ⟨j, hj, hjβ⟩ := D.exists_orbitVec_eq hO (self_mem_thetaOrbit D.θ β)
  have hX : ∀ c, (z : Module.End k (RootModule τ k)) * (D.orbitX (thetaOrbit D.θ β) c :
      Module.End k (RootModule τ k)) = (D.orbitX (thetaOrbit D.θ β) c :
        Module.End k (RootModule τ k)) * z := fun c =>
    congrArg Units.val (hz _ (Subgroup.subset_closure ⟨_, hO, c, Or.inl rfl⟩))
  have hY : ∀ c, (z : Module.End k (RootModule τ k)) * (D.orbitY (thetaOrbit D.θ β) c :
      Module.End k (RootModule τ k)) = (D.orbitY (thetaOrbit D.θ β) c :
        Module.End k (RootModule τ k)) * z := fun c =>
    congrArg Units.val (hz _ (Subgroup.subset_closure ⟨_, hO, c, Or.inr rfl⟩))
  have hu := fun t => commute_uSL_of_commute_orbitX D hτ hq hO (hcard _ hO) hX hj t
  have hv := fun t => commute_vSL_of_commute_orbitY D hτ hq hO (hcard _ hO) hY hj t
  rw [hjβ] at hu hv
  have hle : (⊤ : Subgroup (SL2 k)) ≤
      (Subgroup.centralizer ({z} : Set (ModGL τ k))).comap (rootSL2 τ k β) := by
    rw [← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;>
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    · exact Units.ext (hu t).symm
    · exact Units.ext (hv t).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top A))).symm

theorem mem_simpleRootsJ_withOrbit_classOrbit
    {τ : Tag} (D : OrthogonalSemilinearFixedRootDatum τ p k) {i : KernelComponent D.χ}
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots (componentRoots D.χ i)) :
    β ∈ (D.withOrbit ⟨D.classOrbit i, i, rfl⟩).simpleRootsJ :=
  (D.withOrbit ⟨D.classOrbit i, i, rfl⟩).mem_simpleRootsJ_iff.2
    ⟨i, D.self_mem_classOrbit i, hβ⟩

theorem commute_rootSL2_of_commute_orbitGroups
    {τ : Tag} (hτ : τ ≠ .G2) (D : OrthogonalSemilinearFixedRootDatum τ p k) (hq : 3 ≤ D.q)
    (hcard : ∀ J' : Set.range D.classOrbit,
      ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2) {z : ModGL τ k}
    (hz : ∀ J' : Set.range D.classOrbit, ∀ w ∈ (D.withOrbit J').orbitGroup, z * w = w * z)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleUnion D.χ) (A : SL2 k) :
    z * rootSL2 τ k β A = rootSL2 τ k β A * z := by
  obtain ⟨i, hi⟩ : ∃ i : KernelComponent D.χ, β ∈ simpleRoots (componentRoots D.χ i) := by
    simpa [simpleUnion] using hβ
  exact commute_rootSL2_of_commute_orbitGroup hτ (D.withOrbit ⟨D.classOrbit i, i, rfl⟩) hq
    (hcard _) (hz _) (mem_simpleRootsJ_withOrbit_classOrbit D hi) A

@[expose] def e6TwGamma2 : List ((Fin (Tag.rank .E6) → ℤ) × ℤ) :=
  [(![1, 2, 2, 3, 2, 1], 11), (![1, 0, 0, 0, 0, 0], 5), (![0, 0, 1, 0, 0, 0], 8),
    (![0, 0, 0, 1, 0, 0], 9), (![0, 0, 0, 0, 1, 0], 8), (![0, 0, 0, 0, 0, 1], 5)]

theorem e6TwGamma2_reg :
    ∀ α ∈ rootFinset .E6,
      (∑ j, regCoweight e6TwGamma2 j * α j) ≠ 0 ∧
        (∑ j, regCoweight e6TwGamma2 j * α j).natAbs < 23 := by
  decide +kernel

theorem e6TwGamma2_mem :
    ∀ y ∈ e6TwGamma2, y.1 ∈ Set.range e6A5Root ∪ {hiE6} := by
  intro y hy
  simp only [e6TwGamma2, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨0, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inl ⟨1, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inl ⟨2, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inl ⟨3, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inl ⟨4, by funext i; fin_cases i <;> rfl⟩

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
theorem rootChar_E6
    (b : Fin (Tag.rank .E6) → kˣ) (v : Fin (Tag.rank .E6) → ℤ) :
    rootChar b v = b (e6Node 0) ^ v (e6Node 0) * b (e6Node 1) ^ v (e6Node 1) *
      b (e6Node 2) ^ v (e6Node 2) * b (e6Node 3) ^ v (e6Node 3) * b (e6Node 4) ^ v (e6Node 4) *
        b (e6Node 5) ^ v (e6Node 5) := by
  show ∏ i : Fin 6, b i ^ v i = _
  rw [Fin.prod_univ_six]
  rfl

theorem orbitCard_of_two
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ)) :
    ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2 := by
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties TwistTag.E6.perm 2 D.χ (ToralSign.wordElt .E6 []) := by
    rw [hχ]
    exact h6.theta ⟨2, 36, 1, e6OmegaWords2⟩ (by simp [e6SignDiagramReps]) []
      (by simp [e6OmegaWords2])
  exact fun O hO => orbitCard_eq_of_thetaProperties D hθp hθ hO

theorem sq_eq_one_of_commute_orbitGroups_two
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hq : 3 ≤ D.q)
    (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    {z : ModGL .E6 k} (hzG : z ∈ adjointGroup .E6 k)
    (hz : ∀ J' : Set.range D.classOrbit, ∀ w ∈ (D.withOrbit J').orbitGroup, z * w = w * z) :
    z ^ 2 = 1 := by
  have hcard : ∀ J' : Set.range D.classOrbit,
      ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 :=
    fun J' => orbitCard_of_two (D.withOrbit J') hχ hθ
  have hΔ : simpleUnion D.χ = Set.range e6A5Root ∪ {hiE6} := by
    rw [hχ, simpleUnion_e6_two]
  have hmem : ∀ β ∈ Set.range e6A5Root ∪ {hiE6}, ∀ A : SL2 k,
      z * rootSL2 .E6 k β A = rootSL2 .E6 k β A * z := fun β hβ A =>
    commute_rootSL2_of_commute_orbitGroups (by decide) D hq hcard hz (hΔ ▸ hβ) A
  have hroot : ∀ β ∈ Set.range e6A5Root ∪ {hiE6}, IsRoot .E6 β := by
    rintro β (⟨i, rfl⟩ | hβ)
    · exact isRoot_single _ _
    · rw [Set.mem_singleton_iff] at hβ
      rw [hβ]
      exact isRoot_hiE6
  have hT := mem_torusGroup_of_commute_rootTorus p (Or.inl rfl) hzG e6TwGamma2
    (fun y hy => hroot _ (e6TwGamma2_mem y hy))
    (fun y hy s => hmem y.1 (e6TwGamma2_mem y hy) (HSL s)) 23
    (fun α hα => e6TwGamma2_reg α (mem_rootFinset.2 hα))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hχb : ∀ β ∈ Set.range e6A5Root ∪ {hiE6}, rootChar b β = 1 := fun β hβ =>
    rootChar_eq_one_of_commute (hroot β hβ) (hmem β hβ (uSL 1))
  have hb : ∀ j : Fin 6, j ≠ 1 → b (e6Node j) = 1 := by
    intro j hj
    have hj' : ∃ i : Fin 5, e6A5Root i = Pi.single (e6Node j) 1 := by
      fin_cases j
      · exact ⟨0, by funext i; fin_cases i <;> rfl⟩
      · exact absurd rfl hj
      · exact ⟨1, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
    obtain ⟨i, hi⟩ := hj'
    have h := hχb _ (Or.inl ⟨i, hi⟩)
    rwa [rootChar_single'] at h
  have hb1 : b (e6Node 1) ^ 2 = 1 := by
    have h := hχb hiE6 (Or.inr rfl)
    have h' := (rootChar_E6 b hiE6).symm.trans h
    rw [hb 0 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
      hb 5 (by decide)] at h'
    have e : hiE6 (e6Node 1) = 2 := rfl
    rw [e] at h'
    simpa using h'
  rw [sq, ← rootDiagUnit_mul]
  convert rootDiagUnit_one (τ := .E6) (K := k) using 2
  funext j
  obtain ⟨j', rfl⟩ : ∃ j' : Fin 6, e6Node j' = j := ⟨j, rfl⟩
  by_cases hj : j' = 1
  · subst hj
    rw [Pi.mul_apply, ← sq, hb1]
    rfl
  · rw [Pi.mul_apply, hb j' hj, one_mul]
    rfl

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In
