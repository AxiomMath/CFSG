module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerOrbit
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwistShape
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.ModelFacts (orbitMap_of_orbitCard_eq_one)
open scoped MatrixGroups

section Datum

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_mask2_datum (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
      (s : Fin TwistTag.E6.tag.rank → kˣ),
      D.χ = signMaskChar TwistTag.E6.tag 2 ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ)) ∧
      (fixedPointsIn (torusGroup TwistTag.E6.tag k ⊔
          rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)))
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))).map
          (MulAut.conj (rootDiagUnit TwistTag.E6.tag s)).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
  classical
  set t := TwistTag.E6 with ht
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  have hr : (⟨2, 36, 1, e6OmegaWords2⟩ : SignRep .E6) ∈ e6SignDiagramReps := by
    simp [e6SignDiagramReps]
  have hr0 : ([] : List (Fin Tag.E6.rank)) ∈
      (⟨2, 36, 1, e6OmegaWords2⟩ : SignRep .E6).omegaWords :=
    CFSG.ClassicalInvolution.ModelFacts.nil_mem_omegaWords_e6 hr
  set χ := signMaskChar t.tag 2 with hχ
  set F := frobTwistGL t.tag k p e (diagramMap t k) with hF
  set M := torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots χ) with hM_def
  have hD : (adjointGroup t.tag k).map (MulAut.conj (diagramMap t k)).toMonoidHom =
      adjointGroup t.tag k := map_conj_diagramMap t k (Or.inl rfl)
  have hMG : M ≤ adjointGroup t.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hne : (kernelRoots χ).Nonempty := ⟨e6Theta, layerShape_E6_mask2.mem_e⟩
  have hA := t.cartan_perm
  have hB := symmetrizedCartan_perm_E6
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_pinned_datum p hp hk he (τ := t.tag)
      (Or.inr (Or.inl rfl)) (ρ := t.perm) hA hB (h6.theta _ hr [] hr0) (Q₀ :=
        wordWeylMatrix t.tag k [] * diagramMap t k)
      (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX t [] hγ)
      (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer t))
      (map_conj_wordWeylMatrix_mul [] hD) (n6 _ hr [] hr0) hne
  have hQ₀ : wordWeylMatrix t.tag k [] * diagramMap t k = diagramMap t k := by
    rw [CFSG.ClassicalInvolution.ModelFacts.wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hDF hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_rootDiagUnit_frob_eq p t he a₀⁻¹
  set u := rootDiagUnit t.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL t.tag k p e (h * diagramMap t k) y = h * F y * h⁻¹ :=
    fun y => CFSG.ClassicalInvolution.ModelFacts.frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) :=
    CFSG.ClassicalInvolution.ModelFacts.map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  have hθ1 : ∀ γ, thetaMap (ToralSign.wordElt Tag.E6 []) t.perm γ = permLattice t.perm γ :=
    fun γ => by
      rw [wordElt_nil]
      exact CFSG.ClassicalInvolution.ModelFacts.thetaMap_one _ γ
  exact ⟨D, s, hDχ, hDe, fun γ => (hDθ γ).trans (congrArg toReal (hθ1 γ)),
    hconj.trans hX.symm⟩

end Datum

section Orbits

@[expose] def e6a3 : Fin TwistTag.E6.tag.rank → ℤ := Pi.single ⟨2, by decide⟩ 1

@[expose] def e6a4 : Fin TwistTag.E6.tag.rank → ℤ := Pi.single ⟨3, by decide⟩ 1

@[expose] def e6a5 : Fin TwistTag.E6.tag.rank → ℤ := Pi.single ⟨4, by decide⟩ 1

theorem perm_e6Theta : permLattice TwistTag.E6.perm e6Theta = e6Theta :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm e6Theta) =
    List.ofFn e6Theta)

theorem perm_e6a3 : permLattice TwistTag.E6.perm e6a3 = e6a5 :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm e6a3) =
    List.ofFn e6a5)

theorem perm_e6a5 : permLattice TwistTag.E6.perm e6a5 = e6a3 :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm e6a5) =
    List.ofFn e6a3)

theorem perm_e6a4 : permLattice TwistTag.E6.perm e6a4 = e6a4 :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm e6a4) =
    List.ofFn e6a4)

theorem height_e6Theta : height e6Theta = 11 := by decide

theorem height_e6a3 : height e6a3 = 1 := by decide

theorem height_e6a4 : height e6a4 = 1 := by decide

theorem height_add' {τ : Tag} (u v : Fin τ.rank → ℤ) : height (u + v) = height u + height v := by
  simp [height, Finset.sum_add_distrib]

theorem height_neg' {τ : Tag} (u : Fin τ.rank → ℤ) : height (-u) = - height u := by
  simp [height]

end Orbits

section Classes

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))

include hDχ in
theorem mask2_shape : LayerShape D.χ e6Theta e6a4 e6a3 := by
  rw [hDχ]
  exact layerShape_E6_mask2

include hDθ in
theorem theta_pow (m : ℕ) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    (D.θ ^ m) (toReal γ) = toReal ((permLattice TwistTag.E6.perm)^[m] γ) := by
  induction m generalizing γ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, hDθ, Function.iterate_succ_apply']

@[expose] def cls₁ (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2) : KernelComponent D.χ :=
  Quotient.mk (kernelRootSetoid D.χ) ⟨e6Theta, (mask2_shape D hDχ).mem_e⟩

@[expose] def cls₂ (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2) : KernelComponent D.χ :=
  Quotient.mk (kernelRootSetoid D.χ) ⟨e6a4, (mask2_shape D hDχ).mem₂⟩

include hDχ in
theorem cls₁_ne_cls₂ : cls₁ D hDχ ≠ cls₂ D hDχ := (mask2_shape D hDχ).mk_e_ne

include hDχ hDθ in
theorem classOrbit_cls₁ : D.classOrbit (cls₁ D hDχ) = {cls₁ D hDχ} := by
  have hS := mask2_shape D hDχ
  ext i
  constructor
  · rintro ⟨m, α, ⟨hαK, hα⟩, β, ⟨hβK, hβ⟩, hm⟩
    have hαθ : α = e6Theta ∨ α = -e6Theta := (hS.mk_eq_e_iff α hαK).1 hα
    have h1 := theta_pow D hDθ m α
    have hfix : (permLattice TwistTag.E6.perm)^[m] e6Theta = e6Theta :=
      Function.iterate_fixed perm_e6Theta m
    have hfix' : (permLattice TwistTag.E6.perm)^[m] (-e6Theta) = -e6Theta :=
      Function.iterate_fixed (by rw [permLattice_neg, perm_e6Theta]) m
    have hβθ : β = e6Theta ∨ β = -e6Theta := by
      rcases hαθ with rfl | rfl
      · exact Or.inl (toReal_injective (hm.symm.trans (h1.trans (congrArg toReal hfix))))
      · exact Or.inr (toReal_injective (hm.symm.trans (h1.trans (congrArg toReal hfix'))))
    have hcl : (Quotient.mk (kernelRootSetoid D.χ) ⟨β, hβK⟩ : KernelComponent D.χ) = cls₁ D hDχ :=
      (hS.mk_eq_e_iff β hβK).2 hβθ
    rw [← hβ, hcl]
    exact Set.mem_singleton _
  · intro hi
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    exact D.self_mem_classOrbit _

include hDχ hDθ in
theorem classOrbit_cls₂ : D.classOrbit (cls₂ D hDχ) = {cls₂ D hDχ} := by
  have hS := mask2_shape D hDχ
  ext i
  constructor
  · rintro ⟨m, α, ⟨hαK, hα⟩, β, ⟨hβK, hβ⟩, hm⟩
    have hαne1 : α ≠ e6Theta := fun h => hS.mk_e_ne ((hS.mk_eq_e_iff α hαK).2 (Or.inl h) ▸ hα)
    have hαne2 : α ≠ -e6Theta := fun h =>
      hS.mk_e_ne ((hS.mk_eq_e_iff α hαK).2 (Or.inr h) ▸ hα)
    have h1 := theta_pow D hDθ m α
    have hfix : (permLattice TwistTag.E6.perm)^[m] e6Theta = e6Theta :=
      Function.iterate_fixed perm_e6Theta m
    have hfix' : (permLattice TwistTag.E6.perm)^[m] (-e6Theta) = -e6Theta :=
      Function.iterate_fixed (by rw [permLattice_neg, perm_e6Theta]) m
    have hinj : Function.Injective ((permLattice TwistTag.E6.perm)^[m]) :=
      (CFSG.LieType.Chevalley.permLattice_injective TwistTag.E6.perm).iterate m
    have hβ' : (permLattice TwistTag.E6.perm)^[m] α = β :=
      toReal_injective (h1.symm.trans hm)
    have hβne1 : β ≠ e6Theta := fun h => hαne1 (hinj (hβ'.trans (h.trans hfix.symm)))
    have hβne2 : β ≠ -e6Theta := fun h => hαne2 (hinj (hβ'.trans (h.trans hfix'.symm)))
    have hcl : (Quotient.mk (kernelRootSetoid D.χ) ⟨β, hβK⟩ : KernelComponent D.χ) = cls₂ D hDχ :=
      hS.conn β hβK hβne1 hβne2
    rw [← hβ, hcl]
    exact Set.mem_singleton _
  · intro hi
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    exact D.self_mem_classOrbit _

theorem exists_two_orbits (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ)) :
    ∃ J₁ J₂ : Set.range D.classOrbit, J₁ ≠ J₂ ∧ (∀ J, J = J₁ ∨ J = J₂) ∧
      (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ} ∧
      (J₂ : Set (KernelComponent D.χ)) = {cls₂ D hDχ} := by
  have hS := mask2_shape D hDχ
  let J₁ : Set.range D.classOrbit := ⟨D.classOrbit (cls₁ D hDχ), cls₁ D hDχ, rfl⟩
  let J₂ : Set.range D.classOrbit := ⟨D.classOrbit (cls₂ D hDχ), cls₂ D hDχ, rfl⟩
  have h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ} := classOrbit_cls₁ D hDχ hDθ
  have h2 : (J₂ : Set (KernelComponent D.χ)) = {cls₂ D hDχ} := classOrbit_cls₂ D hDχ hDθ
  refine ⟨J₁, J₂, fun h => cls₁_ne_cls₂ D hDχ ?_, fun J => ?_, h1, h2⟩
  · have := congrArg (fun J : Set.range D.classOrbit => (J : Set (KernelComponent D.χ))) h
    simp only [h1, h2, Set.singleton_eq_singleton_iff] at this
    exact this
  · obtain ⟨_, i, rfl⟩ := J
    rcases hS.exists_eq i with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

end Classes

section Simple

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))

include hDχ in
theorem mem_simpleRoots_cls₁ {β : Fin TwistTag.E6.tag.rank → ℤ} :
    β ∈ simpleRoots (componentRoots D.χ (cls₁ D hDχ)) ↔ β = e6Theta := by
  have hS := mask2_shape D hDχ
  have hmem : ∀ γ, γ ∈ componentRoots D.χ (cls₁ D hDχ) ↔ γ = e6Theta ∨ γ = -e6Theta := by
    intro γ
    constructor
    · rintro ⟨h, hγ⟩
      exact (hS.mk_eq_e_iff γ h).1 hγ
    · intro h
      have hK : γ ∈ kernelRoots D.χ := by
        rcases h with rfl | rfl
        · exact hS.mem_e
        · exact CFSG.ClassicalInvolution.ModelFacts.neg_mem_kernelRoots hS.mem_e
      exact ⟨hK, (hS.mk_eq_e_iff γ hK).2 h⟩
  have hpos : ∀ γ, γ ∈ posRoots (componentRoots D.χ (cls₁ D hDχ)) ↔ γ = e6Theta := by
    intro γ
    constructor
    · rintro ⟨h1, h2⟩
      rcases (hmem γ).1 h1 with h | h
      · exact h
      · rw [h, height_neg', height_e6Theta] at h2
        omega
    · rintro rfl
      exact ⟨(hmem _).2 (Or.inl rfl), by rw [height_e6Theta]; omega⟩
  rw [mem_simpleRoots]
  constructor
  · rintro ⟨-, h, -⟩
    exact (hpos β).1 h
  · rintro rfl
    refine ⟨isRoot_e6Theta, (hpos _).2 rfl, fun γ hγ δ hδ h => ?_⟩
    rw [(hpos γ).1 hγ, (hpos δ).1 hδ] at h
    exact absurd (congrArg List.ofFn h) (by decide)

include hDχ in
theorem mem_simpleRoots_cls₂_a4 : e6a4 ∈ simpleRoots (componentRoots D.χ (cls₂ D hDχ)) := by
  have hS := mask2_shape D hDχ
  rw [mem_simpleRoots]
  refine ⟨isRoot_single _ _, ⟨⟨hS.mem₂, rfl⟩, by rw [height_e6a4]; omega⟩,
    fun γ hγ δ hδ h => ?_⟩
  have h1 := hγ.2
  have h2 := hδ.2
  have := congrArg height h
  rw [height_add', height_e6a4] at this
  omega

include hDχ in
theorem mem_simpleRoots_cls₂_a3 : e6a3 ∈ simpleRoots (componentRoots D.χ (cls₂ D hDχ)) := by
  have hS := mask2_shape D hDχ
  rw [mem_simpleRoots]
  refine ⟨isRoot_single _ _, ⟨⟨hS.mem₃, hS.conn _ hS.mem₃ hS.ne₃ hS.ne₃'⟩, by
    rw [height_e6a3]; omega⟩, fun γ hγ δ hδ h => ?_⟩
  have h1 := hγ.2
  have h2 := hδ.2
  have := congrArg height h
  rw [height_add', height_e6a3] at this
  omega

end Simple

section OrbitSets

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))

include hDθ in
theorem thetaOrbit_theta : thetaOrbit D.θ e6Theta = {e6Theta} := by
  ext β
  constructor
  · rintro ⟨m, hm⟩
    rw [theta_pow D hDθ m] at hm
    have hfix : (permLattice TwistTag.E6.perm)^[m] e6Theta = e6Theta :=
      Function.iterate_fixed perm_e6Theta m
    rw [hfix] at hm
    exact (toReal_injective hm).symm
  · intro hβ
    rw [Set.mem_singleton_iff] at hβ
    rw [hβ]
    exact self_mem_thetaOrbit _ _

include hDθ in
theorem thetaOrbit_a3 : thetaOrbit D.θ e6a3 = {e6a3, e6a5} := by
  have key : ∀ m : ℕ, (permLattice TwistTag.E6.perm)^[m] e6a3 = e6a3 ∨
      (permLattice TwistTag.E6.perm)^[m] e6a3 = e6a5 := by
    intro m
    induction m with
    | zero => exact Or.inl rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h, perm_e6a3]
        exact Or.inr rfl
      · rw [h, perm_e6a5]
        exact Or.inl rfl
  ext β
  constructor
  · rintro ⟨m, hm⟩
    rw [theta_pow D hDθ m] at hm
    have hβ := toReal_injective hm
    rcases key m with h | h
    · rw [h] at hβ
      exact Or.inl hβ.symm
    · rw [h] at hβ
      exact Or.inr hβ.symm
  · rintro (rfl | rfl)
    · exact self_mem_thetaOrbit _ _
    · refine ⟨1, ?_⟩
      rw [theta_pow D hDθ 1]
      simp only [Function.iterate_one, perm_e6a3]

theorem e6a3_ne_e6a5 : e6a3 ≠ e6a5 := fun h => absurd (congrArg List.ofFn h) (by decide)

theorem e6a4_ne_e6a3 : e6a4 ≠ e6a3 := fun h => absurd (congrArg List.ofFn h) (by decide)

theorem e6a4_ne_e6a5 : e6a4 ≠ e6a5 := fun h => absurd (congrArg List.ofFn h) (by decide)

include hDθ in
theorem thetaOrbit_a3_ncard : (thetaOrbit D.θ e6a3).ncard = 2 := by
  rw [thetaOrbit_a3 D hDθ]
  exact Set.ncard_pair e6a3_ne_e6a5

include hDθ in
theorem thetaOrbit_a4 : thetaOrbit D.θ e6a4 = {e6a4} := by
  ext β
  constructor
  · rintro ⟨m, hm⟩
    rw [theta_pow D hDθ m] at hm
    have hfix : (permLattice TwistTag.E6.perm)^[m] e6a4 = e6a4 :=
      Function.iterate_fixed perm_e6a4 m
    rw [hfix] at hm
    exact (toReal_injective hm).symm
  · intro hβ
    rw [Set.mem_singleton_iff] at hβ
    rw [hβ]
    exact self_mem_thetaOrbit _ _

include hDθ in
theorem thetaOrbit_a3_ne_a4 : thetaOrbit D.θ e6a3 ≠ thetaOrbit D.θ e6a4 := by
  rw [thetaOrbit_a3 D hDθ, thetaOrbit_a4 D hDθ]
  intro h
  have : e6a3 ∈ ({e6a4} : Set (Fin TwistTag.E6.tag.rank → ℤ)) := by
    rw [← h]
    exact Or.inl rfl
  exact e6a4_ne_e6a3 (Set.mem_singleton_iff.1 this).symm

end OrbitSets

section OrbitsJ

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
  {J₁ J₂ : Set.range D.classOrbit} (h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ})
  (h2 : (J₂ : Set (KernelComponent D.χ)) = {cls₂ D hDχ})

include h1 in
theorem mem_J₁_iff {i : KernelComponent D.χ} : i ∈ (D.withOrbit J₁).J ↔ i = cls₁ D hDχ := by
  have h : i ∈ (D.withOrbit J₁).J ↔ i ∈ (J₁ : Set (KernelComponent D.χ)) := Iff.rfl
  rw [h, h1]
  exact Set.mem_singleton_iff

include h2 in
theorem mem_J₂_iff {i : KernelComponent D.χ} : i ∈ (D.withOrbit J₂).J ↔ i = cls₂ D hDχ := by
  have h : i ∈ (D.withOrbit J₂).J ↔ i ∈ (J₂ : Set (KernelComponent D.χ)) := Iff.rfl
  rw [h, h2]
  exact Set.mem_singleton_iff

include hDχ hDθ h1 in
theorem orbits_J₁ : (D.withOrbit J₁).orbits = {{e6Theta}} := by
  ext O
  constructor
  · rintro ⟨β, hβ, rfl⟩
    rw [(D.withOrbit J₁).simpleRootsJ_eq] at hβ
    obtain ⟨i, hi, hβi⟩ := hβ
    have hi' : i = cls₁ D hDχ := (mem_J₁_iff D hDχ h1).1 hi
    subst hi'
    have hβθ := (mem_simpleRoots_cls₁ D hDχ).1 hβi
    subst hβθ
    exact (thetaOrbit_theta D hDθ).symm ▸ Set.mem_singleton _
  · intro hO
    rw [Set.mem_singleton_iff] at hO
    subst hO
    refine ⟨e6Theta, ?_, (thetaOrbit_theta D hDθ).symm⟩
    rw [(D.withOrbit J₁).simpleRootsJ_eq]
    exact ⟨cls₁ D hDχ, (mem_J₁_iff D hDχ h1).2 rfl, (mem_simpleRoots_cls₁ D hDχ).2 rfl⟩

include hDχ h2 in
theorem a4_mem_simpleRootsJ : e6a4 ∈ (D.withOrbit J₂).simpleRootsJ := by
  rw [(D.withOrbit J₂).simpleRootsJ_eq]
  exact ⟨cls₂ D hDχ, (mem_J₂_iff D hDχ h2).2 rfl, mem_simpleRoots_cls₂_a4 D hDχ⟩

include hDχ h2 in
theorem a3_mem_simpleRootsJ : e6a3 ∈ (D.withOrbit J₂).simpleRootsJ := by
  rw [(D.withOrbit J₂).simpleRootsJ_eq]
  exact ⟨cls₂ D hDχ, (mem_J₂_iff D hDχ h2).2 rfl, mem_simpleRoots_cls₂_a3 D hDχ⟩

include hDχ h2 in
theorem thetaOrbit_a3_mem_orbits : thetaOrbit D.θ e6a3 ∈ (D.withOrbit J₂).orbits :=
  ⟨e6a3, a3_mem_simpleRootsJ D hDχ h2, rfl⟩

include hDχ h2 in
theorem thetaOrbit_a4_mem_orbits : thetaOrbit D.θ e6a4 ∈ (D.withOrbit J₂).orbits :=
  ⟨e6a4, a4_mem_simpleRootsJ D hDχ h2, rfl⟩

include hDχ hDθ h2 in
theorem isQuasisimple_orbitGroup_J₂ : CFSG.IsQuasisimple (D.withOrbit J₂).orbitGroup := by
  have hfin : (D.withOrbit J₂).orbits.Finite := by
    have : (D.withOrbit J₂).orbits =
        (thetaOrbit D.θ) '' (D.withOrbit J₂).simpleRootsJ := by
      ext O
      exact ⟨fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩, fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩⟩
    rw [this]
    exact ((D.withOrbit J₂).finite_roots.subset fun _ h => h.2).image _
  refine (orthogonal_semilinear_fixed_root_quasisimplicity (D.withOrbit J₂)).2.2.1 ?_
  have := (Set.one_lt_ncard hfin).2 ⟨_, thetaOrbit_a3_mem_orbits D hDχ h2, _,
    thetaOrbit_a4_mem_orbits D hDχ h2, thetaOrbit_a3_ne_a4 D hDθ⟩
  omega

end OrbitsJ

section Identify

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

variable (p k) in
@[expose] noncomputable def rankOneFix (e : ℕ) : Subgroup (ModGL TwistTag.E6.tag k) :=
  fixedPointsIn (rootSubgroup TwistTag.E6.tag k e6Theta)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ⊔
    fixedPointsIn (rootSubgroup TwistTag.E6.tag k (-e6Theta))
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))

end Identify

section Identify2

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
  {J₁ J₂ : Set.range D.classOrbit} (h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ})
  (h2 : (J₂ : Set (KernelComponent D.χ)) = {cls₂ D hDχ})

theorem conj_conj_inv {M : Type*} [Group M] (u : M) :
    (MulAut.conj u).toMonoidHom.comp (MulAut.conj u⁻¹).toMonoidHom = MonoidHom.id M := by
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    MonoidHom.id_apply]
  group

include hDχ hDθ h1 in
theorem orbitGroup_J₁_eq {e : ℕ} (he : 1 ≤ e)
    {s : Fin TwistTag.E6.tag.rank → kˣ} (hDe : D.e = e)
    (hconj : (fixedPointsIn (torusGroup TwistTag.E6.tag k ⊔
          rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)))
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))).map
          (MulAut.conj (rootDiagUnit TwistTag.E6.tag s)).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype) :
    (D.withOrbit J₁).orbitGroup =
      (rankOneFix p k e).map (MulAut.conj (rootDiagUnit TwistTag.E6.tag s)).toMonoidHom := by
  classical
  set D₁ := D.withOrbit J₁ with hD₁
  have hO : D₁.orbits = {{e6Theta}} := orbits_J₁ D hDχ hDθ h1
  have hOm : ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∈ D₁.orbits := by
    rw [hO]
    exact Set.mem_singleton _
  have hcard : OrthogonalSemilinearFixedRootDatum.orbitCard
      ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = 1 := Set.ncard_singleton _
  have hroot : OrthogonalSemilinearFixedRootDatum.orbitRoot
      ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = e6Theta := by
    have := D₁.orbitRoot_mem hOm
    exact Set.mem_singleton_iff.1 this
  set u := rootDiagUnit TwistTag.E6.tag s with hu
  have hCX : D₁.orbitGroup ≤ D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
    intro c hc
    have hcG : c ∈ adjointGroup TwistTag.E6.tag k := D₁.orbitGroup_le_adjointGroup hc
    have hmem : (⟨c, hcG⟩ : adjointGroup TwistTag.E6.tag k) ∈ D₁.orbitGroupC := hc
    have hX := D.kernelFixedGroup_le_totalFixedGroup
      ((D.fixedGroup_withOrbit_le_kernelFixedGroup J₁) (D₁.orbitGroupC_le_fixedGroup hmem))
    exact ⟨_, hX, rfl⟩
  have hJF : ∀ y ∈ D₁.orbitGroup.map (MulAut.conj u⁻¹).toMonoidHom,
      frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) y = y := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := hCX hc
    rw [← hconj] at hc'
    obtain ⟨m, hm, rfl⟩ := hc'
    have : (MulAut.conj u⁻¹).toMonoidHom ((MulAut.conj u).toMonoidHom m) = m := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact (mem_fixedPointsIn.1 hm).2
  have hFq : Nat.card (D₁.orbitField {e6Theta}) = p ^ e := by
    rw [D₁.card_orbitField hOm, hcard, pow_one]
    change p ^ D.e = p ^ e
    rw [hDe]
  have hJ : ∀ y : ModGL TwistTag.E6.tag k,
      y ∈ (D₁.orbitGroup.map (MulAut.conj u⁻¹).toMonoidHom).map
          (MulAut.conj (rootDiagUnit TwistTag.E6.tag s)).toMonoidHom ↔
        ∃ A : SL(2, D₁.orbitField {e6Theta}), y = rootSL2 TwistTag.E6.tag k e6Theta
          (Matrix.SpecialLinearGroup.map (D₁.orbitField {e6Theta}).subtype A) := by
    intro y
    rw [Subgroup.map_map, conj_conj_inv, Subgroup.map_id, ← SetLike.mem_coe,
      ← D₁.range_orbitMap_eq_of_orbits_eq hO]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, by rw [orbitMap_of_orbitCard_eq_one D₁ hcard, hroot]⟩
    · rintro ⟨A, rfl⟩
      exact ⟨A, by rw [orbitMap_of_orbitCard_eq_one D₁ hcard, hroot]⟩
  have hfix : permLattice TwistTag.E6.perm e6Theta = e6Theta := perm_e6Theta
  have heq := CFSG.ClassicalInvolution.ModelFacts.eq_fixed_rootSubgroup_sup_of_conj p
    TwistTag.E6 he isRoot_e6Theta hfix s hJF hFq hJ
  rw [rankOneFix, ← heq, Subgroup.map_map, conj_conj_inv, Subgroup.map_id]

end Identify2

section Torus

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem iform_e6Theta_e6Theta : iform e6Theta e6Theta = 2 := by decide

theorem iform_e6Theta_single (j : Fin TwistTag.E6.tag.rank) :
    2 * iform e6Theta (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) / iform e6Theta e6Theta =
      (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ⟨1, by decide⟩ := by
  rw [iform_e6Theta_e6Theta]
  fin_cases j <;> decide

theorem rootTorusSL2_e6Theta (a : kˣ) :
    rootTorusSL2 TwistTag.E6.tag k e6Theta a =
      rootDiagUnit TwistTag.E6.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) a) := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag k isRoot_e6Theta
  obtain ⟨b, hb, -⟩ := hH _ (hdH a)
  rw [hb]
  congr 1
  funext j
  have h1 := (hv a).2 (Pi.single j 1) (isRoot_single _ j)
  rw [hb] at h1
  change rootDiag b (rootVec _ k _) = _ at h1
  rw [rootDiag_rootVec b (isRoot_single _ j)] at h1
  have hne : rootVec TwistTag.E6.tag k (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ 0 := by
    rw [CFSG.LieType.Chevalley.rootVec_eq_single (isRoot_single _ j)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective k hne h1
  have e : rootChar b (Pi.single j 1) = b j := by
    have := rootChar_nsmul_single b j 1
    rwa [one_nsmul, pow_one] at this
  rw [e, iform_e6Theta_single] at h3
  refine Units.ext ?_
  rw [h3]
  by_cases hj : j = ⟨1, by decide⟩
  · subst hj
    simp
  · rw [Pi.single_eq_of_ne' hj, Pi.mulSingle_eq_of_ne hj, zpow_zero]

end Torus

section Involution

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
  {J₁ J₂ : Set.range D.classOrbit} (h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ})

@[expose] noncomputable def involX (k : Type) [Field k] : ModGL TwistTag.E6.tag k :=
  rootDiagUnit TwistTag.E6.tag (signMaskTuple TwistTag.E6.tag k 2)

omit [IsAlgClosed k] [CharP k p] in
theorem involX_eq_rootTorusSL2 : involX k = rootTorusSL2 TwistTag.E6.tag k e6Theta (-1) := by
  rw [rootTorusSL2_e6Theta, involX]
  congr 1
  funext j
  by_cases hj : j = ⟨1, by decide⟩
  · subst hj
    simp [signMaskTuple]
  · rw [Pi.mulSingle_eq_of_ne hj]
    fin_cases j <;> simp_all [signMaskTuple]

include hDχ hDθ h1 in
theorem involX_mem_rankOneFix {e : ℕ} (he : 1 ≤ e)
    {s : Fin TwistTag.E6.tag.rank → kˣ} (hDe : D.e = e)
    (hconj : (fixedPointsIn (torusGroup TwistTag.E6.tag k ⊔
          rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)))
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))).map
          (MulAut.conj (rootDiagUnit TwistTag.E6.tag s)).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype) :
    involX k ∈ rankOneFix p k e := by
  classical
  set D₁ := D.withOrbit J₁ with hD₁
  have hO : D₁.orbits = {{e6Theta}} := orbits_J₁ D hDχ hDθ h1
  have hOm : ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∈ D₁.orbits := by
    rw [hO]
    exact Set.mem_singleton _
  have hcard : OrthogonalSemilinearFixedRootDatum.orbitCard
      ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = 1 := Set.ncard_singleton _
  have hroot : OrthogonalSemilinearFixedRootDatum.orbitRoot
      ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = e6Theta := by
    have := D₁.orbitRoot_mem hOm
    exact Set.mem_singleton_iff.1 this
  have hG := orbitGroup_J₁_eq D hDχ hDθ h1 he hDe hconj
  have hx : involX k ∈ D₁.orbitGroup := by
    refine D₁.orbitMap_mem_orbitGroup hOm (HSL (-1)) |> fun hmem => ?_
    have : D₁.orbitMap {e6Theta} (HSL (-1)) = involX k := by
      rw [orbitMap_of_orbitCard_eq_one D₁ hcard, hroot, involX_eq_rootTorusSL2, rootTorusSL2,
        map_HSL]
      rfl
    rwa [this] at hmem
  rw [hG] at hx
  obtain ⟨r, hr, hrx⟩ := hx
  have hcomm : Commute (rootDiagUnit TwistTag.E6.tag s) (involX k) := by
    unfold involX
    rw [Commute, SemiconjBy, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have : r = involX k := by
    have h := hrx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [mul_inv_eq_iff_eq_mul, ← hcomm.eq] at h
    exact mul_left_cancel h
  rwa [← this]

end Involution

section Card

theorem not_sq_dvd_mul_sq_sub_one (q : ℕ) (hq : 5 ≤ q) : ¬ q ^ 2 ∣ q * (q ^ 2 - 1) := by
  intro h
  have h1 : q * q ∣ q * (q * q - 1) := by
    have : q ^ 2 = q * q := sq q
    rwa [this] at h
  have h2 : q ∣ q * q - 1 := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
  have h3 : q ∣ q * q - (q * q - 1) := Nat.dvd_sub (dvd_mul_right q q) h2
  have h4 : q * q - (q * q - 1) = 1 := by
    have : 1 ≤ q * q := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  rw [h4] at h3
  have := Nat.le_of_dvd one_pos h3
  omega

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
  (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
  (hDχ : D.χ = signMaskChar TwistTag.E6.tag 2)
  (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
  {J₁ J₂ : Set.range D.classOrbit} (h1 : (J₁ : Set (KernelComponent D.χ)) = {cls₁ D hDχ})
  (h2 : (J₂ : Set (KernelComponent D.χ)) = {cls₂ D hDχ})

include hDχ hDθ h1 h2 in
theorem card_orbitGroup_ne {e : ℕ} (hq : 5 ≤ p ^ e) (hDe : D.e = e) :
    Nat.card (D.withOrbit J₂).orbitGroup ≠ Nat.card (D.withOrbit J₁).orbitGroup := by
  classical
  set D₁ := D.withOrbit J₁ with hD₁
  set D₂ := D.withOrbit J₂ with hD₂
  have hO₁ : D₁.orbits = {{e6Theta}} := orbits_J₁ D hDχ hDθ h1
  have hOm₁ : ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∈ D₁.orbits := by
    rw [hO₁]
    exact Set.mem_singleton _
  have hcard₁ : OrthogonalSemilinearFixedRootDatum.orbitCard
      ({e6Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = 1 := Set.ncard_singleton _
  have hq1 : Nat.card (D₁.orbitField {e6Theta}) = p ^ e := by
    rw [D₁.card_orbitField hOm₁, hcard₁, pow_one]
    change p ^ D.e = p ^ e
    rw [hDe]
  have hfin1 : Finite (D₁.orbitField {e6Theta}) :=
    Nat.finite_of_card_ne_zero (by rw [hq1]; positivity)
  have hC₁ : D₁.orbitGroup = (D₁.orbitMapHom hOm₁).range := by
    apply SetLike.coe_injective
    rw [MonoidHom.coe_range]
    exact (D₁.range_orbitMap_eq_of_orbits_eq hO₁).symm
  have hdvd₁ : Nat.card D₁.orbitGroup ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [hC₁]
    have := Subgroup.card_range_dvd (D₁.orbitMapHom hOm₁)
    rwa [CFSG.GorensteinWalter.sl2_card_formula, hq1] at this
  have hO₃ := thetaOrbit_a3_mem_orbits D hDχ h2
  have hcard₃ := thetaOrbit_a3_ncard D hDθ
  set O₃ := thetaOrbit D.θ e6a3 with hO₃def
  have hq3 : Nat.card (D₂.orbitField O₃) = (p ^ e) ^ 2 := by
    rw [D₂.card_orbitField hO₃]
    change D₂.q ^ O₃.ncard = (p ^ e) ^ 2
    rw [hcard₃]
    change (p ^ D.e) ^ 2 = (p ^ e) ^ 2
    rw [hDe]
  let φ : Multiplicative (D₂.orbitField O₃) →* ModGL TwistTag.E6.tag k :=
    { toFun := fun c => D₂.orbitX O₃ (Multiplicative.toAdd c)
      map_one' := by
        change D₂.orbitX O₃ 0 = 1
        rw [OrthogonalSemilinearFixedRootDatum.orbitX, uSL_zero_eq_one, D₂.orbitMap_one]
      map_mul' := fun a b => by
        change D₂.orbitX O₃ (Multiplicative.toAdd a + Multiplicative.toAdd b) = _
        exact D₂.orbitX_add hO₃ _ _ }
  have hφinj : Function.Injective φ := fun a b h =>
    Multiplicative.toAdd.injective (D₂.orbitX_injective hO₃ h)
  have hφle : φ.range ≤ D₂.orbitGroup := by
    rintro _ ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨O₃, hO₃, Multiplicative.toAdd c, Or.inl rfl⟩
  have hcardφ : Nat.card φ.range = (p ^ e) ^ 2 := by
    have h1 : Nat.card φ.range = Nat.card (Multiplicative (D₂.orbitField O₃)) :=
      (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
    rw [h1, Nat.card_congr Multiplicative.toAdd, hq3]
  have hdvd₂ : (p ^ e) ^ 2 ∣ Nat.card D₂.orbitGroup := by
    rw [← hcardφ]
    exact Subgroup.card_dvd_of_le hφle
  intro heq
  rw [heq] at hdvd₂
  exact not_sq_dvd_mul_sq_sub_one (p ^ e) hq (hdvd₂.trans hdvd₁)

end Card

section Main

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem orbitGroup_le_totalFixed {τ : Tag}
    (D : OrthogonalSemilinearFixedRootDatum τ p k) (J : Set.range D.classOrbit) :
    (D.withOrbit J).orbitGroup ≤ D.totalFixedGroup.map (adjointGroup τ k).subtype := by
  intro c hc
  have hcG : c ∈ adjointGroup τ k := (D.withOrbit J).orbitGroup_le_adjointGroup hc
  have hmem : (⟨c, hcG⟩ : adjointGroup τ k) ∈ (D.withOrbit J).orbitGroupC := hc
  exact ⟨_, D.kernelFixedGroup_le_totalFixedGroup
    ((D.fixedGroup_withOrbit_le_kernelFixedGroup J)
      ((D.withOrbit J).orbitGroupC_le_fixedGroup hmem)), rfl⟩

end Main

section Layer

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

variable (p k) in
@[expose] noncomputable def twistedR (e : ℕ) : Subgroup (ModGL TwistTag.E6.tag k) :=
  fixedPointsIn (adjointGroup TwistTag.E6.tag k)
    (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))

theorem mem_fixedPointsIn_of_commutes_involX (hp : p ≠ 2) {e : ℕ}
    {y : ModGL TwistTag.E6.tag k} (hyG : y ∈ adjointGroup TwistTag.E6.tag k)
    (hyF : frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) y = y)
    (hyx : involX k * y = y * involX k) :
    y ∈ fixedPointsIn (torusGroup TwistTag.E6.tag k ⊔
        rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)))
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set χ := signMaskChar TwistTag.E6.tag 2 with hχ
  have ha : signCharTuple (k := k) χ = signMaskTuple TwistTag.E6.tag k 2 :=
    signCharTuple_signMaskChar 2
  have hZ := (CFSG.LieType.AlgebraicGroups.exceptional_toral_centralizer_identity_component
    TwistTag.E6.tag k hk2 (signCharTuple (k := k) χ) (signCharTuple_sign χ)).2.2.2.2.1
    (Or.inr (Or.inr (Or.inl rfl)))
  have hy : y ∈ toralCentralizer TwistTag.E6.tag k (signCharTuple (k := k) χ) := by
    rw [mem_toralCentralizer]
    refine ⟨hyG, ?_⟩
    rw [ha]
    change involX k * y * (involX k)⁻¹ = y
    rw [hyx]
    group
  rw [← hZ] at hy
  refine mem_fixedPointsIn.2 ⟨?_, hyF⟩
  change y ∈ torusGroup TwistTag.E6.tag k ⊔
    rootSpan TwistTag.E6.tag k (rootCharKernel (signCharTuple (k := k) χ)) at hy
  rwa [rootCharKernel_signCharTuple hk2 χ] at hy

omit [IsAlgClosed k] [CharP k p] [Fact p.Prime] in
theorem perfect_comap_subtype {M : Type*} [Group M] {G P : Subgroup M} (hPG : P ≤ G)
    (hP : P ≤ ⁅P, P⁆) :
    P.comap G.subtype ≤ ⁅P.comap G.subtype, P.comap G.subtype⁆ := by
  have hm : (P.comap G.subtype).map G.subtype = P := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.2 hPG
  have h2 : (⁅P.comap G.subtype, P.comap G.subtype⁆).map G.subtype = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, hm]
  intro x hx
  have h3 : (x : M) ∈ (⁅P.comap G.subtype, P.comap G.subtype⁆).map G.subtype := by
    rw [h2]
    exact hP hx
  obtain ⟨w, hw, hwx⟩ := h3
  exact (Subtype.ext hwx : w = x) ▸ hw

theorem exists_twisted_layer (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (hq : 5 ≤ p ^ e) :
    ∃ L : Subgroup (ModGL TwistTag.E6.tag k),
      L ≤ ⁅twistedR p k e, twistedR p k e⁆ ∧ CFSG.Open.IsQuasisimple ↥L ∧
      L ≤ Subgroup.centralizer (rankOneFix p k e : Set (ModGL TwistTag.E6.tag k)) ∧
      (∀ P : Subgroup (ModGL TwistTag.E6.tag k), P ≤ ⁅twistedR p k e, twistedR p k e⁆ →
        P ≤ Subgroup.centralizer (rankOneFix p k e : Set (ModGL TwistTag.E6.tag k)) →
          P ≤ ⁅P, P⁆ → P ≤ L) ∧
      Nat.card ↥L ≠ Nat.card ↥(rankOneFix p k e) := by
  classical
  obtain ⟨D, s, hDχ, hDe, hDθ, hconj⟩ := exists_mask2_datum p hp hk he
  obtain ⟨J₁, J₂, hne, hJ, h1, h2⟩ := exists_two_orbits D hDχ hDθ
  have hC₁ := orbitGroup_J₁_eq D hDχ hDθ h1 he hDe hconj
  have hx := involX_mem_rankOneFix D hDχ hDθ h1 he hDe hconj
  have hqs₂ := CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
    (isQuasisimple_orbitGroup_J₂ D hDχ hDθ h2)
  have hcard := card_orbitGroup_ne D hDχ hDθ h1 h2 hq hDe
  set u := rootDiagUnit TwistTag.E6.tag s with hu
  set Mk := torusGroup TwistTag.E6.tag k ⊔
    rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 2)) with hMk
  set Fk := frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) with hFk
  have hMG : Mk ≤ adjointGroup TwistTag.E6.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  set C₂ := (D.withOrbit J₂).orbitGroup with hC₂
  set L := C₂.map (MulAut.conj u⁻¹).toMonoidHom with hL
  have hLM : L ≤ fixedPointsIn Mk Fk := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := orbitGroup_le_totalFixed D J₂ hc
    rw [← hconj] at hc'
    obtain ⟨m, hm, rfl⟩ := hc'
    have : (MulAut.conj u⁻¹).toMonoidHom ((MulAut.conj u).toMonoidHom m) = m := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hm
  have hLR : L ≤ twistedR p k e := hLM.trans (inf_le_inf_right _ hMG)
  have hqL : CFSG.Open.IsQuasisimple ↥L :=
    (open_isQuasisimple_congr (Subgroup.equivMapOfInjective C₂ (MulAut.conj u⁻¹).toMonoidHom
      (MulAut.conj u⁻¹).injective)).1 hqs₂
  have hLperf : L ≤ ⁅L, L⁆ := by
    have : Group.IsPerfect ↥L := ⟨hqL.1⟩
    exact (Subgroup.isPerfect_iff.1 this).ge
  refine ⟨L, hLperf.trans (Subgroup.commutator_mono hLR hLR), hqL, ?_, ?_, ?_⟩
  ·
    rintro y ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : u * r * u⁻¹ ∈ (D.withOrbit J₁).orbitGroup := by
      rw [hC₁]
      exact ⟨r, hr, rfl⟩
    have hcomm : Commute (u * r * u⁻¹) c :=
      D.commute_of_ne hne ((D.withOrbit J₁).orbitGroup_le_rootSpanJ hr')
        ((D.withOrbit J₂).orbitGroup_le_rootSpanJ hc)
    have h := hcomm.eq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc r * (u⁻¹ * c * u⁻¹⁻¹) = u⁻¹ * ((u * r * u⁻¹) * c) * u := by group
      _ = u⁻¹ * (c * (u * r * u⁻¹)) * u := by rw [h]
      _ = u⁻¹ * c * u⁻¹⁻¹ * r := by group
  ·
    intro P hPH hPC hPperf
    have hPR : P ≤ twistedR p k e := hPH.trans (Subgroup.commutator_le_of_le le_rfl le_rfl)
    have hPM : P ≤ fixedPointsIn Mk Fk := by
      intro y hy
      obtain ⟨hyG, hyF⟩ := mem_fixedPointsIn.1 (hPR hy)
      exact mem_fixedPointsIn_of_commutes_involX hp hyG hyF
        (Subgroup.mem_centralizer_iff.1 (hPC hy) _ hx)
    set X' := D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype with hX'
    set P₂ := P.map (MulAut.conj u).toMonoidHom with hP₂
    have hP₂X : P₂ ≤ X' := by
      rw [← hconj]
      exact Subgroup.map_mono hPM
    have hP₂G : P₂ ≤ adjointGroup TwistTag.E6.tag k := by
      rintro _ hy
      obtain ⟨x, -, rfl⟩ := hP₂X hy
      exact x.2
    have hP₂perf : P₂ ≤ ⁅P₂, P₂⁆ := by
      rw [hP₂, ← Subgroup.map_commutator]
      exact Subgroup.map_mono hPperf
    set P'' : Subgroup (adjointGroup TwistTag.E6.tag k) :=
      P₂.comap (adjointGroup TwistTag.E6.tag k).subtype with hP''
    have hP''X : P'' ≤ D.totalFixedGroup := by
      intro x hx'
      obtain ⟨z, hz, hzx⟩ := hP₂X hx'
      exact (Subtype.ext hzx : z = x) ▸ hz
    have hP''perf : P'' ≤ ⁅P'', P''⁆ := perfect_comap_subtype hP₂G hP₂perf
    have hP''C : P'' ≤ Subgroup.centralizer
        ((D.withOrbit J₁).orbitGroupC : Set (adjointGroup TwistTag.E6.tag k)) := by
      intro x hx'
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hc' : (c : ModGL TwistTag.E6.tag k) ∈ (D.withOrbit J₁).orbitGroup := hc
      rw [hC₁] at hc'
      obtain ⟨r, hr, hrc⟩ := hc'
      obtain ⟨y, hy, hyx⟩ := (show (x : ModGL TwistTag.E6.tag k) ∈ P₂ from hx')
      have hry := Subgroup.mem_centralizer_iff.1 (hPC hy) r hr
      apply Subtype.ext
      change (c : ModGL TwistTag.E6.tag k) * x = x * c
      rw [← hrc, ← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc u * r * u⁻¹ * (u * y * u⁻¹) = u * (r * y) * u⁻¹ := by group
        _ = u * (y * r) * u⁻¹ := by rw [hry]
        _ = u * y * u⁻¹ * (u * r * u⁻¹) := by group
    have hPC₂ := le_orbitGroupC_of_perfect D hne hJ hP''X hP''perf hP''C
    intro y hy
    have hyP'' : (⟨u * y * u⁻¹, hP₂G ⟨y, hy, rfl⟩⟩ : adjointGroup TwistTag.E6.tag k) ∈ P'' :=
      ⟨y, hy, rfl⟩
    have hmem : u * y * u⁻¹ ∈ C₂ := hPC₂ hyP''
    exact ⟨u * y * u⁻¹, hmem, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group⟩
  ·
    intro heq
    apply hcard
    have e1 : Nat.card ↥L = Nat.card ↥C₂ :=
      (Nat.card_congr (Subgroup.equivMapOfInjective C₂ (MulAut.conj u⁻¹).toMonoidHom
        (MulAut.conj u⁻¹).injective).toEquiv).symm
    have e2 : Nat.card ↥(rankOneFix p k e) =
        Nat.card ↥((D.withOrbit J₁).orbitGroup) := by
      rw [hC₁]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj u).toMonoidHom
        (MulAut.conj u).injective).toEquiv
    rw [← e1, ← e2]
    exact heq

end Layer

end CFSG.ClassicalInvolution.RouteD.Exotic
