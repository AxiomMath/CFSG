module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv Topology
  CFSG.LieType.AlgebraicGroups

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

variable {τ : Tag} {k : Type} [Field k]

theorem toral_root_subgroup_regular_cover_char
    {M : Type} [CommGroup M] (τ : Tag) (k : Type) [Field k]
    [IsAlgClosed k] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    {nI : ℕ} (κ : Fin nI → KernelComponent χ)
    (hκ : Function.Bijective κ) {m : Fin nI → ℕ}
    (α : (l : Fin nI) → Fin (m l) → Fin τ.rank → ℤ) (hα : ∀ l, Function.Injective (α l))
    (hαr : ∀ l, Set.range (α l) = posRoots (componentRoots χ (κ l)))
    (v : (Fin τ.rank → ℤ) → WeylGroup τ) (j : (Fin τ.rank → ℤ) → Fin τ.rank)
    (hvj : ∀ i, ∀ β ∈ simpleRoots (componentRoots χ i),
      v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
    (ω : KernelComponent χ → WeylGroup τ → List (Fin τ.rank → ℤ))
    (hω : ∀ i, ∀ w ∈ componentWeylGroup (componentRoots χ i),
      IsComponentWord (componentRoots χ i) (ω i w) ∧
        reflectionWordProd (ω i w) = w) :
    (∀ (w : Fin nI → WeylGroup τ) (t : Fin τ.rank → kˣ) (e : Fin (∑ l, (m l + m l)) → k),
      (modGLPoint τ k).symm (toConv ((torusAffinePoint t e).comp
          (toralCoverCo τ k α v j fun l => ω (κ l) (w l)))) =
        toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t
          (fun l p => e (finSigmaFinEquiv ⟨l, Fin.castAdd (m l) p⟩))
          (fun l p => e (finSigmaFinEquiv ⟨l, Fin.natAdd (m l) p⟩))) ∧
    Finite ((l : Fin nI) → componentWeylGroup (componentRoots χ (κ l))) ∧
    (∀ w : Fin nI → WeylGroup τ,
      (∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l))) →
      ∀ t c d, toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d ∈
        torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) ∧
    (∀ g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ),
      ∃ w : Fin nI → WeylGroup τ,
        (∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l))) ∧
        ∃ t c d, toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d = g) ∧
    transportPoints (modGLPoint τ k)
        ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) : Subgroup (ModGL τ k)) :
          Set (ModGL τ k)) =
      (⋃ w : (l : Fin nI) → componentWeylGroup (componentRoots χ (κ l)),
        Set.range fun z : TorusAffine k τ.rank (∑ l, (m l + m l)) →ₐ[k] k =>
          z.comp (toralCoverCo τ k α v j fun l => ω (κ l) (w l))) ∧
    (∀ w : Fin nI → WeylGroup τ,
      (∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l))) →
      ∀ t c d, toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d ∈
        bruhatCell τ k (List.ofFn w).prod) ∧
    Subgroup.closure (rootReflection '' kernelRoots χ) =
      ⨆ i, componentWeylGroup (componentRoots χ i) ∧
    (∀ i i' : KernelComponent χ, i ≠ i' →
      ∀ x ∈ componentWeylGroup (componentRoots χ i),
        ∀ y ∈ componentWeylGroup (componentRoots χ i'), Commute x y) ∧
    (∀ g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ),
      ∃ w ∈ Subgroup.closure (rootReflection '' kernelRoots χ),
        g ∈ bruhatCell τ k w) ∧
    IsPointIrreducible k (transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) : Subgroup (ModGL τ k)) :
        Set (ModGL τ k))) ∧
    IsPointConstructible k (transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) : Subgroup (ModGL τ k)) :
        Set (ModGL τ k))) := by
  have hpoint := fun (w : Fin nI → WeylGroup τ) (t : Fin τ.rank → kˣ)
    (e : Fin (∑ l, (m l + m l)) → k) => point_toralCoverCo (k := k) α v j
      (fun l => ω (κ l) (w l)) t e
  have hcover := fun {g : ModGL τ k}
    (hg : g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) =>
    exists_toralCoverElt_eq (κ := κ) hvj hω hαr hκ hα hg
  have hbruhat := fun (w : Fin nI → WeylGroup τ)
    (hw : ∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l)))
    (t : Fin τ.rank → kˣ) (c d : (l : Fin nI) → Fin (m l) → k) =>
    toralCoverElt_mem_bruhatCell (k := k) hvj hω hαr hκ.1 hw t c d
  have hunion : transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) : Subgroup (ModGL τ k)) :
        Set (ModGL τ k)) =
      ⋃ w : (l : Fin nI) → componentWeylGroup (componentRoots χ (κ l)),
        Set.range fun z : TorusAffine k τ.rank (∑ l, (m l + m l)) →ₐ[k] k =>
          z.comp (toralCoverCo τ k α v j fun l => ω (κ l) (w l)) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨w, hw, t, c, d, rfl⟩ := hcover hg
      let F : ((l : Fin nI) × Fin (m l + m l)) → k := fun x => Fin.append (c x.1) (d x.1) x.2
      let e : Fin (∑ l, (m l + m l)) → k := fun n => F (finSigmaFinEquiv.symm n)
      have he : ∀ x, e (finSigmaFinEquiv x) = F x := fun x =>
        congrArg F (finSigmaFinEquiv.symm_apply_apply x)
      refine ⟨fun l => ⟨w l, hw l⟩, torusAffinePoint t e, ?_⟩
      refine (eq_ofConv_of_symm_eq (hpoint w t e)).trans ?_
      simp only [he, F, Fin.append_left, Fin.append_right]
    · rintro ⟨w, z, rfl⟩
      obtain ⟨⟨t, e⟩, rfl⟩ := torusAffinePointEquiv.surjective z
      rw [torusAffinePointEquiv_apply]
      refine ⟨_, toralCoverElt_mem hvj hω hαr (fun l => (w l).2) t
        (fun l p => e (finSigmaFinEquiv ⟨l, Fin.castAdd (m l) p⟩))
        (fun l p => e (finSigmaFinEquiv ⟨l, Fin.natAdd (m l) p⟩)), ?_⟩
      exact (eq_ofConv_of_symm_eq (hpoint (fun l => (w l : WeylGroup τ)) t e)).symm
  refine ⟨hpoint, inferInstance, fun w hw t c d => toralCoverElt_mem hvj hω hαr hw t c d,
    fun g hg => hcover hg, hunion, hbruhat, closure_rootReflection_kernelRoots,
    fun i i' h x hx y hy => commute_of_mem_componentWeylGroup h hx hy, fun g hg => ?_,
    isPointIrreducible_torusGroup_sup_rootSpan fun β h => h.1, ?_⟩
  · obtain ⟨w, hw, t, c, d, rfl⟩ := hcover hg
    refine ⟨(List.ofFn w).prod, ?_, hbruhat w hw t c d⟩
    rw [closure_rootReflection_kernelRoots]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
    exact Subgroup.mem_iSup_of_mem (κ l) (hw l)
  · have h := isPointConstructible_iUnion_range (k := k) (A := GLCoord k (Label τ))
      (J := (l : Fin nI) → componentWeylGroup (componentRoots χ (κ l)))
      (fun _ => TorusAffine k τ.rank (∑ l, (m l + m l)))
      fun w => toralCoverCo τ k α v j fun l => ω (κ l) (w l)
    convert h using 1

section Connected


theorem isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots [IsAlgClosed k] {M : Type}
    [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    IsConnectedAlgebraicSubgroup k
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map (modGLPoint τ k).toMonoidHom) := by
  obtain ⟨nI, κ, m, α, v, j, ω, hκ, hα, hαr, hvj, hω⟩ := exists_toralCoverData χ
  obtain ⟨-, -, -, -, -, -, -, -, -, hirr, hcons⟩ :=
    toral_root_subgroup_regular_cover_char τ k χ κ hκ α hα hαr v j hvj ω hω
  obtain ⟨-, hM, -⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k)
    (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) hcons hirr
  exact hM

end Connected

end CFSG.HardMathSupport.Timmesfeld.Torality
