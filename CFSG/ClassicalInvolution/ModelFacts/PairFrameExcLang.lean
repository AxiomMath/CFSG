module

public import CFSG.LieType.AlgebraicGroups.ToralCentralizerIdentity
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleLang
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealizationGroups
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups WithConv
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] {M : Type*} [CommGroup M]


variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] {M : Type*} [CommGroup M]

theorem isConnectedAlgebraicSubgroup_torus_sup_rootSpan
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    IsConnectedAlgebraicSubgroup k ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map
      (modGLPoint τ k).toMonoidHom) := by
  classical
  obtain ⟨nI, κ, m, α, v, j, ω, hκ, hα, hαr, hvj, hω⟩ := exists_toralCoverData (τ := τ) χ
  have hpoint := fun (w : Fin nI → WeylGroup τ) (t : Fin τ.rank → kˣ)
    (e : Fin (∑ l, (m l + m l)) → k) => point_toralCoverCo (k := k) α v j
      (fun l => ω (κ l) (w l)) t e
  have hcover := fun {g : ModGL τ k}
    (hg : g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) =>
    exists_toralCoverElt_eq (κ := κ) hvj hω hαr hκ hα hg
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
  have hirr := isPointIrreducible_torusGroup_sup_rootSpan (k := k) (S := kernelRoots χ)
    fun β h => h.1
  have hcons : IsPointConstructible k (transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) : Subgroup (ModGL τ k)) :
        Set (ModGL τ k))) := by
    have h := isPointConstructible_iUnion_range (k := k) (A := GLCoord k (Label τ))
      (J := (l : Fin nI) → componentWeylGroup (componentRoots χ (κ l)))
      (fun _ => TorusAffine k τ.rank (∑ l, (m l + m l)))
      fun w => toralCoverCo τ k α v j fun l => ω (κ l) (w l)
    convert h using 1
  exact (isConnectedAlgebraicSubgroup_map (modGLPoint τ k)
    (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) hcons hirr).2.1

omit [IsAlgClosed k] in
theorem map_entrywiseFrobGL_rootSpan_le (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ)
    (S : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ k S).map (entrywiseFrobGL τ k p e) ≤ rootSpan τ k S := by
  rw [rootSpan, Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hα => ?_
  rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  rw [entrywiseFrobGL_pinnedX]
  exact pinnedX_mem_rootSpan hα _

omit [IsAlgClosed k] in
theorem entrywiseFrobGL_mem_torus_sup_rootSpan (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {g : ModGL τ k}
    (hg : g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) :
    entrywiseFrobGL τ k p e g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
  have hle : (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)).map (entrywiseFrobGL τ k p e) ≤
      torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
    rw [Subgroup.map_sup, sup_le_iff]
    constructor
    · rw [torusGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨⟨i, t⟩, rfl⟩, rfl⟩
      refine Subgroup.mem_sup_left ?_
      change baseChangeGL (iterateFrobenius k p e) (torusElt τ k i t) ∈ _
      rw [baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    · exact (map_entrywiseFrobGL_rootSpan_le p e _).trans le_sup_right
  exact hle (Subgroup.mem_map_of_mem _ hg)

theorem exists_eq_inv_mul_frob_torus_sup_rootSpan (p : ℕ) [Fact p.Prime] [CharP k p] {e : ℕ}
    (he : 1 ≤ e) (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {u : ModGL τ k}
    (hu : u ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) :
    ∃ m ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ), u = m⁻¹ * entrywiseFrobGL τ k p e m := by
  have hM := isConnectedAlgebraicSubgroup_torus_sup_rootSpan (k := k) χ
  obtain ⟨hsm, -, -⟩ := hM.smooth
  obtain ⟨m, hm, h⟩ := exists_eq_inv_mul_frobTwistGL p he (1 : ModGL τ k) hM hsm
    (fun g hg => by
      rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
      exact entrywiseFrobGL_mem_torus_sup_rootSpan p e χ hg) hu
  refine ⟨m, hm, ?_⟩
  rw [h, frobTwistGL_apply, one_mul, inv_one, mul_one]


end CFSG.ClassicalInvolution.ModelFacts.Levi
