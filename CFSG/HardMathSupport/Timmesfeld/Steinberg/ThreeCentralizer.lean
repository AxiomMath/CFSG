module

public import CFSG.LieType.AlgebraicGroups.ToralCentralizerIdentity
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv Topology
  CFSG.LieType.AlgebraicGroups

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

variable {τ : Tag} {k : Type} [Field k]

theorem toral_root_subgroup_regular_cover_gen
    (τ : Tag) (k : Type) [Field k]
    [IsAlgClosed k] (a : Fin τ.rank → kˣ)
    {nI : ℕ} (κ : Fin nI → KernelComponent (rootCharHom a))
    (hκ : Function.Bijective κ) {m : Fin nI → ℕ}
    (α : (l : Fin nI) → Fin (m l) → Fin τ.rank → ℤ) (hα : ∀ l, Function.Injective (α l))
    (hαr : ∀ l, Set.range (α l) = posRoots (componentRoots (rootCharHom a) (κ l)))
    (v : (Fin τ.rank → ℤ) → WeylGroup τ) (j : (Fin τ.rank → ℤ) → Fin τ.rank)
    (hvj : ∀ i, ∀ β ∈ simpleRoots (componentRoots (rootCharHom a) i),
      v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
    (ω : KernelComponent (rootCharHom a) → WeylGroup τ → List (Fin τ.rank → ℤ))
    (hω : ∀ i, ∀ w ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
      IsComponentWord (componentRoots (rootCharHom a) i) (ω i w) ∧
        reflectionWordProd (ω i w) = w) :
    (∀ (w : Fin nI → WeylGroup τ) (t : Fin τ.rank → kˣ) (e : Fin (∑ l, (m l + m l)) → k),
      (modGLPoint τ k).symm (toConv ((torusAffinePoint t e).comp
          (toralCoverCo τ k α v j fun l => ω (κ l) (w l)))) =
        toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t
          (fun l p => e (finSigmaFinEquiv ⟨l, Fin.castAdd (m l) p⟩))
          (fun l p => e (finSigmaFinEquiv ⟨l, Fin.natAdd (m l) p⟩))) ∧
    Finite ((l : Fin nI) → componentWeylGroup (componentRoots (rootCharHom a) (κ l))) ∧
    (∀ w : Fin nI → WeylGroup τ,
      (∀ l, w l ∈ componentWeylGroup (componentRoots (rootCharHom a) (κ l))) →
      ∀ t c d, toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d ∈
        torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a))) ∧
    (∀ g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a)),
      ∃ w : Fin nI → WeylGroup τ,
        (∀ l, w l ∈ componentWeylGroup (componentRoots (rootCharHom a) (κ l))) ∧
        ∃ t c d, toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d = g) ∧
    transportPoints (modGLPoint τ k)
        ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a)) : Subgroup (ModGL τ k)) :
          Set (ModGL τ k)) =
      (⋃ w : (l : Fin nI) → componentWeylGroup (componentRoots (rootCharHom a) (κ l)),
        Set.range fun z : TorusAffine k τ.rank (∑ l, (m l + m l)) →ₐ[k] k =>
          z.comp (toralCoverCo τ k α v j fun l => ω (κ l) (w l))) ∧
    (∀ w : Fin nI → WeylGroup τ,
      (∀ l, w l ∈ componentWeylGroup (componentRoots (rootCharHom a) (κ l))) →
      ∀ t c d, toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d ∈
        bruhatCell τ k (List.ofFn w).prod) ∧
    Subgroup.closure (rootReflection '' kernelRoots (rootCharHom a)) =
      ⨆ i, componentWeylGroup (componentRoots (rootCharHom a) i) ∧
    (∀ i i' : KernelComponent (rootCharHom a), i ≠ i' →
      ∀ x ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
        ∀ y ∈ componentWeylGroup (componentRoots (rootCharHom a) i'), Commute x y) ∧
    (∀ g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a)),
      ∃ w ∈ Subgroup.closure (rootReflection '' kernelRoots (rootCharHom a)),
        g ∈ bruhatCell τ k w) ∧
    IsPointIrreducible k (transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a)) : Subgroup (ModGL τ k)) :
        Set (ModGL τ k))) ∧
    IsPointConstructible k (transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a)) : Subgroup (ModGL τ k)) :
        Set (ModGL τ k))) := by
  have hpoint := fun (w : Fin nI → WeylGroup τ) (t : Fin τ.rank → kˣ)
    (e : Fin (∑ l, (m l + m l)) → k) => point_toralCoverCo (k := k) α v j
      (fun l => ω (κ l) (w l)) t e
  have hcover := fun {g : ModGL τ k}
    (hg : g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a))) =>
    exists_toralCoverElt_eq (κ := κ) hvj hω hαr hκ hα hg
  have hbruhat := fun (w : Fin nI → WeylGroup τ)
    (hw : ∀ l, w l ∈ componentWeylGroup (componentRoots (rootCharHom a) (κ l)))
    (t : Fin τ.rank → kˣ) (c d : (l : Fin nI) → Fin (m l) → k) =>
    toralCoverElt_mem_bruhatCell (k := k) hvj hω hαr hκ.1 hw t c d
  have hunion : transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k (kernelRoots (rootCharHom a)) : Subgroup (ModGL τ k)) :
        Set (ModGL τ k)) =
      ⋃ w : (l : Fin nI) → componentWeylGroup (componentRoots (rootCharHom a) (κ l)),
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
      (J := (l : Fin nI) → componentWeylGroup (componentRoots (rootCharHom a) (κ l)))
      (fun _ => TorusAffine k τ.rank (∑ l, (m l + m l)))
      fun w => toralCoverCo τ k α v j fun l => ω (κ l) (w l)
    convert h using 1


section Connected


theorem mem_kernelReflectionGroup_of_canonicalRep_mem_gen [IsAlgClosed k]
    {a : Fin τ.rank → kˣ} {w : WeylGroup τ}
    (hw : canonicalRep (coxeterSystem τ) k w ∈ toralRootGroup τ k a) :
    w ∈ kernelReflectionGroup a := by
  obtain ⟨nI, κ, m, α, v, j, ω, hκ, hα, hαr, hvj, hω⟩ := exists_toralCoverData (rootCharHom a)
  obtain ⟨-, -, -, -, -, -, -, -, hidx, -, -⟩ :=
    toral_root_subgroup_regular_cover_gen τ k a κ hκ α hα hαr v j hvj ω hω
  obtain ⟨u, hu, hnu⟩ := hidx _ hw
  have huw : u = w := by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_bruhatCell hne) hnu (canonicalRep_mem_bruhatCell w)
  rw [kernelReflectionGroup_eq_kernelWeylGroup_rootCharHom, kernelWeylGroup_eq_closure, ← huw]
  exact hu

theorem toral_centralizer_connected_of_stabilizer_le [IsAlgClosed k] (a : Fin τ.rank → kˣ)
    (hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    toralCentralizer τ k a = toralRootGroup τ k a ∧
      IsConnectedAlgebraicSubgroup k (toralCentralizerPointSubgroup τ k a) := by
  have hZM : toralCentralizer τ k a = toralRootGroup τ k a :=
    toralCentralizer_eq_toralRootGroup_of_stabilizer_le τ k a hW
  refine ⟨hZM, ?_⟩
  obtain ⟨nI, κ, m, α, v, j, ω, hκ, hα, hαr, hvj, hω⟩ := exists_toralCoverData (rootCharHom a)
  obtain ⟨-, -, -, -, -, -, -, -, -, hirr, hcons⟩ :=
    toral_root_subgroup_regular_cover_gen τ k a κ hκ α hα hαr v j hvj ω hω
  obtain ⟨-, hM, -⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k)
    (toralRootGroup τ k a) hcons hirr
  rw [toralCentralizerPointSubgroup, hZM]
  exact hM

end Connected


section Lang

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem entrywiseFrobGL_rootDiagUnit_pow (e : ℕ) (a : Fin τ.rank → kˣ) :
    entrywiseFrobGL τ k p e (rootDiagUnit τ a) = rootDiagUnit τ a ^ p ^ e := by
  rw [show rootDiagUnit τ a ^ p ^ e = rootDiagUnitHom τ k (a ^ p ^ e) from
    ((rootDiagUnitHom τ k).map_pow a (p ^ e)).symm]
  apply Units.ext
  change entrywise (iterateFrobenius k p e) (rootDiag a) = rootDiag (a ^ p ^ e)
  rw [entrywise_rootDiag]
  congr 1

theorem exists_pow_eq_self {G : Type*} [Group G] {d : G} (hd : d ^ 3 = 1) {t : ℕ}
    (ht : ¬ 3 ∣ t) : ∃ u : ℕ, (d ^ t) ^ u = d := by
  have h3 : ∀ n : ℕ, d ^ (3 * n) = 1 := fun n => by rw [pow_mul, hd, one_pow]
  have hmod : t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hmod with h | h
  · refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ : ∃ m, t = 3 * m + 1 := ⟨t / 3, by omega⟩
    rw [pow_one, hm, pow_add, h3, one_mul, pow_one]
  · refine ⟨2, ?_⟩
    obtain ⟨m, hm⟩ : ∃ m, t = 3 * m + 2 := ⟨t / 3, by omega⟩
    rw [← pow_mul, hm]
    have : (3 * m + 2) * 2 = 3 * (2 * m + 1) + 1 := by ring
    rw [this, pow_add, h3, one_mul, pow_one]

variable [IsAlgClosed k]

theorem toral_centralizer_Lang_of_cube (hp3 : p ≠ 3) (a : Fin τ.rank → kˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (e : ℕ) (he : 1 ≤ e) {Q : ModGL τ k} (hQG : Q ∈ adjointGroup τ k) {s : ℕ} (hs : ¬ 3 ∣ s)
    (hQ : Q * rootDiagUnit τ a * Q⁻¹ = rootDiagUnit τ a ^ s) :
    ∀ c ∈ toralCentralizer τ k a, ∃ z ∈ toralCentralizer τ k a,
      z⁻¹ * frobTwistGL τ k p e Q z = c := by
  obtain ⟨-, hZ⟩ := toral_centralizer_connected_of_stabilizer_le a hW
  have hd3 : rootDiagUnit τ a ^ 3 = 1 := by
    have h1 : a ^ 3 = 1 := funext fun i => by simpa using ha3 i
    have := (rootDiagUnitHom τ k).map_pow a 3
    rw [h1, map_one] at this
    exact this.symm
  have hQ' : ∀ g ∈ toralCentralizer τ k a, frobTwistGL τ k p e Q g ∈ toralCentralizer τ k a := by
    intro g hg
    obtain ⟨hgG, hgc⟩ := mem_toralCentralizer.1 hg
    refine mem_toralCentralizer.2 ⟨?_, ?_⟩
    · rw [frobTwistGL_apply]
      exact mul_mem (mul_mem hQG (entrywiseFrobGL_mem p e hgG)) (inv_mem hQG)
    · set d := rootDiagUnit τ a with hd
      have hcg : Commute g d := by
        have := hgc
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      have h1 : Commute (entrywiseFrobGL τ k p e g) (d ^ p ^ e) := by
        rw [← entrywiseFrobGL_rootDiagUnit_pow p e a]
        exact hcg.map _
      have h2 : Commute (Q * entrywiseFrobGL τ k p e g * Q⁻¹) (Q * d ^ p ^ e * Q⁻¹) :=
        h1.map (MulAut.conj Q).toMonoidHom
      have h3 : Q * d ^ p ^ e * Q⁻¹ = d ^ (s * p ^ e) := by
        rw [← conj_pow, hQ, ← pow_mul]
      rw [h3] at h2
      have hnd : ¬ 3 ∣ s * p ^ e := by
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
        · exact hs h
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out)).1
            (Nat.prime_three.dvd_of_dvd_pow h)).symm
      obtain ⟨u, hu⟩ := exists_pow_eq_self hd3 hnd
      have h4 : Commute (Q * entrywiseFrobGL τ k p e g * Q⁻¹) d := by
        rw [← hu]
        exact h2.pow_right u
      rw [frobTwistGL_apply, mul_inv_eq_iff_eq_mul]
      exact h4.symm.eq
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ he Q hQ'
  exact hlang

end Lang

end CFSG.HardMathSupport.Timmesfeld.Steinberg
