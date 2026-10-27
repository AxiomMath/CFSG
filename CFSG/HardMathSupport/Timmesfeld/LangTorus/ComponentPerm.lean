module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem u3perm_componentRoots_smul_of_isCharConj
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ χ' : Multiplicative (Fin τ.rank → ℤ) →* M} {t : WeylGroup τ}
    (h : IsCharConj χ χ' t) (i : KernelComponent χ) :
    ∃ i' : KernelComponent χ',
      componentRoots χ i = (fun α => t⁻¹ • α) '' componentRoots χ' i' := by
  obtain ⟨⟨β, hβ⟩, rfl⟩ := Quotient.exists_rep i
  have htβ : t • β ∈ kernelRoots χ' :=
    (kernelRoots_iff_of_isCharConj h).2 (by rwa [inv_smul_smul])
  refine ⟨⟦⟨t • β, htβ⟩⟧, ?_⟩
  ext α
  constructor
  · rintro ⟨hα, hαi⟩
    have htα : t • α ∈ kernelRoots χ' :=
      (kernelRoots_iff_of_isCharConj h).2 (by rwa [inv_smul_smul])
    refine ⟨t • α, ⟨htα, ?_⟩, inv_smul_smul t α⟩
    rw [mk_eq_mk_iff_of_isCharConj h htα htβ]
    simp only [inv_smul_smul]
    exact hαi
  · rintro ⟨γ, ⟨hγ, hγi⟩, rfl⟩
    have hk := (kernelRoots_iff_of_isCharConj h).1 hγ
    refine ⟨hk, ?_⟩
    have := (mk_eq_mk_iff_of_isCharConj h hγ htβ).1 hγi
    simpa only [inv_smul_smul] using this

private theorem u3perm_exists_not_commute_pinnedX_neg
    {τ : Tag} {K : Type} [Field K]
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ c d : K, pinnedX τ K β c * pinnedX τ K (-β) d ≠
      pinnedX τ K (-β) d * pinnedX τ K β c := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨ε₁, -, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single τ i)
  obtain ⟨ε₂, -, hY⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_neg_single τ i)
  refine ⟨ε₁ * 1, ε₂ * 1, fun h => ?_⟩
  refine not_commute_xUnit_yUnit (τ := τ) (K := K) i ?_
  have e1 := hX 1
  have e2 := hY 1
  rw [pinnedX_single] at e1
  rw [pinnedX_neg_single, smul_neg] at e2
  set n := canonicalRep (coxeterSystem τ) K w
  have h' : (n * xUnit τ K i 1 * n⁻¹) * (n * yUnit τ K i 1 * n⁻¹) =
      (n * yUnit τ K i 1 * n⁻¹) * (n * xUnit τ K i 1 * n⁻¹) := by
    rw [e1, e2]
    exact h
  show xUnit τ K i 1 * yUnit τ K i 1 = yUnit τ K i 1 * xUnit τ K i 1
  calc xUnit τ K i 1 * yUnit τ K i 1
      = n⁻¹ * ((n * xUnit τ K i 1 * n⁻¹) * (n * yUnit τ K i 1 * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * yUnit τ K i 1 * n⁻¹) * (n * xUnit τ K i 1 * n⁻¹)) * n := by rw [h']
    _ = yUnit τ K i 1 * xUnit τ K i 1 := by group

theorem exists_weyl_image_component
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer a) (j : KernelComponent (rootCharHom a)) :
    ∃ j' : KernelComponent (rootCharHom a),
      (fun γ => w • γ) '' componentRoots (rootCharHom a) j = componentRoots (rootCharHom a) j' := by
  have h : IsCharConj (rootCharHom a) (rootCharHom a) w := fun v => by
    have h1 : rootChar a (w • (w⁻¹ • v)) = rootChar a (w⁻¹ • v) := hw (w⁻¹ • v)
    rw [smul_inv_smul] at h1
    exact h1
  obtain ⟨j', hj'⟩ := u3perm_componentRoots_smul_of_isCharConj h j
  refine ⟨j', ?_⟩
  rw [hj', Set.image_image]
  ext x
  simp [smul_inv_smul]

theorem eq_of_rootSpan_componentRoots_eq
    {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {j j' : KernelComponent χ}
    (h : rootSpan τ K (componentRoots χ j) = rootSpan τ K (componentRoots χ j')) : j = j' := by
  by_contra hne
  obtain ⟨a, ha⟩ := Quotient.exists_rep j
  have hγ : (a : Fin τ.rank → ℤ) ∈ componentRoots χ j := ⟨a.2, ha⟩
  have hneg : -(a : Fin τ.rank → ℤ) ∈ componentRoots χ j :=
    (isRootComponent_componentRoots j).neg_mem _ hγ
  have hroot : IsRoot τ (a : Fin τ.rank → ℤ) := isRoot_of_mem_componentRoots hγ
  obtain ⟨c, d, hcd⟩ := u3perm_exists_not_commute_pinnedX_neg (K := K) hroot
  have hx : pinnedX τ K (a : Fin τ.rank → ℤ) c ∈ componentRootSpan K χ j :=
    pinnedX_mem_rootSpan hγ c
  have hy : pinnedX τ K (-(a : Fin τ.rank → ℤ)) d ∈ componentRootSpan K χ j' := by
    change pinnedX τ K (-(a : Fin τ.rank → ℤ)) d ∈ rootSpan τ K (componentRoots χ j')
    rw [← h]
    exact pinnedX_mem_rootSpan hneg d
  exact hcd (commute_of_mem_componentRootSpan hne hx hy).eq

theorem exists_mul_canonicalRep_of_mem_toralCentralizer
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    {y : ModGL τ K} (hy : y ∈ toralCentralizer τ K a) :
    ∃ w ∈ rootCharStabilizer a, ∃ m ∈ toralRootGroup τ K a,
      y = m * canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hyv⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ K a).1 y hy
  refine ⟨w, hw, h * u * (canonicalRep (coxeterSystem τ) K w * v *
    (canonicalRep (coxeterSystem τ) K w)⁻¹), ?_, ?_⟩
  · have hvn : canonicalRep (coxeterSystem τ) K w * v *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ rootSpan τ K (rootCharKernel a) := by
      have hsub : (fun α => w • α) '' (rootCharKernel a ∩ inversionSet w) ⊆
          rootCharKernel a := by
        rintro β ⟨α, hα, rfl⟩
        exact ⟨IsRoot.smul hα.1.1 w, (hw α).trans hα.1.2⟩
      exact (rootSpan_mono hsub)
        (canonicalRep_conj_mem_rootSpan (fun α hα => hα.1.1) hv)
    rw [toralRootGroup]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)))
      (Subgroup.mem_sup_right hvn)
  · rw [hyv]
    group

theorem map_conj_componentRootSpan
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer a) {m : ModGL τ K} (hm : m ∈ toralRootGroup τ K a)
    {j j' : KernelComponent (rootCharHom a)}
    (hjj' : (fun γ => w • γ) '' componentRoots (rootCharHom a) j =
      componentRoots (rootCharHom a) j') :
    (rootSpan τ K (componentRoots (rootCharHom a) j)).map
        (MulAut.conj (m * canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      rootSpan τ K (componentRoots (rootCharHom a) j') := by
  have hroots : ∀ α ∈ componentRoots (rootCharHom a) j, IsRoot τ α :=
    fun α hα => isRoot_of_mem_componentRoots hα
  have h1 : (rootSpan τ K (componentRoots (rootCharHom a) j)).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      rootSpan τ K (componentRoots (rootCharHom a) j') := by
    rw [(canonical_weyl_root_transport τ K).1 w (componentRoots (rootCharHom a) j) hroots,
      hjj']
  have hTnorm : torusGroup τ K ≤ Subgroup.normalizer
      (rootSpan τ K (componentRoots (rootCharHom a) j') : Set (ModGL τ K)) :=
    torusGroup_le_normalizer_rootSpan (fun α hα => isRoot_of_mem_componentRoots hα)
  have hSnorm : rootSpan τ K (rootCharKernel a) ≤ Subgroup.normalizer
      (rootSpan τ K (componentRoots (rootCharHom a) j') : Set (ModGL τ K)) := by
    change rootSpan τ K (kernelRoots (rootCharHom a)) ≤ Subgroup.normalizer
      (rootSpan τ K (componentRoots (rootCharHom a) j') : Set (ModGL τ K))
    rw [← iSup_componentRootSpan K]
    refine iSup_le fun j'' => ?_
    by_cases hjj : j'' = j'
    · subst hjj
      exact Subgroup.le_normalizer
    · exact (componentRootSpan_le_centralizer K hjj).trans (Subgroup.centralizer_le_normalizer _)
  have hmN : m ∈ Subgroup.normalizer
      (rootSpan τ K (componentRoots (rootCharHom a) j') : Set (ModGL τ K)) := by
    rw [toralRootGroup] at hm
    exact (sup_le hTnorm hSnorm) hm
  have h2 : (rootSpan τ K (componentRoots (rootCharHom a) j')).map
      (MulAut.conj m).toMonoidHom = rootSpan τ K (componentRoots (rootCharHom a) j') := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map]
    exact Subgroup.mem_normalizer_iff_conj_image_eq.1 hmN
  rw [show (MulAut.conj (m * canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      (MulAut.conj m).toMonoidHom.comp
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom from by
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    group]
  rw [← Subgroup.map_map, h1, h2]

theorem weyl_image_component_eq_of_cube
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (h3 : ¬ 3 ∣ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    {y : ModGL τ L} (hyM : y ∈ S.D.model) (hy3 : y ^ 3 = 1)
    (hyR : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj y).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {w : WeylGroup τ} (hw : w ∈ rootCharStabilizer a) {m : ModGL τ L}
    (hm : m ∈ toralRootGroup τ L a) (hy : y = m * canonicalRep (coxeterSystem τ) L w) :
    (fun γ => w • γ) '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  classical
  have hwc : ∀ j : KernelComponent (rootCharHom a), ∃ j',
      (fun γ => w • γ) '' componentRoots (rootCharHom a) j = componentRoots (rootCharHom a) j' :=
    fun j => exists_weyl_image_component a hw j
  choose wc hwc_spec using hwc
  have hrc : ∀ j : KernelComponent (rootCharHom a), ∃ j',
      (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) j =
        componentRoots (rootCharHom a) j' :=
    fun j => outer_exists_image_component S hT j
  choose rc hrc_spec using hrc
  have hy_span : ∀ j, (rootSpan τ L (componentRoots (rootCharHom a) j)).map
      (MulAut.conj y).toMonoidHom =
        rootSpan τ L (componentRoots (rootCharHom a) (wc j)) := by
    intro j
    rw [hy]
    exact map_conj_componentRootSpan a hw hm (hwc_spec j)
  have hstep_span : ∀ j, (rootSpan τ L (componentRoots (rootCharHom a) j)).map S.D.step =
      rootSpan τ L (componentRoots (rootCharHom a) (rc j)) := by
    intro j
    rw [map_rootSpan_step S (componentRoots (rootCharHom a) j)
      (fun α hα => isRoot_of_mem_componentRoots hα), hrc_spec j]
  have hyfix : S.D.step y = y := by
    change S.D.n * S.D.Φ y * S.D.n⁻¹ = y
    exact (S.D.mem_model.1 hyM).2
  have hstep_conj : ∀ A : Subgroup (ModGL τ L),
      (A.map (MulAut.conj y).toMonoidHom).map S.D.step =
        (A.map S.D.step).map (MulAut.conj y).toMonoidHom := by
    intro A
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, map_mul, map_inv, hyfix]
  have hB3 : ∀ j, wc (rc j) = rc (wc j) := by
    intro j
    apply eq_of_rootSpan_componentRoots_eq (K := L) (rootCharHom a)
    rw [← hy_span (rc j), ← hstep_span j,
      ← hstep_conj (rootSpan τ L (componentRoots (rootCharHom a) j)), hy_span j,
      hstep_span (wc j)]
  have hconj_mul : ∀ {A : Subgroup (ModGL τ L)} (a b : ModGL τ L),
      (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        A.map (MulAut.conj (a * b)).toMonoidHom := by
    intro A a b
    rw [Subgroup.map_map]
    congr 1
  have hy3' : y * y * y = 1 := by simpa [pow_succ, mul_assoc] using hy3
  have hB4 : ∀ j, wc (wc (wc j)) = j := by
    intro j
    apply eq_of_rootSpan_componentRoots_eq (K := L) (rootCharHom a)
    rw [← hy_span (wc (wc j)), ← hy_span (wc j), ← hy_span j]
    rw [hconj_mul y y, hconj_mul (y * y) y, hy3']
    rw [show (MulAut.conj (1 : ModGL τ L)).toMonoidHom = MonoidHom.id (ModGL τ L) from by
      ext x
      simp [MulAut.conj_apply]]
    exact Subgroup.map_id _
  have hrc_iter : ∀ (j : KernelComponent (rootCharHom a)) (k : ℕ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) j =
        componentRoots (rootCharHom a) ((rc^[k]) j) := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ', Set.image_comp, ih, hrc_spec, Function.iterate_succ_apply']
  have hcomp_sub : ∀ (j : KernelComponent (rootCharHom a)) (k : ℕ),
      componentRoots (rootCharHom a) ((rc^[k]) j) ⊆
        rationalRoots S.ρ (rootCharHom a) j := by
    intro j k γ hγ
    rw [← hrc_iter j k] at hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    exact ⟨k, δ, hδ, rfl⟩
  have hiter_all : ∀ (x : KernelComponent (rootCharHom a)) (k : ℕ),
      wc ((rc^[k]) x) = (rc^[k]) (wc x) := by
    intro x k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hB3, ih]
  set j' : KernelComponent (rootCharHom a) := wc i with hj'
  have hR_le_i : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    change ⁅rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ,
        rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ⁆ ≤
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)
    refine (Subgroup.commutator_le).2 fun g₁ hg₁ g₂ hg₂ => ?_
    have h₁ : g₁ ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
      (Subgroup.mem_inf.1 hg₁).1
    have h₂ : g₂ ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
      (Subgroup.mem_inf.1 hg₂).1
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hmap_span_le : (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).map
      (MulAut.conj y).toMonoidHom ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) j') := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨k, δ, hδ, rfl⟩ := hγ
    have hγk : (S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ ∈
        componentRoots (rootCharHom a) ((rc^[k]) i) := by
      rw [← hrc_iter i k]
      exact ⟨δ, hδ, rfl⟩
    have hle1 : rootSubgroup τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) ≤
        componentRootSpan L (rootCharHom a) ((rc^[k]) i) := by
      have hα := rootSubgroup_le_componentRootSpan L
        (α := (⟨(S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ, hγk.1⟩ : kernelRoots (rootCharHom a)))
      rwa [hγk.2] at hα
    have hle2 : (componentRootSpan L (rootCharHom a) ((rc^[k]) i)).map
        (MulAut.conj y).toMonoidHom ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) j') := by
      rw [show componentRootSpan L (rootCharHom a) ((rc^[k]) i) =
          rootSpan τ L (componentRoots (rootCharHom a) ((rc^[k]) i)) from rfl,
        hy_span ((rc^[k]) i)]
      rw [show wc ((rc^[k]) i) = (rc^[k]) j' from hiter_all i k]
      exact rootSpan_mono (hcomp_sub j' k)
    exact hle1.trans (Subgroup.map_le_iff_le_comap.1 hle2)
  have hR_le_j' : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) j') :=
    calc rationalComponent S.ρ S.Γ (rootCharHom a) i
        = (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj y).toMonoidHom :=
          hyR.symm
      _ ≤ (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).map
            (MulAut.conj y).toMonoidHom := Subgroup.map_mono hR_le_i
      _ ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) j') := hmap_span_le
  have horbit : rationalRoots S.ρ (rootCharHom a) i = rationalRoots S.ρ (rootCharHom a) j' := by
    by_contra hij
    have hcomm : ∀ x y : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        (x : ModGL τ L) * (y : ModGL τ L) = (y : ModGL τ L) * (x : ModGL τ L) := by
      intro x y
      exact (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.commute_rootSpan_rationalRoots
        (fun γ hγ => outer_rho_mem_kernelRoots S hT hγ)
        (fun γ δ => S.frob.iform_eq γ δ) hij (x : ModGL τ L) (hR_le_i x.2) (y : ModGL τ L)
        (hR_le_j' y.2)).eq
    have hcomm_sub : ∀ x y : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i), x * y = y * x :=
      fun x y => Subtype.ext (hcomm x y)
    haveI : IsMulCommutative ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      isMulCommutative_iff.2 hcomm_sub
    have hsing : Subsingleton (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, Subgroup.center_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨x, y, hxy⟩ := hQS.2.2
    exact hxy (Subsingleton.elim (x * y) (y * x))
  obtain ⟨γ₀, hγ₀⟩ := Quotient.exists_rep j'
  have hγ₀mem : (γ₀ : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) j' := ⟨γ₀.2, hγ₀⟩
  have hγ₀rat : (γ₀ : Fin τ.rank → ℤ) ∈ rationalRoots S.ρ (rootCharHom a) i := by
    rw [horbit]
    exact ⟨0, γ₀, hγ₀mem, rfl⟩
  obtain ⟨t, δ, hδ, htγ⟩ := hγ₀rat
  have hγ₀rc : (γ₀ : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) ((rc^[t]) i) := by
    rw [← hrc_iter i t]
    exact ⟨δ, hδ, htγ.symm⟩
  have htj' : j' = (rc^[t]) i := eq_of_mem_componentRoots hγ₀mem hγ₀rc
  have htj'' : wc i = (rc^[t]) i := htj'
  have hwc2 : wc (wc i) = (rc^[2 * t]) i := by
    calc wc (wc i) = wc ((rc^[t]) i) := by rw [htj'']
      _ = (rc^[t]) (wc i) := hiter_all i t
      _ = (rc^[t]) ((rc^[t]) i) := by rw [htj'']
      _ = (rc^[2 * t]) i := by
        rw [← Function.iterate_add_apply, show t + t = 2 * t by ring]
  have hwc3 : wc (wc (wc i)) = (rc^[3 * t]) i := by
    calc wc (wc (wc i)) = wc ((rc^[2 * t]) i) := by rw [hwc2]
      _ = (rc^[2 * t]) (wc i) := hiter_all i (2 * t)
      _ = (rc^[2 * t]) ((rc^[t]) i) := by rw [htj'']
      _ = (rc^[3 * t]) i := by
        rw [← Function.iterate_add_apply, show 2 * t + t = 3 * t by ring]
  have hrc3 : (rc^[3 * t]) i = i := hwc3.symm.trans (hB4 i)
  have hper : (S.ρ : (Fin τ.rank → ℤ) → _)^[3 * t] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    rw [hrc_iter i (3 * t), hrc3]
  set s : ℕ := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hs := outer_componentOrbitLength_spec S hT i
  have hsdvd : s ∣ 3 * t := by
    by_contra hnd
    have hmod : 0 < (3 * t) % s := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
    have hlt : (3 * t) % s < s := Nat.mod_lt _ hs.1
    refine hs.2.2 ((3 * t) % s) hmod hlt ?_
    rw [← iterate_image_period S hs.2.1 (3 * t), hper]
  have hcop : Nat.Coprime 3 s := Nat.prime_three.coprime_iff_not_dvd.2 h3
  have hstdvd : s ∣ t := by
    have h1 : Nat.Coprime s 3 := hcop.symm
    have h2 : s ∣ t * 3 := by rwa [mul_comm] at hsdvd
    exact h1.dvd_of_dvd_mul_right h2
  have htper : (S.ρ : (Fin τ.rank → ℤ) → _)^[t] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    rw [iterate_image_period S hs.2.1 t, Nat.mod_eq_zero_of_dvd hstdvd]
    simp
  have hseteq : componentRoots (rootCharHom a) (wc i) = componentRoots (rootCharHom a) i := by
    rw [htj'', ← hrc_iter i t]
    exact htper
  have hwci : wc i = i :=
    eq_of_rootSpan_componentRoots_eq (K := L) (rootCharHom a) (by rw [hseteq])
  rw [hwc_spec i, hwci]

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end
