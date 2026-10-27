module

public import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity
public import CFSG.LieType.Chevalley.GraphFixedParabolicSelfCentralizing
public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section RootSpans

variable {τ : Tag} {K : Type} [Field K]

theorem rootSpan_inf_rootSpan_eq_bot
    {S T : Set (Fin τ.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β)
    (hSc : ∀ β ∈ S, ∀ γ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ S)
    (hT : ∀ β ∈ T, IsRoot τ β ∧ 0 < height β)
    (hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T)
    (hST : Disjoint S T) : rootSpan τ K S ⊓ rootSpan τ K T = ⊥ := by
  classical
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxS, hxT⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨k, γ₁, hγ₁⟩ := ((finite_setOf_isRoot τ).subset fun β hβ => (hS β hβ).1).fin_embedding
  obtain ⟨l, γ₂, hγ₂⟩ := ((finite_setOf_isRoot τ).subset fun β hβ => (hT β hβ).1).fin_embedding
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hS hSc γ₁ γ₁.injective hγ₁).surjOn hxS
  obtain ⟨e, -, he⟩ := (bijOn_prod_pinnedX K hT hTc γ₂ γ₂.injective hγ₂).surjOn hxT
  have hd' : (List.ofFn fun i => pinnedX τ K (γ₁ i) (d i)).prod = x := hd
  have he' : (List.ofFn fun i => pinnedX τ K (γ₂ i) (e i)).prod = x := he
  have hinj : Function.Injective (Fin.append γ₁ γ₂) :=
    Fin.append_injective_iff.2 ⟨γ₁.injective, γ₂.injective, fun i j hij =>
      hST.ne_of_mem (hγ₁ ▸ Set.mem_range_self i) (hγ₂ ▸ Set.mem_range_self j) hij⟩
  have hpos : ∀ i, IsRoot τ (Fin.append γ₁ γ₂ i) ∧ 0 < height (Fin.append γ₁ γ₂ i) := by
    intro i
    induction i using Fin.addCases with
    | left j =>
      rw [Fin.append_left]
      exact hS _ (hγ₁ ▸ Set.mem_range_self j)
    | right j =>
      rw [Fin.append_right]
      exact hT _ (hγ₂ ▸ Set.mem_range_self j)
  have hsplit : ∀ (d₁ : Fin k → K) (d₂ : Fin l → K),
      (List.ofFn fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append d₁ d₂ i)).prod =
        (List.ofFn fun i => pinnedX τ K (γ₁ i) (d₁ i)).prod *
          (List.ofFn fun i => pinnedX τ K (γ₂ i) (d₂ i)).prod := by
    intro d₁ d₂
    have e : (fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append d₁ d₂ i)) =
        Fin.append (fun i => pinnedX τ K (γ₁ i) (d₁ i)) (fun i => pinnedX τ K (γ₂ i) (d₂ i)) := by
      funext i
      induction i using Fin.addCases with
      | left j => rw [Fin.append_left, Fin.append_left, Fin.append_left]
      | right j => rw [Fin.append_right, Fin.append_right, Fin.append_right]
    rw [e, List.ofFn_fin_append, List.prod_append]
  have hone : ∀ {m : ℕ} (γ : Fin m → Fin τ.rank → ℤ),
      (List.ofFn fun i => pinnedX τ K (γ i) ((0 : Fin m → K) i)).prod = 1 := by
    intro m γ
    simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 : (List.ofFn fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append d 0 i)).prod = x := by
    rw [hsplit, hone, mul_one, hd']
  have h2 : (List.ofFn fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append 0 e i)).prod = x := by
    rw [hsplit, hone, one_mul, he']
  have hde := (positive_root_product_injectivity τ K _ hinj hpos).2 (h1.trans h2.symm)
  have hd0 : d = 0 := funext fun i => by
    have := congrFun hde (Fin.castAdd l i)
    simpa only [Fin.append_left] using this
  rw [Subgroup.mem_bot, ← hd', hd0, hone]

theorem eq_of_conj_eq_of_mem_rootSpan
    {O : Set (Fin τ.rank → ℤ)} {s : ℤ}
    (hO : ∀ γ ∈ O, IsRoot τ γ ∧ height γ = s) (hs : 0 < s)
    (hnr : ∀ γ ∈ O, ∀ γ' ∈ O, ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → ¬IsRoot τ (p • γ + q • γ'))
    {u y z : ModGL τ K} (hu : u ∈ posUnipotent τ K) (hy : y ∈ rootSpan τ K O)
    (hz : z ∈ rootSpan τ K O) (h : u * y * u⁻¹ = z) : y = z := by
  have hOpos : ∀ γ ∈ O, IsRoot τ γ ∧ 0 < height γ := fun γ hγ =>
    ⟨(hO γ hγ).1, by rw [(hO γ hγ).2]; exact hs⟩
  have hOc : ∀ β ∈ O, ∀ γ ∈ O, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ O := fun β hβ γ hγ a b ha hb hr => absurd hr (hnr β hβ γ hγ a b ha hb)
  have hTpos : ∀ β ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β ∧ 1 + s ≤ height β},
      IsRoot τ β ∧ 0 < height β := fun β hβ => ⟨hβ.1, hβ.2.1⟩
  have hTc : ∀ β ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β ∧ 1 + s ≤ height β},
      ∀ γ ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β ∧ 1 + s ≤ height β},
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β ∧ 1 + s ≤ height β} := by
    intro β hβ γ hγ a b ha hb hr
    have h' := nsmul_add_nsmul_mem_heightSet (h := 0) (k := 1 + s) ⟨hβ.2.1, hβ.2.1.le⟩
      ⟨hγ.2.1, hγ.2.2⟩ ha hb hr
    exact ⟨h'.1, h'.2.1, by have := h'.2.2; omega⟩
  have hdisj : Disjoint O {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β ∧ 1 + s ≤ height β} :=
    Set.disjoint_left.2 fun γ hγO hγT => by
      have h1 := hγT.2.2
      rw [(hO γ hγO).2] at h1
      omega
  have hbot := rootSpan_inf_rootSpan_eq_bot (K := K) hOpos hOc hTpos hTc hdisj
  have hsub : O ⊆ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β ∧ s ≤ height β} :=
    fun γ hγ => ⟨(hO γ hγ).1, (hOpos γ hγ).2, (hO γ hγ).2.ge⟩
  have hyU : y ∈ heightSeries τ K s := rootSpan_mono hsub hy
  have hu1 : u ∈ heightSeries τ K 1 := by
    rw [heightSeries_one]
    exact hu
  have hcomm := commutator_heightSeries_le K 1 s (Subgroup.commutator_mem_commutator hu1 hyU)
  have hzy : z * y⁻¹ = ⁅u, y⁆ := by rw [commutatorElement_def, ← h]
  have hmem : z * y⁻¹ ∈ rootSpan τ K O ⊓
      rootSpan τ K {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β ∧ 1 + s ≤ height β} :=
    Subgroup.mem_inf.2 ⟨mul_mem hz (inv_mem hy), by rw [hzy]; exact hcomm⟩
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem.symm

end RootSpans

variable {t : TwistTag} {K : Type} [Field K]

theorem not_isRoot_nsmul_add_nsmul_of_mem_orbitImage
    (w : WeylGroup t.tag)
    (a : Fin t.foldedTag.rank) {γ γ' : Fin t.tag.rank → ℤ}
    (hγ : γ ∈ (t.orbit a).image fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ))
    (hγ' : γ' ∈ (t.orbit a).image fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ))
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) : ¬IsRoot t.tag (p • γ + q • γ') := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hγ
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ'
  by_cases hij : i = j
  · subst hij
    intro h
    have h1 := iform_self_bounds_of_isRoot h
    have h2 := iform_self_bounds_of_isRoot (IsRoot.smul (isRoot_single t.tag i) w)
    rw [CFSG.LieType.Steinberg.Adjoint.iform_nsmul_add_nsmul] at h1
    have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
    have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
    have hsum : (4 : ℤ) ≤ (p : ℤ) ^ 2 + 2 * p * q + (q : ℤ) ^ 2 := by nlinarith
    have hI : (0 : ℤ) ≤ CFSG.LieType.Steinberg.Adjoint.iform
        (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) (w • Pi.single i 1) := by linarith [h2.1]
    nlinarith [mul_le_mul_of_nonneg_right hsum hI, h1.2, h2.1]
  · rw [← smul_nsmul_add_nsmul, isRoot_smul_iff]
    exact not_isRoot_nsmul_single_add_nsmul_single hij (t.cartan_eq_zero_of_mem_orbit hi hj hij)
      hp hq

theorem height_eq_of_mem_orbitImage
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {a : Fin t.foldedTag.rank} {i : Fin t.tag.rank} (hi : i ∈ t.orbit a) {γ : Fin t.tag.rank → ℤ}
    (hγ : γ ∈ (t.orbit a).image fun j => w • (Pi.single j 1 : Fin t.tag.rank → ℤ)) :
    height γ = height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) := by
  have hγ' : γ ∈ t.diagramOrbit (w • Pi.single i 1) := by
    rw [t.diagramOrbit_smul_single hw i, (t.mem_orbit_iff).1 hi]
    exact hγ
  exact t.height_of_mem_diagramOrbit hγ'

theorem exists_orbit_card_eq_order
    {J : Set (Fin t.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    ∃ w ∈ relWeylTwist t, ∃ a, (t.orbit a).card = t.order ∧ ∀ i ∈ t.orbit a,
      w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈ parabolicRadicalRoots t.tag (t.orbitUnion J) := by
  have hAne := orbitUnion_ne_univ (t := t) hJ
  obtain ⟨-, hspan, -, -⟩ := parabolic_radical_roots_span_lattice t.tag hAne
  have hmoved : ∃ α ∈ parabolicRadicalRoots t.tag (t.orbitUnion J), permLattice t.perm α ≠ α := by
    by_contra hcon
    push Not at hcon
    let M : Submodule ℤ (Fin t.tag.rank → ℤ) :=
      { carrier := {v | permLattice t.perm v = v}
        add_mem' := fun {u v} hu hv => by
          change permLattice t.perm (u + v) = u + v
          rw [permLattice_add, show permLattice t.perm u = u from hu,
            show permLattice t.perm v = v from hv]
        zero_mem' := rfl
        smul_mem' := fun c v hv => by
          change permLattice t.perm (c • v) = c • v
          have hv' : permLattice t.perm v = v := hv
          have e : permLattice t.perm (c • v) = c • permLattice t.perm v := rfl
          rw [e, hv'] }
    have hle : Submodule.span ℤ (parabolicRadicalRoots t.tag (t.orbitUnion J)) ≤ M :=
      Submodule.span_le.2 hcon
    rw [hspan] at hle
    have hperm : t.perm = 1 := Equiv.ext fun i => by
      have h1 : permLattice t.perm (Pi.single i 1) = Pi.single i 1 :=
        hle (Submodule.mem_top (x := Pi.single i 1))
      rw [permLattice_single] at h1
      exact t.single_one_injective h1
    have hne : t.perm ≠ 1 := by cases t <;> decide
    exact hne hperm
  obtain ⟨α, hα, hρα⟩ := hmoved
  obtain ⟨w, hw, a, hOα⟩ := t.exists_diagramOrbit_eq hα.1.1
  refine ⟨w, hw, a, ?_, fun i hi => ?_⟩
  · rcases t.card_orbit a with h1 | h1
    · exfalso
      have hcard : (t.diagramOrbit α).card = 1 := by rw [hOα, t.card_image_smul_single, h1]
      have hmem1 := t.self_mem_diagramOrbit α
      have hmem2 : permLattice t.perm α ∈ t.diagramOrbit α :=
        t.mem_diagramOrbit.2 ⟨t.perm, Subgroup.mem_zpowers _, rfl⟩
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
      rw [hx] at hmem1 hmem2
      exact hρα ((Finset.mem_singleton.1 hmem2).trans (Finset.mem_singleton.1 hmem1).symm)
    · exact h1
  · refine diagramOrbit_subset (fun β hβ => permLattice_mem_parabolicRadicalRoots hβ) hα ?_
    rw [hOα]
    exact Finset.mem_image_of_mem _ hi

theorem units_map_entrywiseHom_coe_orbitX
    {σ : K →+* K} {δ : K ≃+* K}
    (hδ : ∀ c, δ (σ c) = σ (δ c)) (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    Units.map (entrywiseHom δ.toRingHom) (orbitX t K σ a c : ModGL t.tag K) =
      orbitX t K σ a ⟨δ c, map_mem_orbitField hδ c.2⟩ := by
  have hpow : ∀ (n : ℕ) (x : K), δ ((σ ^ n) x) = (σ ^ n) (δ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', RingHom.coe_mul, Function.comp_apply, Function.comp_apply, hδ, ih]
  rw [coe_orbitX, coe_orbitX, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  rw [Function.comp_apply, units_map_entrywiseHom_xUnit]
  exact congrArg _ (hpow k c)

theorem units_map_entrywiseHom_conj_orbitX
    {σ : K →+* K} {δ : K ≃+* K}
    (hδ : ∀ c, δ (σ c) = σ (δ c)) (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank)
    (c : orbitField t K σ a) :
    Units.map (entrywiseHom δ.toRingHom) (canonicalRep (coxeterSystem t.tag) K w *
        (orbitX t K σ a c : ModGL t.tag K) * (canonicalRep (coxeterSystem t.tag) K w)⁻¹) =
      canonicalRep (coxeterSystem t.tag) K w *
        (orbitX t K σ a ⟨δ c, map_mem_orbitField hδ c.2⟩ : ModGL t.tag K) *
          (canonicalRep (coxeterSystem t.tag) K w)⁻¹ := by
  rw [map_mul, map_mul, map_inv, entrywise_canonicalRep δ w, units_map_entrywiseHom_coe_orbitX hδ]

theorem conj_orbitX_mem
    {σ : K →+* K} {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    canonicalRep (coxeterSystem t.tag) K w * (orbitX t K σ a c : ModGL t.tag K) *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
      rootSpan t.tag K ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ := by
  have := (orbitConjEquiv t σ a hw (Multiplicative.ofAdd c)).2
  rwa [coe_orbitConjEquiv] at this

section Diag

variable {σ : K →+* K} {b : Fin t.tag.rank → Kˣ} {δ : K ≃+* K}

theorem diagFieldAut_toMonoidHom (b : Fin t.tag.rank → Kˣ) (δ : K ≃+* K) :
    (diagFieldAut t.tag b δ).toMonoidHom =
      (MulAut.conj (rootDiagUnit t.tag b)).toMonoidHom.comp
        (Units.map (entrywiseHom δ.toRingHom)) :=
  MonoidHom.ext fun _ => rfl

theorem map_diagFieldAut_twistedFixedGroup
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    (twistedFixedGroup t K σ).map (diagFieldAut t.tag b δ).toMonoidHom =
      twistedFixedGroup t K σ := by
  rw [diagFieldAut_toMonoidHom, ← Subgroup.map_map,
    map_units_map_entrywiseHom_twistedFixedGroup hδ,
    map_conj_eq_of_mem_normalizer (rootDiagUnit_mem_normalizer_twistedFixedGroup hb)]

theorem map_diagFieldAut_rootSpan_inf
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) (hδ : ∀ c, δ (σ c) = σ (δ c))
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot t.tag γ) :
    (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ).map (diagFieldAut t.tag b δ).toMonoidHom =
      rootSpan t.tag K S ⊓ twistedFixedGroup t K σ := by
  rw [Subgroup.map_inf_eq _ _ _ (diagFieldAut t.tag b δ).injective,
    map_diagFieldAut_rootSpan b δ hS, map_diagFieldAut_twistedFixedGroup hb hδ]

theorem map_diagFieldAut_graphFixedRootGroup
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    (graphFixedRootGroup t K σ).map (diagFieldAut t.tag b δ).toMonoidHom =
      graphFixedRootGroup t K σ := by
  rw [diagFieldAut_toMonoidHom, ← Subgroup.map_map,
    map_units_map_entrywiseHom_graphFixedRootGroup hδ, map_conj_rootDiagUnit_graphFixedRootGroup hb]

theorem exists_mulAut_graphFixedRootGroup
    {g : ModGL t.tag K}
    (hg : g ∈ graphFixedRootGroup t K σ)
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    ∃ α : MulAut (graphFixedRootGroup t K σ), ∀ x : graphFixedRootGroup t K σ,
      (α x : ModGL t.tag K) = g * rootDiagUnit t.tag b * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit t.tag b)⁻¹ * g⁻¹ := by
  set e : MulAut (ModGL t.tag K) := MulAut.conj g * diagFieldAut t.tag b δ with he
  have hmap : (graphFixedRootGroup t K σ).map e.toMonoidHom = graphFixedRootGroup t K σ := by
    have e' : e.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (diagFieldAut t.tag b δ).toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [e', ← Subgroup.map_map, map_diagFieldAut_graphFixedRootGroup hb hδ,
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)]
  refine ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap), fun x => ?_⟩
  change e x = _
  rw [he, MulAut.mul_apply, MulAut.conj_apply, diagFieldAut_apply]
  group

end Diag

theorem mem_borelGroup_of_normalizes_graphFixed
    (σ : K ≃+* K) {J : Set (Fin t.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {g : ModGL t.tag K} (hgP : g ∈ graphFixedParabolic t K σ.toRingHom J)
    (hgN : ∀ h : ℤ, ∀ x ∈ graphFixedParabolicRadicalGe t K σ.toRingHom J h,
      g * x * g⁻¹ ∈ graphFixedParabolicRadicalGe t K σ.toRingHom J h) :
    g ∈ borelGroup t.tag K := by
  classical
  have hAne := orbitUnion_ne_univ (t := t) hJ
  have hgΓ : g ∈ twistedFixedGroup t K σ.toRingHom :=
    graphFixedRootGroup_le t K _ (graphFixedParabolic_le t K _ J hgP)
  have hgP' : g ∈ (graphFixedParabolic t K σ.toRingHom J : Set (ModGL t.tag K)) := hgP
  rw [(fixed_standard_parabolic_cells t K σ).1 J] at hgP'
  obtain ⟨⟨w, hwJ⟩, hgw⟩ := Set.mem_iUnion.1 hgP'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hgw
  have hw : w ∈ parabolicWeylGroup t.tag (t.orbitUnion J) ⊓ relWeylTwist t := by
    rw [parabolicWeylGroup_inf_relWeylTwist]
    exact hwJ
  obtain ⟨hwA, hwρ⟩ := Subgroup.mem_inf.1 hw
  set n := canonicalRep (coxeterSystem t.tag) K w with hn
  obtain ⟨-, -, hbij, -⟩ := parabolic_radical_roots_span_lattice t.tag hAne
  have hbB : b ∈ borelGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1
  have hbΓ : b ∈ twistedFixedGroup t K σ.toRingHom :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).2
  have hb'B : b' ∈ borelGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb').1).1
  have hb'Γ : b' ∈ twistedFixedGroup t K σ.toRingHom :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb').1).2
  have hnΓ : n ∈ twistedFixedGroup t K σ.toRingHom := by
    have e : n = b⁻¹ * (b * n * b') * b'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hbΓ) hgΓ) (inv_mem hb'Γ)
  have htail : ∀ h : ℤ, ∀ α ∈ parabolicRadicalRootsGe t.tag (t.orbitUnion J) h,
      w • α ∈ parabolicRadicalRootsGe t.tag (t.orbitUnion J) h := by
    intro h α hα
    set S := parabolicRadicalRootsGe t.tag (t.orbitUnion J) h with hS
    have hle : rootSpan t.tag K ((fun β => w • β) '' S) ⊓ twistedFixedGroup t K σ.toRingHom ≤
        rootSpan t.tag K S ⊓ twistedFixedGroup t K σ.toRingHom := by
      intro y hy
      obtain ⟨hyS, hyΓ⟩ := Subgroup.mem_inf.1 hy
      rw [← (canonical_weyl_root_transport t.tag K).1 w S (fun β hβ => hβ.1.1.1)] at hyS
      obtain ⟨x, hx, rfl⟩ := hyS
      change n * x * n⁻¹ ∈ _
      change n * x * n⁻¹ ∈ twistedFixedGroup t K σ.toRingHom at hyΓ
      have hxΓ : x ∈ twistedFixedGroup t K σ.toRingHom := by
        have e : x = n⁻¹ * (n * x * n⁻¹) * n := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hnΓ) hyΓ) hnΓ
      refine Subgroup.mem_inf.2 ⟨?_, hyΓ⟩
      have hNb := borelGroup_le_normalizer_parabolicRadicalGe (K := K) (t.orbitUnion J) h
      have hconj : ∀ z ∈ borelGroup t.tag K, ∀ x' ∈ rootSpan t.tag K S,
          z * x' * z⁻¹ ∈ rootSpan t.tag K S :=
        fun z hz x' hx' => (Subgroup.mem_normalizer_iff.1 (hNb hz) x').1 hx'
      have hx' : b'⁻¹ * x * b'⁻¹⁻¹ ∈ graphFixedParabolicRadicalGe t K σ.toRingHom J h :=
        Subgroup.mem_inf.2 ⟨hconj _ (inv_mem hb'B) x hx,
          mul_mem (mul_mem (inv_mem hb'Γ) hxΓ) (inv_mem (inv_mem hb'Γ))⟩
      have hx'' := (Subgroup.mem_inf.1 (hgN h _ hx')).1
      have e : n * x * n⁻¹ = b⁻¹ * ((b * n * b') * (b'⁻¹ * x * b'⁻¹⁻¹) * (b * n * b')⁻¹) *
          b⁻¹⁻¹ := by group
      rw [e]
      exact hconj _ (inv_mem hbB) _ hx''
    have hSpos : ∀ β ∈ (fun β => w • β) '' S, IsRoot t.tag β ∧ 0 < height β := by
      rintro _ ⟨β, hβ, rfl⟩
      exact ((hbij w hwA).mapsTo hβ.1).1
    have hSρ : ∀ β ∈ (fun β => w • β) '' S, permLattice t.perm β ∈ (fun β => w • β) '' S := by
      rintro _ ⟨β, hβ, rfl⟩
      exact ⟨permLattice t.perm β, permLattice_mem_parabolicRadicalRootsGe hβ,
        (mem_relWeylTwist_iff_smul t).1 hwρ β⟩
    exact subset_of_rootSpan_inf_le σ.toRingHom hSpos hSρ (fun β hβ => hβ.1.1)
      parabolicRadicalRootsGe_closed hle ⟨α, hα, rfl⟩
  have hw1 : w = 1 := eq_one_of_forall_mapsTo_parabolicRadicalRootsGe hAne hwA htail
  rw [hn, hw1, canonicalRep_one, mul_one]
  exact mul_mem hbB hb'B

theorem diagram_fixed_parabolic_radical_diagonal_field_pointwise_rigidity
    (t : TwistTag)
    (K : Type) [Field K] (σ : K ≃+* K) (hσ : σ ^ t.order = 1) {J : Set (Fin t.foldedTag.rank)}
    (hJ : J ≠ Set.univ) :
    (∀ g ∈ graphFixedRootGroup t K σ.toRingHom, ∀ b : Fin t.tag.rank → Kˣ,
      (∀ i, b (t.perm i) = Units.map σ.toRingHom.toMonoidHom (b i)) →
      ∀ δ : K ≃+* K, δ * σ = σ * δ →
      ∃ α : MulAut (graphFixedRootGroup t K σ.toRingHom),
        ∀ x : graphFixedRootGroup t K σ.toRingHom,
          (α x : ModGL t.tag K) = g * rootDiagUnit t.tag b *
            Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit t.tag b)⁻¹ * g⁻¹) ∧
    (∀ g ∈ graphFixedRootGroup t K σ.toRingHom, ∀ b : Fin t.tag.rank → Kˣ,
      (∀ i, b (t.perm i) = Units.map σ.toRingHom.toMonoidHom (b i)) →
      ∀ δ : K ≃+* K, δ * σ = σ * δ → ∀ α : MulAut (graphFixedRootGroup t K σ.toRingHom),
      (∀ x : graphFixedRootGroup t K σ.toRingHom, (α x : ModGL t.tag K) =
        g * rootDiagUnit t.tag b * Units.map (entrywiseHom δ.toRingHom) x *
          (rootDiagUnit t.tag b)⁻¹ * g⁻¹) →
      (∀ x : graphFixedRootGroup t K σ.toRingHom,
        (x : ModGL t.tag K) ∈ graphFixedParabolicRadical t K σ.toRingHom J → α x = x) →
      δ = 1 ∧ ∃ z ∈ (Subgroup.center (graphFixedParabolicRadical t K σ.toRingHom J)).map
          (graphFixedParabolicRadical t K σ.toRingHom J).subtype,
        ∃ hz : z ∈ graphFixedRootGroup t K σ.toRingHom, α = MulAut.conj ⟨z, hz⟩) ∧
    ∀ z ∈ (Subgroup.center (graphFixedParabolicRadical t K σ.toRingHom J)).map
        (graphFixedParabolicRadical t K σ.toRingHom J).subtype,
      ∃ hz : z ∈ graphFixedRootGroup t K σ.toRingHom,
        (∀ x : graphFixedRootGroup t K σ.toRingHom,
          (x : ModGL t.tag K) ∈ graphFixedParabolicRadical t K σ.toRingHom J →
            MulAut.conj (⟨z, hz⟩ : graphFixedRootGroup t K σ.toRingHom) x = x) ∧
        ∃ g ∈ graphFixedRootGroup t K σ.toRingHom, ∃ b : Fin t.tag.rank → Kˣ,
          (∀ i, b (t.perm i) = Units.map σ.toRingHom.toMonoidHom (b i)) ∧
          ∀ x : graphFixedRootGroup t K σ.toRingHom,
            ((MulAut.conj (⟨z, hz⟩ : graphFixedRootGroup t K σ.toRingHom) x :
              graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K) =
              g * rootDiagUnit t.tag b * Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x *
                (rootDiagUnit t.tag b)⁻¹ * g⁻¹ := by
  have hQC : graphFixedParabolicRadical t K σ.toRingHom J ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup t K _ J
  refine ⟨fun g hg b hb δ hδσ => ?_, fun g hg b hb δ hδσ α hα hfix => ?_, fun z hz => ?_⟩
  · have hδ : ∀ c, δ (σ.toRingHom c) = σ.toRingHom (δ c) := fun c =>
      congrArg (fun f : K ≃+* K => f c) hδσ
    exact exists_mulAut_graphFixedRootGroup hg hb hδ
  · have hδ : ∀ c, δ (σ.toRingHom c) = σ.toRingHom (δ c) := fun c =>
      congrArg (fun f : K ≃+* K => f c) hδσ
    have hfix' : ∀ x ∈ graphFixedParabolicRadical t K σ.toRingHom J,
        g * diagFieldAut t.tag b δ x * g⁻¹ = x := by
      intro x hx
      have h1 := congrArg Subtype.val (hfix ⟨x, hQC hx⟩ hx)
      rw [hα] at h1
      rw [diagFieldAut_apply]
      simpa only [mul_assoc] using h1
    have hNQ : g ∈ Subgroup.normalizer
        (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) :=
      mem_normalizer_of_fixes (map_diagFieldAut_rootSpan_inf hb hδ fun γ hγ => hγ.1.1) hfix'
    have hgP : g ∈ graphFixedParabolic t K σ.toRingHom J := by
      rw [← diagram_fixed_parabolic_root_radical_normalizers t K σ J]
      exact Subgroup.mem_inf.2 ⟨hg, hNQ⟩
    have hgN : ∀ h : ℤ, ∀ x ∈ graphFixedParabolicRadicalGe t K σ.toRingHom J h,
        g * x * g⁻¹ ∈ graphFixedParabolicRadicalGe t K σ.toRingHom J h := by
      intro h x hx
      have hN := mem_normalizer_of_fixes (H := graphFixedParabolicRadicalGe t K σ.toRingHom J h)
        (map_diagFieldAut_rootSpan_inf hb hδ fun γ hγ => hγ.1.1.1)
        (fun y hy => hfix' y (graphFixedParabolicRadicalGe_le t K _ J h hy))
      exact (Subgroup.mem_normalizer_iff.1 hN x).1 hx
    have hgB := mem_borelGroup_of_normalizes_graphFixed σ hJ hgP hgN
    have hgB' : g ∈ (borelGroup t.tag K : Set (ModGL t.tag K)) := hgB
    rw [(triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.1] at hgB'
    obtain ⟨u, hu, s, hs, rfl⟩ := hgB'
    beta_reduce at hg hα hfix'
    obtain ⟨e, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs
    set c := e * b with hc
    have hdc : rootDiagUnit t.tag e * rootDiagUnit t.tag b = rootDiagUnit t.tag c := by
      rw [hc, rootDiagUnit_mul]
    have hkey : ∀ x ∈ graphFixedParabolicRadical t K σ.toRingHom J,
        u * (rootDiagUnit t.tag c * Units.map (entrywiseHom δ.toRingHom) x *
          (rootDiagUnit t.tag c)⁻¹) * u⁻¹ = x := by
      intro x hx
      refine Eq.trans ?_ (hfix' x hx)
      rw [diagFieldAut_apply, ← hdc]
      group
    have hzQ : ∀ w ∈ relWeylTwist t, ∀ a, (∀ i ∈ t.orbit a,
        w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈
          parabolicRadicalRoots t.tag (t.orbitUnion J)) → ∀ y : orbitField t K σ.toRingHom a,
        canonicalRep (coxeterSystem t.tag) K w * (orbitX t K σ.toRingHom a y : ModGL t.tag K) *
          (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
            graphFixedParabolicRadical t K σ.toRingHom J := by
      intro w hw a hsub y
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 (conj_orbitX_mem hw a y)
      refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ h1, h2⟩
      rintro _ ⟨i, hi, rfl⟩
      exact hsub i hi
    have hconjO : ∀ w ∈ relWeylTwist t, ∀ a, (∀ i ∈ t.orbit a,
        w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈
          parabolicRadicalRoots t.tag (t.orbitUnion J)) → ∀ {y z : ModGL t.tag K},
        y ∈ rootSpan t.tag K
          ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) →
        z ∈ rootSpan t.tag K
          ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) →
        u * y * u⁻¹ = z → y = z := by
      intro w hw a hsub y z hy hz hyz
      obtain ⟨i₀, hi₀⟩ := t.orbit_nonempty a
      refine eq_of_conj_eq_of_mem_rootSpan (s := height (w • (Pi.single i₀ 1 :
        Fin t.tag.rank → ℤ))) (fun γ hγ => ?_) (hsub i₀ hi₀).1.2 (fun γ hγ γ' hγ' p q hp hq => ?_)
        hu hy hz hyz
      · obtain ⟨i, hi, rfl⟩ := hγ
        exact ⟨(hsub i hi).1.1,
          height_eq_of_mem_orbitImage hw hi₀ (Finset.mem_image_of_mem _ hi)⟩
      · obtain ⟨i, hi, rfl⟩ := hγ
        obtain ⟨j, hj, rfl⟩ := hγ'
        exact not_isRoot_nsmul_add_nsmul_of_mem_orbitImage w a (Finset.mem_image_of_mem _ hi)
          (Finset.mem_image_of_mem _ hj) hp hq
    have hchar : ∀ γ ∈ parabolicRadicalRoots t.tag (t.orbitUnion J), rootChar c γ = 1 := by
      intro γ hγ
      obtain ⟨w, hw, a, hOγ⟩ := t.exists_diagramOrbit_eq hγ.1.1
      have hsub : ∀ i ∈ t.orbit a, w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈
          parabolicRadicalRoots t.tag (t.orbitUnion J) := fun i hi =>
        diagramOrbit_subset (fun β hβ => permLattice_mem_parabolicRadicalRoots hβ) hγ
          (by rw [hOγ]; exact Finset.mem_image_of_mem _ hi)
      set n := canonicalRep (coxeterSystem t.tag) K w with hn
      set z := n * (orbitX t K σ.toRingHom a 1 : ModGL t.tag K) * n⁻¹ with hz
      have hzQ' := hzQ w hw a hsub 1
      have h1' : (⟨δ ((1 : orbitField t K σ.toRingHom a) : K),
          map_mem_orbitField hδ (1 : orbitField t K σ.toRingHom a).2⟩ :
            orbitField t K σ.toRingHom a) = 1 := Subtype.ext (by simp)
      have hzfix : Units.map (entrywiseHom δ.toRingHom) z = z := by
        rw [hz, hn, units_map_entrywiseHom_conj_orbitX hδ, h1']
      have hzO := (Subgroup.mem_inf.1 (conj_orbitX_mem (K := K) (σ := σ.toRingHom) hw a 1)).1
      have hyO : rootDiagUnit t.tag c * z * (rootDiagUnit t.tag c)⁻¹ ∈ rootSpan t.tag K
          ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) := by
        have hmap := map_rootSpan_of_forall (f := (MulAut.conj (rootDiagUnit t.tag c)).toMonoidHom)
          (S := (fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a))
          fun β hβ => by
            obtain ⟨i, hi, rfl⟩ := hβ
            exact map_conj_rootDiagUnit_rootSubgroup c (IsRoot.smul (isRoot_single t.tag i) w)
        rw [← hmap]
        exact ⟨z, hzO, rfl⟩
      have h1 : u * (rootDiagUnit t.tag c * z * (rootDiagUnit t.tag c)⁻¹) * u⁻¹ = z := by
        have := hkey z hzQ'
        rwa [hzfix] at this
      have hyz := hconjO w hw a hsub hyO hzO h1
      obtain ⟨m, β, hβ⟩ := ((finite_setOf_isRoot t.tag).subset
        fun β (hβ : β ∈ {β | IsRoot t.tag β ∧ 0 < height β}) => hβ.1).fin_embedding
      have hβpos : ∀ i, IsRoot t.tag (β i) ∧ 0 < height (β i) := fun i => by
        have : β i ∈ {β | IsRoot t.tag β ∧ 0 < height β} := hβ ▸ Set.mem_range_self i
        exact this
      have hpos : ∀ i ∈ t.orbit a, 0 < height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) :=
        fun i hi => (hsub i hi).1.2
      obtain ⟨c₀, hc₀, hsupp⟩ := exists_coordinates_conj_orbitXProd (K := K) w a hpos β
        β.injective hβ
      have hz1 : (orbitX t K σ.toRingHom a 1 : ModGL t.tag K) = orbitXProd t a fun _ => 1 := by
        rw [coe_orbitX_eq_orbitXProd]
        refine orbitXProd_congr t fun j hj => ?_
        obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
        rw [orbitParam_pow t σ.toRingHom _ hk]
        simp
      have hzprod : z = (List.ofFn fun i => pinnedX t.tag K (β i) (c₀ i)).prod := by
        rw [hz, hz1, ← hc₀]
      have hyprod : rootDiagUnit t.tag c * z * (rootDiagUnit t.tag c)⁻¹ =
          (List.ofFn fun i => pinnedX t.tag K (β i) ((rootChar c (β i) : K) * c₀ i)).prod := by
        rw [hzprod, rootDiagUnit_conj_list_prod c β (fun i => (hβpos i).1) c₀]
      have hcc := (positive_root_product_injectivity t.tag K β β.injective hβpos).2
        (hyprod.symm.trans (hyz.trans hzprod))
      obtain ⟨i₀, hi₀⟩ : γ ∈ Set.range β := hβ ▸ ⟨hγ.1.1, hγ.1.2⟩
      have hne : c₀ i₀ ≠ 0 := (hsupp i₀).2 (by
        rw [hi₀, ← hOγ]
        exact t.self_mem_diagramOrbit γ)
      have h2 : (rootChar c (β i₀) : K) * c₀ i₀ = c₀ i₀ := congrFun hcc i₀
      rw [hi₀] at h2
      have h3 : ((rootChar c γ : K) - 1) * c₀ i₀ = 0 := by linear_combination h2
      exact Units.ext (by
        rw [Units.val_one]
        exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne))
    obtain ⟨-, hspan, -, -⟩ := parabolic_radical_roots_span_lattice t.tag
      (orbitUnion_ne_univ (t := t) hJ)
    let φ : (Fin t.tag.rank → ℤ) →+ Additive Kˣ :=
      { toFun := fun v => Additive.ofMul (rootChar c v)
        map_zero' := by rw [rootChar_zero]; rfl
        map_add' := fun u v => by rw [rootChar_add]; rfl }
    have hle : Submodule.span ℤ (parabolicRadicalRoots t.tag (t.orbitUnion J)) ≤
        φ.ker.toIntSubmodule :=
      Submodule.span_le.2 fun γ hγ => by
        change Additive.ofMul (rootChar c γ) = 0
        rw [hchar γ hγ]
        rfl
    rw [hspan] at hle
    have hc1 : c = 1 := funext fun i => by
      have h1 : φ (Pi.single i 1) = 0 := hle (Submodule.mem_top (x := Pi.single i 1))
      change Additive.ofMul (rootChar c (Pi.single i 1)) = 0 at h1
      rw [rootChar_single] at h1
      exact h1
    have hdc1 : rootDiagUnit t.tag c = 1 := by rw [hc1, rootDiagUnit_one]
    have hδ1 : δ = 1 := by
      obtain ⟨w, hw, a, hcard, hsub⟩ := exists_orbit_card_eq_order (t := t) hJ
      have hfull : ∀ x : K, x ∈ orbitField t K σ.toRingHom a := fun x => by
        rw [mem_orbitField, hcard]
        have h1 : σ.toRingHom ^ t.order = (σ ^ t.order).toRingHom := by
          induction t.order with
          | zero => rfl
          | succ k ih => rw [pow_succ, pow_succ, ih]; rfl
        rw [h1, hσ]
        rfl
      refine RingEquiv.ext fun x => ?_
      have h1 := hkey _ (hzQ w hw a hsub ⟨x, hfull x⟩)
      rw [hdc1, one_mul, inv_one, mul_one, units_map_entrywiseHom_conj_orbitX hδ] at h1
      have h2 := hconjO w hw a hsub
        (Subgroup.mem_inf.1 (conj_orbitX_mem (K := K) (σ := σ.toRingHom) hw a _)).1
        (Subgroup.mem_inf.1 (conj_orbitX_mem (K := K) (σ := σ.toRingHom) hw a _)).1 h1
      have h3 : (orbitX t K σ.toRingHom a ⟨δ x, map_mem_orbitField hδ (hfull x)⟩ :
          ModGL t.tag K) = orbitX t K σ.toRingHom a ⟨x, hfull x⟩ :=
        mul_left_cancel (mul_right_cancel h2)
      have h4 := orbitX_injective σ.toRingHom a (Subtype.ext h3)
      exact congrArg Subtype.val h4
    subst hδ1
    have heb : rootDiagUnit t.tag e * rootDiagUnit t.tag b = 1 := by rw [hdc, hdc1]
    have hαu : ∀ x : graphFixedRootGroup t K σ.toRingHom, (α x : ModGL t.tag K) = u * x * u⁻¹ := by
      intro x
      rw [hα, units_map_entrywiseHom_one_ringEquiv]
      calc u * rootDiagUnit t.tag e * rootDiagUnit t.tag b * x * (rootDiagUnit t.tag b)⁻¹ *
            (u * rootDiagUnit t.tag e)⁻¹ =
          u * (rootDiagUnit t.tag e * rootDiagUnit t.tag b) * x *
            (rootDiagUnit t.tag e * rootDiagUnit t.tag b)⁻¹ * u⁻¹ := by group
        _ = u * x * u⁻¹ := by rw [heb]; group
    have huΓ : u ∈ twistedFixedGroup t K σ.toRingHom := by
      refine (mem_twistedFixedGroup_iff_twistHom t K _).2 ⟨posUnipotent_le_adjointGroup hu, ?_⟩
      have hgF := ((mem_twistedFixedGroup_iff_twistHom t K _).1
        (graphFixedRootGroup_le t K _ hg)).2
      have hug : u = u * rootDiagUnit t.tag e * rootDiagUnit t.tag b := by
        rw [mul_assoc, heb, mul_one]
      rw [hug, map_mul, hgF, twistHom_rootDiagUnit hb]
    have huC0 : u ∈ graphFixedRootGroup t K σ.toRingHom :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hu, huΓ⟩)
    have huP : u ∈ graphFixedParabolic t K σ.toRingHom J :=
      graphFixedRootBorel_le_graphFixedParabolic t K _ J (Subgroup.mem_inf.2
        ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right hu, huΓ⟩, huC0⟩)
    have huCen : u ∈ graphFixedParabolic t K σ.toRingHom J ⊓ Subgroup.centralizer
        (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) := by
      refine Subgroup.mem_inf.2 ⟨huP, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have h1 := congrArg Subtype.val (hfix ⟨x, hQC hx⟩ hx)
      rw [hαu] at h1
      calc x * u = u * x * u⁻¹ * u := by rw [h1]
        _ = u * x := by group
    rw [(diagram_fixed_proper_parabolic_root_radical_self_centralizing t K σ hJ).1] at huCen
    refine ⟨rfl, u, huCen, huC0, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hαu]
    rfl
  · obtain ⟨⟨z, hzQ⟩, hzc, rfl⟩ := hz
    refine ⟨hQC hzQ, fun x hx => Subtype.ext ?_, z, hQC hzQ, 1, fun i => by simp, fun x => ?_⟩
    · have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨x, hx⟩)
      change z * x * z⁻¹ = x
      change (x : ModGL t.tag K) * z = z * x at h1
      rw [← h1]
      group
    · rw [rootDiagUnit_one, units_map_entrywiseHom_one_ringEquiv]
      change z * x * z⁻¹ = _
      group

end CFSG.LieType.Chevalley
