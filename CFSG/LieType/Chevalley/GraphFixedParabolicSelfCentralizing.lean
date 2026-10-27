module

public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Coordinates

variable {τ : Tag} {K : Type} [Field K]

theorem fst_coords_eq_of_eq_mul
    {T : Set (Fin τ.rank → ℤ)}
    (hT : ∀ β ∈ T, IsRoot τ β ∧ 0 < height β)
    (hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T)
    {l k : ℕ} (γ₁ : Fin l → Fin τ.rank → ℤ) (γ₂ : Fin k → Fin τ.rank → ℤ)
    (hγ₂ : Set.range γ₂ = T) (hinj : Function.Injective (Fin.append γ₁ γ₂))
    (hpos : ∀ i, IsRoot τ (Fin.append γ₁ γ₂ i) ∧ 0 < height (Fin.append γ₁ γ₂ i))
    (c c' : Fin l → K) (e e' : Fin k → K) {n : ModGL τ K} (hn : n ∈ rootSpan τ K T)
    (h : (List.ofFn fun i => pinnedX τ K (γ₁ i) (c i)).prod *
        (List.ofFn fun i => pinnedX τ K (γ₂ i) (e i)).prod =
      (List.ofFn fun i => pinnedX τ K (γ₁ i) (c' i)).prod *
        (List.ofFn fun i => pinnedX τ K (γ₂ i) (e' i)).prod * n) :
    c = c' := by
  have hγ₂inj : Function.Injective γ₂ := fun i j hij => by
    have := hinj (a₁ := Fin.natAdd l i) (a₂ := Fin.natAdd l j)
      (by rw [Fin.append_right, Fin.append_right]; exact hij)
    exact (Fin.natAdd_inj l).1 this
  have hmem : (List.ofFn fun i => pinnedX τ K (γ₂ i) (e' i)).prod * n ∈ rootSpan τ K T :=
    mul_mem (list_prod_pinnedX_mem_rootSpan γ₂ (fun i => hγ₂ ▸ Set.mem_range_self i) e') hn
  obtain ⟨f, -, hf⟩ := (bijOn_prod_pinnedX K hT hTc γ₂ hγ₂inj hγ₂).surjOn hmem
  have hf' : (List.ofFn fun i => pinnedX τ K (γ₂ i) (f i)).prod =
      (List.ofFn fun i => pinnedX τ K (γ₂ i) (e' i)).prod * n := hf
  have hsplit : ∀ (d : Fin l → K) (d' : Fin k → K),
      (List.ofFn fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append d d' i)).prod =
        (List.ofFn fun i => pinnedX τ K (γ₁ i) (d i)).prod *
          (List.ofFn fun i => pinnedX τ K (γ₂ i) (d' i)).prod := by
    intro d d'
    have e : (fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append d d' i)) =
        Fin.append (fun i => pinnedX τ K (γ₁ i) (d i)) (fun i => pinnedX τ K (γ₂ i) (d' i)) := by
      funext i
      induction i using Fin.addCases with
      | left j => rw [Fin.append_left, Fin.append_left, Fin.append_left]
      | right j => rw [Fin.append_right, Fin.append_right, Fin.append_right]
    rw [e, List.ofFn_fin_append, List.prod_append]
  have hinjP := (positive_root_product_injectivity τ K _ hinj hpos).2
  have hcc := hinjP (a₁ := Fin.append c e) (a₂ := Fin.append c' f) (by
    change (List.ofFn fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append c e i)).prod =
      (List.ofFn fun i => pinnedX τ K (Fin.append γ₁ γ₂ i) (Fin.append c' f i)).prod
    rw [hsplit, hsplit, h, mul_assoc, ← hf'])
  funext i
  have := congrFun hcc (Fin.castAdd k i)
  simpa only [Fin.append_left] using this

theorem conj_mul_eq_mul_conj {G : Type*} [Group G] (d x y : G) :
    d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by
  group

theorem rootDiagUnit_conj_list_prod
    {m : ℕ} (l : Fin τ.rank → Kˣ) (β : Fin m → Fin τ.rank → ℤ)
    (hβ : ∀ i, IsRoot τ (β i)) (c : Fin m → K) :
    rootDiagUnit τ l * (List.ofFn fun i => pinnedX τ K (β i) (c i)).prod * (rootDiagUnit τ l)⁻¹ =
      (List.ofFn fun i => pinnedX τ K (β i) ((rootChar l (β i) : K) * c i)).prod := by
  have e : rootDiagUnit τ l * (List.ofFn fun i => pinnedX τ K (β i) (c i)).prod *
      (rootDiagUnit τ l)⁻¹ =
      MulAut.conj (rootDiagUnit τ l) (List.ofFn fun i => pinnedX τ K (β i) (c i)).prod := rfl
  rw [e, map_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  simp only [Function.comp_apply, MulAut.conj_apply]
  exact rootDiagUnit_conj_pinnedX l (hβ i) (c i)

end Coordinates

variable {t : TwistTag} {K : Type} [Field K]

theorem orbitUnion_ne_univ {J : Set (Fin t.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    t.orbitUnion J ≠ Set.univ := by
  intro h
  refine hJ (Set.eq_univ_of_forall fun a => ?_)
  obtain ⟨i, rfl⟩ := t.exists_orbitIndex_eq a
  exact mem_orbitUnion_iff_orbitIndex.1 (h ▸ Set.mem_univ i)

theorem permLattice_mem_parabolicRadicalRootsGe
    {J : Set (Fin t.foldedTag.rank)} {h : ℤ}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ parabolicRadicalRootsGe t.tag (t.orbitUnion J) h) :
    permLattice t.perm α ∈ parabolicRadicalRootsGe t.tag (t.orbitUnion J) h :=
  ⟨permLattice_mem_parabolicRadicalRoots hα.1, by rw [height_permLattice]; exact hα.2⟩

theorem mem_borelGroup_of_centralizes_graphFixed
    (σ : K ≃+* K) {J : Set (Fin t.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {g : ModGL t.tag K} (hgP : g ∈ graphFixedParabolic t K σ.toRingHom J)
    (hgC : ∀ q ∈ graphFixedParabolicRadical t K σ.toRingHom J, q * g = g * q) :
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
      have hx' : b'⁻¹ * x * b'⁻¹⁻¹ ∈ rootSpan t.tag K S := hconj _ (inv_mem hb'B) x hx
      have hx'Q : b'⁻¹ * x * b'⁻¹⁻¹ ∈ graphFixedParabolicRadical t K σ.toRingHom J :=
        Subgroup.mem_inf.2 ⟨parabolicRadicalGe_le_parabolicRadical _ h hx',
          mul_mem (mul_mem (inv_mem hb'Γ) hxΓ) (inv_mem (inv_mem hb'Γ))⟩
      have hcomm := hgC _ hx'Q
      have e : n * x * n⁻¹ = b⁻¹ * (b'⁻¹ * x * b'⁻¹⁻¹) * b⁻¹⁻¹ :=
        calc n * x * n⁻¹ = b⁻¹ * ((b * n * b') * (b'⁻¹ * x * b'⁻¹⁻¹) * (b * n * b')⁻¹) *
              b⁻¹⁻¹ := by group
          _ = b⁻¹ * (b'⁻¹ * x * b'⁻¹⁻¹) * b⁻¹⁻¹ := by rw [← hcomm, mul_inv_cancel_right]
      rw [e]
      exact hconj _ (inv_mem hbB) _ hx'
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

theorem exists_mul_torus_of_centralizes_graphFixed
    (σ : K ≃+* K)
    {J : Set (Fin t.foldedTag.rank)} (hJ : J ≠ Set.univ) {g : ModGL t.tag K}
    (hgP : g ∈ graphFixedParabolic t K σ.toRingHom J)
    (hgC : ∀ q ∈ graphFixedParabolicRadical t K σ.toRingHom J, q * g = g * q) :
    ∃ q ∈ parabolicRadical t.tag K (t.orbitUnion J), ∃ s ∈ torusGroup t.tag K, g = q * s := by
  have hgB : g ∈ (borelGroup t.tag K : Set (ModGL t.tag K)) :=
    mem_borelGroup_of_centralizes_graphFixed σ hJ hgP hgC
  rw [borelGroup_eq_mul_parabolic (t.orbitUnion J)] at hgB
  obtain ⟨q, hq, _, ⟨s, hs, v, hv, rfl⟩, rfl⟩ := hgB
  obtain ⟨-, -, -, ⟨wA, ⟨hwA, hwAΦ⟩, -⟩, hprops⟩ := diagram_fixed_parabolic_intersection t K σ J
  obtain ⟨-, hnMP, -, -⟩ := hprops wA hwA hwAΦ
  set n := canonicalRep (coxeterSystem t.tag) K wA with hn
  have hnP : n ∈ graphFixedParabolic t K σ.toRingHom J := (Subgroup.mem_inf.1 hnMP).2
  have hnPA : n ∈ parabolicSubgroup t.tag K (t.orbitUnion J) :=
    parabolicLevi_le_parabolicSubgroup _ (Subgroup.mem_inf.1 hnMP).1
  have hnΓ : n ∈ twistedFixedGroup t K σ.toRingHom :=
    graphFixedRootGroup_le t K _ (graphFixedParabolic_le t K _ J hnP)
  have hNQ := parabolicSubgroup_le_normalizer_parabolicRadical (K := K) (t.orbitUnion J)
  have hg'C : ∀ x ∈ graphFixedParabolicRadical t K σ.toRingHom J,
      x * (n * (q * (s * v)) * n⁻¹) = n * (q * (s * v)) * n⁻¹ * x := by
    intro x hx
    obtain ⟨hxQ, hxΓ⟩ := Subgroup.mem_inf.1 hx
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ graphFixedParabolicRadical t K σ.toRingHom J :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hNQ (inv_mem hnPA)) x).1 hxQ,
        mul_mem (mul_mem (inv_mem hnΓ) hxΓ) (inv_mem (inv_mem hnΓ))⟩
    have h1 := hgC _ hx'
    calc x * (n * (q * (s * v)) * n⁻¹) =
          n * ((n⁻¹ * x * n⁻¹⁻¹) * (q * (s * v))) * n⁻¹ := by group
      _ = n * ((q * (s * v)) * (n⁻¹ * x * n⁻¹⁻¹)) * n⁻¹ := by rw [h1]
      _ = n * (q * (s * v)) * n⁻¹ * x := by group
  have hg'B := mem_borelGroup_of_centralizes_graphFixed σ hJ
    (mul_mem (mul_mem hnP hgP) (inv_mem hnP)) hg'C
  exact ⟨q, hq, s, hs, by simp [eq_one_of_conj_mem_borelGroup hq hs hv hwA hwAΦ hg'B]⟩

theorem torus_eq_one_of_centralizes_graphFixed
    (σ : K ≃+* K) {J : Set (Fin t.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {q s : ModGL t.tag K} (hq : q ∈ parabolicRadical t.tag K (t.orbitUnion J))
    (hs : s ∈ torusGroup t.tag K)
    (hC : ∀ x ∈ graphFixedParabolicRadical t K σ.toRingHom J, x * (q * s) = q * s * x) :
    s = 1 := by
  classical
  have hAne := orbitUnion_ne_univ (t := t) hJ
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs
  obtain ⟨-, hspan, -, -⟩ := parabolic_radical_roots_span_lattice t.tag hAne
  have hchar : ∀ α ∈ parabolicRadicalRoots t.tag (t.orbitUnion J), rootChar l α = 1 := by
    intro α hα
    set d := rootDiagUnit t.tag l with hd
    set T : Set (Fin t.tag.rank → ℤ) :=
      {β | IsRoot t.tag β ∧ 0 < height β ∧ 1 + height α ≤ height β} with hTdef
    have hT : ∀ β ∈ T, IsRoot t.tag β ∧ 0 < height β := fun β hβ => ⟨hβ.1, hβ.2.1⟩
    have hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • β + b • γ) →
        a • β + b • γ ∈ T := by
      intro β hβ γ hγ a b ha hb hr
      have h' := nsmul_add_nsmul_mem_heightSet (h := 0) (k := 1 + height α) ⟨hβ.2.1, hβ.2.1.le⟩
        ⟨hγ.2.1, hγ.2.2⟩ ha hb hr
      exact ⟨h'.1, h'.2.1, by have := h'.2.2; omega⟩
    have hO : t.diagramOrbit α ∈ t.diagramRootOrbits := ⟨α, hα.1.1, rfl⟩
    have hOpos : ∀ γ ∈ t.diagramOrbit α, 0 < height γ := fun γ hγ => by
      rw [t.height_of_mem_diagramOrbit hγ]
      exact hα.1.2
    obtain ⟨z, hz, hcoord⟩ := exists_orbit_coordinate_element (K := K) σ.toRingHom hO hOpos
    obtain ⟨hzO, hzΓ⟩ := Subgroup.mem_inf.1 hz
    have hOR : (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) ⊆
        parabolicRadicalRoots t.tag (t.orbitUnion J) :=
      diagramOrbit_subset (fun β hβ => permLattice_mem_parabolicRadicalRoots hβ) hα
    have hzQ : z ∈ graphFixedParabolicRadical t K σ.toRingHom J :=
      Subgroup.mem_inf.2 ⟨rootSpan_mono hOR hzO, hzΓ⟩
    set y := d * z * d⁻¹ with hy
    have hzy : z = q * y * q⁻¹ := by
      have h1 := hC z hzQ
      calc z = (q * d) * z * (q * d)⁻¹ := by rw [← h1, mul_inv_cancel_right]
        _ = q * y * q⁻¹ := by rw [hy]; group
    have hyU : y ∈ heightSeries t.tag K (height α) := by
      have hyO : y ∈ rootSpan t.tag K (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) :=
        (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan
          (fun β hβ => (hOR hβ).1.1) hs) z).1 hzO
      have hsub : (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) ⊆
          {β | IsRoot t.tag β ∧ 0 < height β ∧ height α ≤ height β} := fun β hβ =>
        ⟨(hOR hβ).1.1, (hOR hβ).1.2, (t.height_of_mem_diagramOrbit hβ).ge⟩
      exact rootSpan_mono hsub hyO
    have hqU : q ∈ heightSeries t.tag K 1 := by
      rw [heightSeries_one]
      exact parabolicRadical_le_posUnipotent _ hq
    have hcomm := commutator_heightSeries_le K 1 (height α)
      (Subgroup.commutator_mem_commutator hqU hyU)
    set n := y⁻¹ * ⁅q, y⁆ * y with hn
    have hnT : n ∈ rootSpan t.tag K T := by
      have hyU' : y⁻¹ ∈ posUnipotent t.tag K := inv_mem (heightSeries_le_posUnipotent _ hyU)
      have := (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K (1 + height α) hyU')
        _).1 hcomm
      rw [inv_inv] at this
      exact this
    have hzyn : z = y * n := by
      rw [hn, commutatorElement_def, hzy]
      group
    obtain ⟨k₁, γ₁, hγ₁⟩ := ((finite_setOf_isRoot t.tag).subset
      fun β (hβ : β ∈ {β | IsRoot t.tag β ∧ 0 < height β} \ T) => hβ.1.1).fin_embedding
    obtain ⟨k₂, γ₂, hγ₂⟩ :=
      ((finite_setOf_isRoot t.tag).subset fun β hβ => (hT β hβ).1).fin_embedding
    have hβinj : Function.Injective (Fin.append γ₁ γ₂) := by
      refine Fin.append_injective_iff.2 ⟨γ₁.injective, γ₂.injective, fun i j hij => ?_⟩
      have h₁ : γ₁ i ∈ {β | IsRoot t.tag β ∧ 0 < height β} \ T := hγ₁ ▸ Set.mem_range_self i
      have h₂ : γ₂ j ∈ T := hγ₂ ▸ Set.mem_range_self j
      exact h₁.2 (hij ▸ h₂)
    have hβrange : Set.range (Fin.append γ₁ γ₂) = {β | IsRoot t.tag β ∧ 0 < height β} := by
      ext γ
      constructor
      · rintro ⟨i, rfl⟩
        induction i using Fin.addCases with
        | left j =>
          rw [Fin.append_left]
          exact (hγ₁ ▸ Set.mem_range_self j : γ₁ j ∈ {β | IsRoot t.tag β ∧ 0 < height β} \ T).1
        | right j =>
          rw [Fin.append_right]
          exact hT _ (hγ₂ ▸ Set.mem_range_self j)
      · intro hγ
        by_cases hγT : γ ∈ T
        · obtain ⟨j, rfl⟩ : γ ∈ Set.range γ₂ := hγ₂ ▸ hγT
          exact ⟨Fin.natAdd k₁ j, Fin.append_right _ _ _⟩
        · obtain ⟨j, rfl⟩ : γ ∈ Set.range γ₁ := hγ₁ ▸ ⟨hγ, hγT⟩
          exact ⟨Fin.castAdd k₂ j, Fin.append_left _ _ _⟩
    have hβpos : ∀ i, IsRoot t.tag (Fin.append γ₁ γ₂ i) ∧ 0 < height (Fin.append γ₁ γ₂ i) :=
      fun i => by
        have : Fin.append γ₁ γ₂ i ∈ {β | IsRoot t.tag β ∧ 0 < height β} :=
          hβrange ▸ Set.mem_range_self i
        exact this
    obtain ⟨⟨c, hc⟩, hsupp⟩ := hcoord (Fin.append γ₁ γ₂) hβinj hβrange
    set c₁ : Fin k₁ → K := fun i => c (Fin.castAdd k₂ i) with hc₁
    set c₂ : Fin k₂ → K := fun i => c (Fin.natAdd k₁ i) with hc₂
    have hsplit : ∀ (e₁ : Fin k₁ → K) (e₂ : Fin k₂ → K),
        (List.ofFn fun i => pinnedX t.tag K (Fin.append γ₁ γ₂ i) (Fin.append e₁ e₂ i)).prod =
          (List.ofFn fun i => pinnedX t.tag K (γ₁ i) (e₁ i)).prod *
            (List.ofFn fun i => pinnedX t.tag K (γ₂ i) (e₂ i)).prod := by
      intro e₁ e₂
      have e : (fun i => pinnedX t.tag K (Fin.append γ₁ γ₂ i) (Fin.append e₁ e₂ i)) =
          Fin.append (fun i => pinnedX t.tag K (γ₁ i) (e₁ i))
            (fun i => pinnedX t.tag K (γ₂ i) (e₂ i)) := by
        funext i
        induction i using Fin.addCases with
        | left j => rw [Fin.append_left, Fin.append_left, Fin.append_left]
        | right j => rw [Fin.append_right, Fin.append_right, Fin.append_right]
      rw [e, List.ofFn_fin_append, List.prod_append]
    have hcc : c = Fin.append c₁ c₂ := (Fin.append_castAdd_natAdd).symm
    have hz' : z = (List.ofFn fun i => pinnedX t.tag K (γ₁ i) (c₁ i)).prod *
        (List.ofFn fun i => pinnedX t.tag K (γ₂ i) (c₂ i)).prod := by
      rw [hc, hcc, hsplit]
    have hγ₁r : ∀ i, IsRoot t.tag (γ₁ i) := fun i =>
      (hγ₁ ▸ Set.mem_range_self i : γ₁ i ∈ {β | IsRoot t.tag β ∧ 0 < height β} \ T).1.1
    have hγ₂r : ∀ i, IsRoot t.tag (γ₂ i) := fun i => (hT _ (hγ₂ ▸ Set.mem_range_self i)).1
    have hy' : y = (List.ofFn fun i => pinnedX t.tag K (γ₁ i)
          ((rootChar l (γ₁ i) : K) * c₁ i)).prod *
        (List.ofFn fun i => pinnedX t.tag K (γ₂ i) ((rootChar l (γ₂ i) : K) * c₂ i)).prod := by
      rw [hy, hz', conj_mul_eq_mul_conj, hd, rootDiagUnit_conj_list_prod l γ₁ hγ₁r,
        rootDiagUnit_conj_list_prod l γ₂ hγ₂r]
    have heq := fst_coords_eq_of_eq_mul hT hTc γ₁ γ₂ hγ₂ hβinj hβpos c₁
      (fun i => (rootChar l (γ₁ i) : K) * c₁ i) c₂ (fun i => (rootChar l (γ₂ i) : K) * c₂ i) hnT
      (by rw [← hz', ← hy']; exact hzyn)
    have hαT : α ∉ T := fun h => by have := h.2.2; omega
    obtain ⟨j, hj⟩ : α ∈ Set.range γ₁ := hγ₁ ▸ ⟨⟨hα.1.1, hα.1.2⟩, hαT⟩
    have hcj : c₁ j ≠ 0 := by
      have := (hsupp c hc (Fin.castAdd k₂ j)).2 (by
        rw [Fin.append_left, hj]
        exact t.self_mem_diagramOrbit α)
      exact this
    have h1 : c₁ j = (rootChar l (γ₁ j) : K) * c₁ j := congrFun heq j
    rw [hj] at h1
    have h2 : ((rootChar l α : K) - 1) * c₁ j = 0 := by linear_combination -h1
    have h3 : (rootChar l α : K) = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hcj)
    exact Units.ext (by rw [h3, Units.val_one])
  let φ : (Fin t.tag.rank → ℤ) →+ Additive Kˣ :=
    { toFun := fun v => Additive.ofMul (rootChar l v)
      map_zero' := by rw [rootChar_zero]; rfl
      map_add' := fun u v => by rw [rootChar_add]; rfl }
  have hle : Submodule.span ℤ (parabolicRadicalRoots t.tag (t.orbitUnion J)) ≤
      φ.ker.toIntSubmodule :=
    Submodule.span_le.2 fun α hα => by
      change Additive.ofMul (rootChar l α) = 0
      rw [hchar α hα]
      rfl
  rw [hspan] at hle
  have hl : l = 1 := funext fun i => by
    have h1 : φ (Pi.single i 1) = 0 := hle (Submodule.mem_top (x := Pi.single i 1))
    change Additive.ofMul (rootChar l (Pi.single i 1)) = 0 at h1
    rw [rootChar_single] at h1
    exact h1
  rw [hl, rootDiagUnit_one]

theorem diagram_fixed_proper_parabolic_root_radical_self_centralizing
    (t : TwistTag) (K : Type)
    [Field K] (σ : K ≃+* K) {J : Set (Fin t.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    graphFixedParabolic t K σ.toRingHom J ⊓
        Subgroup.centralizer (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) =
      (Subgroup.center (graphFixedParabolicRadical t K σ.toRingHom J)).map
        (graphFixedParabolicRadical t K σ.toRingHom J).subtype ∧
    graphFixedParabolic t K σ.toRingHom J ⊓
        Subgroup.centralizer (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) ≤
      graphFixedParabolicRadical t K σ.toRingHom J := by
  have hle : graphFixedParabolic t K σ.toRingHom J ⊓
      Subgroup.centralizer (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) ≤
        graphFixedParabolicRadical t K σ.toRingHom J := by
    intro g hg
    obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.1 hg
    have hgC' : ∀ q ∈ graphFixedParabolicRadical t K σ.toRingHom J, q * g = g * q :=
      fun q hq => Subgroup.mem_centralizer_iff.1 hgC q hq
    have hgΓ : g ∈ twistedFixedGroup t K σ.toRingHom :=
      graphFixedRootGroup_le t K _ (graphFixedParabolic_le t K _ J hgP)
    obtain ⟨q, hq, s, hs, rfl⟩ := exists_mul_torus_of_centralizes_graphFixed σ hJ hgP hgC'
    rw [torus_eq_one_of_centralizes_graphFixed σ hJ hq hs hgC', mul_one] at hgΓ ⊢
    exact Subgroup.mem_inf.2 ⟨hq, hgΓ⟩
  have hQP : graphFixedParabolicRadical t K σ.toRingHom J ≤
      graphFixedParabolic t K σ.toRingHom J := by
    intro x hx
    refine graphFixedRootBorel_le_graphFixedParabolic t K _ J (Subgroup.mem_inf.2
      ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right (parabolicRadical_le_posUnipotent _
        (Subgroup.mem_inf.1 hx).1), (Subgroup.mem_inf.1 hx).2⟩,
        graphFixedParabolicRadical_le_graphFixedRootGroup t K _ J hx⟩)
  refine ⟨le_antisymm (fun g hg => ?_) ?_, hle⟩
  · refine ⟨⟨g, hle hg⟩, Subgroup.mem_center_iff.2 fun x => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 x x.2
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hQP x.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨y, hy⟩)

end CFSG.LieType.Chevalley
