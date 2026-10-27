module

public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.DiagonalFieldActorData

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

variable (τ) in
@[expose] def diagFieldAut (a : Fin τ.rank → Kˣ) (δ : K ≃+* K) : MulAut (ModGL τ K) :=
  MulAut.conj (rootDiagUnit τ a) * exactEntrywiseAut τ δ

theorem diagFieldAut_apply (a : Fin τ.rank → Kˣ) (δ : K ≃+* K) (x : ModGL τ K) :
    diagFieldAut τ a δ x =
      rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ :=
  rfl

theorem diagFieldAut_pinnedX
    (a : Fin τ.rank → Kˣ) (δ : K ≃+* K) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (c : K) :
    diagFieldAut τ a δ (pinnedX τ K γ c) = pinnedX τ K γ ((rootChar a γ : K) * δ c) := by
  have h : Units.map (entrywiseHom δ.toRingHom) (pinnedX τ K γ c) = pinnedX τ K γ (δ c) :=
    Units.ext (by
      rw [Units.coe_map]
      exact entrywise_pinnedX δ.toRingHom γ c)
  rw [diagFieldAut_apply, h, rootDiagUnit_conj_pinnedX a hγ]

theorem map_diagFieldAut_rootSubgroup
    (a : Fin τ.rank → Kˣ) (δ : K ≃+* K)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (rootSubgroup τ K γ).map (diagFieldAut τ a δ).toMonoidHom = rootSubgroup τ K γ :=
  map_rootSubgroup_of_eq (g := fun c => (rootChar a γ : K) * δ c)
    (fun d => ⟨δ.symm (((rootChar a γ)⁻¹ : Kˣ) * d), by
      simp only [RingEquiv.apply_symm_apply, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]⟩)
    fun c => diagFieldAut_pinnedX a δ hγ c

theorem map_diagFieldAut_rootSpan
    (a : Fin τ.rank → Kˣ) (δ : K ≃+* K)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot τ γ) :
    (rootSpan τ K S).map (diagFieldAut τ a δ).toMonoidHom = rootSpan τ K S :=
  map_rootSpan_of_forall fun γ hγ => map_diagFieldAut_rootSubgroup a δ (hS γ hγ)

theorem mem_normalizer_of_fixes {H : Subgroup (ModGL τ K)} {β : MulAut (ModGL τ K)}
    (hβ : H.map β.toMonoidHom = H) {g : ModGL τ K} (hfix : ∀ x ∈ H, g * β x * g⁻¹ = x) :
    g ∈ Subgroup.normalizer (H : Set (ModGL τ K)) := by
  have hβmem : ∀ x ∈ H, β x ∈ H := fun x hx => hβ ▸ Subgroup.mem_map_of_mem _ hx
  have hβsurj : ∀ y ∈ H, ∃ x ∈ H, β x = y := fun y hy => by
    rw [← hβ] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := hβsurj y hy
    rw [hfix x hx]
    exact hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hβsurj _ hy
    have h1 : g⁻¹ * (g * y * g⁻¹) * g = β (g * y * g⁻¹) := by
      rw [eq_inv_mul_iff_mul_eq.mpr (show g * β (g * y * g⁻¹) = g * y * g⁻¹ * g from ?_)]
      · group
      · have := hfix _ hy
        calc g * β (g * y * g⁻¹) = g * β (g * y * g⁻¹) * g⁻¹ * g := by group
          _ = g * y * g⁻¹ * g := by rw [this]
    have h2 : y = β (g * y * g⁻¹) := by
      rw [← h1]
      group
    rw [h2]
    exact hβmem _ hy

theorem mem_borelGroup_of_normalizes
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) {g : ModGL τ K}
    (hgP : g ∈ parabolicSubgroup τ K J)
    (hgN : ∀ h : ℤ, ∀ x ∈ parabolicRadicalGe τ K J h, g * x * g⁻¹ ∈ parabolicRadicalGe τ K J h) :
    g ∈ borelGroup τ K := by
  classical
  have hcells := (standard_parabolic_cells τ K).1 J
  have hgP' : g ∈ (parabolicSubgroup τ K J : Set (ModGL τ K)) := hgP
  rw [hcells] at hgP'
  obtain ⟨w, hwJ, hgw⟩ := Set.mem_iUnion₂.1 hgP'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hgw
  set n := canonicalRep (coxeterSystem τ) K w with hn
  obtain ⟨-, -, hbij, -⟩ := parabolic_radical_roots_span_lattice τ hJ
  have htail : ∀ h : ℤ, ∀ α ∈ parabolicRadicalRootsGe τ J h,
      w • α ∈ parabolicRadicalRootsGe τ J h := by
    intro h
    refine smul_mem_of_map_conj_rootSpan_le (K := K) w (fun α hα => hα.1.1.1)
      (fun α hα => ((hbij w hwJ).mapsTo hα.1).1.2) parabolicRadicalRootsGe_pos
      parabolicRadicalRootsGe_closed ?_
    rintro _ ⟨x, hx, rfl⟩
    change n * x * n⁻¹ ∈ parabolicRadicalGe τ K J h
    have hNb := borelGroup_le_normalizer_parabolicRadicalGe (K := K) J h
    have hconj : ∀ y ∈ borelGroup τ K, ∀ z ∈ parabolicRadicalGe τ K J h,
        y * z * y⁻¹ ∈ parabolicRadicalGe τ K J h :=
      fun y hy z hz => (Subgroup.mem_normalizer_iff.1 (hNb hy) z).1 hz
    have hx' : b'⁻¹ * x * b'⁻¹⁻¹ ∈ parabolicRadicalGe τ K J h := hconj _ (inv_mem hb') x hx
    have hx'' := hgN h _ hx'
    have e : n * x * n⁻¹ = b⁻¹ * ((b * n * b') * (b'⁻¹ * x * b'⁻¹⁻¹) * (b * n * b')⁻¹) *
        b⁻¹⁻¹ := by group
    rw [e]
    exact hconj _ (inv_mem hb) _ hx''
  have hw1 : w = 1 := eq_one_of_forall_mapsTo_parabolicRadicalRootsGe hJ hwJ htail
  rw [hn, hw1, canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem eq_of_conj_pinnedX_eq
    {u : ModGL τ K} (hu : u ∈ posUnipotent τ K)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγp : 0 < height γ) {c d : K}
    (h : u * pinnedX τ K γ c * u⁻¹ = pinnedX τ K γ d) : c = d := by
  have h2 : ⁅u, pinnedX τ K γ c⁆ = pinnedX τ K γ (d - c) := by
    rw [commutatorElement_def, h, pinnedX_neg, ← pinnedX_add, sub_eq_add_neg]
  have hu1 : u ∈ heightSeries τ K 1 := by
    rw [heightSeries_one]
    exact hu
  have hx2 : pinnedX τ K γ c ∈ heightSeries τ K (height γ) :=
    pinnedX_mem_rootSpan (show γ ∈ {β | IsRoot τ β ∧ 0 < height β ∧ height γ ≤ height β} from
      ⟨hγ, hγp, le_rfl⟩) c
  have h3 := commutator_heightSeries_le K 1 (height γ)
    (Subgroup.commutator_mem_commutator hu1 hx2)
  rw [h2] at h3
  by_contra hcd
  have hne : d - c ≠ 0 := sub_ne_zero.2 (Ne.symm hcd)
  have hmem := mem_of_pinnedX_mem_rootSpan
    (T := {β | IsRoot τ β ∧ 0 < height β ∧ 1 + height γ ≤ height β})
    (fun β hβ => ⟨hβ.1, hβ.2.1⟩)
    (fun β hβ ε hε a b ha hb hr => nsmul_add_nsmul_mem_heightSet (h := 0) (k := 1 + height γ)
      ⟨hβ.2.1, hβ.2.1.le⟩ ⟨hε.2.1, hε.2.2⟩ ha hb hr |> fun h' => ⟨h'.1, h'.2.1, by
        have := h'.2.2; omega⟩)
    ⟨hγ, hγp⟩ hne h3
  exact absurd hmem.2.2 (by omega)

theorem rootChar_mul_tuple (a b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem exists_mem_parabolicRadicalRoots
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    ∃ γ, γ ∈ parabolicRadicalRoots τ J := by
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  exact ⟨Pi.single i 1, mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i,
    by rw [height_single]; exact one_pos, i, hi, by simp⟩⟩

theorem Chevalley_parabolic_radical_diagonal_field_pointwise_rigidity
    (τ : Tag) (K : Type)
    [Field K] {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    (∀ g ∈ adjointGroup τ K, ∀ (a : Fin τ.rank → Kˣ) (δ : K ≃+* K) (α : MulAut (adjointGroup τ K)),
      (∀ x : adjointGroup τ K, (α x : ModGL τ K) =
        g * rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ *
          g⁻¹) →
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x) →
      δ = 1 ∧ ∃ z ∈ (Subgroup.center (parabolicRadical τ K J)).map
          (parabolicRadical τ K J).subtype,
        ∃ hz : z ∈ adjointGroup τ K, α = MulAut.conj ⟨z, hz⟩) ∧
    ∀ z ∈ (Subgroup.center (parabolicRadical τ K J)).map (parabolicRadical τ K J).subtype,
      ∃ hz : z ∈ adjointGroup τ K,
        (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J →
          MulAut.conj (⟨z, hz⟩ : adjointGroup τ K) x = x) ∧
        ∃ g ∈ adjointGroup τ K, ∃ a : Fin τ.rank → Kˣ, ∀ x : adjointGroup τ K,
          ((MulAut.conj (⟨z, hz⟩ : adjointGroup τ K) x : adjointGroup τ K) : ModGL τ K) =
            g * rootDiagUnit τ a * Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x *
              (rootDiagUnit τ a)⁻¹ * g⁻¹ := by
  have hQC : parabolicRadical τ K J ≤ adjointGroup τ K :=
    (parabolicRadical_le_posUnipotent J).trans posUnipotent_le_adjointGroup
  refine ⟨fun g hg a δ α hα hfix => ?_, fun z hz => ?_⟩
  ·
    have hfix' : ∀ x ∈ parabolicRadical τ K J, g * diagFieldAut τ a δ x * g⁻¹ = x := by
      intro x hx
      have h1 := congrArg Subtype.val (hfix ⟨x, hQC hx⟩ hx)
      rw [hα] at h1
      rw [diagFieldAut_apply]
      simpa only [mul_assoc] using h1
    have hNQ : g ∈ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
      mem_normalizer_of_fixes (map_diagFieldAut_rootSpan a δ fun γ hγ => hγ.1.1) hfix'
    have hgP : g ∈ parabolicSubgroup τ K J := by
      rw [← adjointGroup_inf_normalizer_parabolicRadical]
      exact Subgroup.mem_inf.2 ⟨hg, hNQ⟩
    have hgN : ∀ h : ℤ, ∀ x ∈ parabolicRadicalGe τ K J h,
        g * x * g⁻¹ ∈ parabolicRadicalGe τ K J h := by
      intro h x hx
      have hN := mem_normalizer_of_fixes (H := parabolicRadicalGe τ K J h)
        (map_diagFieldAut_rootSpan a δ fun γ hγ => hγ.1.1.1)
        (fun y hy => hfix' y (parabolicRadicalGe_le_parabolicRadical J h hy))
      exact (Subgroup.mem_normalizer_iff.1 hN x).1 hx
    have hgB := mem_borelGroup_of_normalizes hJ hgP hgN
    have hgB' : g ∈ (borelGroup τ K : Set (ModGL τ K)) := hgB
    rw [(triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1] at hgB'
    obtain ⟨u, hu, t, ht, rfl⟩ := hgB'
    beta_reduce at hg hα hfix'
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    set c := b * a with hc
    have hkey : ∀ γ ∈ parabolicRadicalRoots τ J, ∀ s : K, (rootChar c γ : K) * δ s = s := by
      intro γ hγ s
      have hγr : IsRoot τ γ := hγ.1.1
      have h1 := hfix' _ (pinnedX_mem_rootSpan hγ s)
      rw [diagFieldAut_pinnedX a δ hγr] at h1
      have h2 : u * pinnedX τ K γ ((rootChar c γ : K) * δ s) * u⁻¹ = pinnedX τ K γ s := by
        have e : pinnedX τ K γ ((rootChar c γ : K) * δ s) = rootDiagUnit τ b *
            pinnedX τ K γ ((rootChar a γ : K) * δ s) * (rootDiagUnit τ b)⁻¹ := by
          rw [rootDiagUnit_conj_pinnedX b hγr, hc, rootChar_mul_tuple, Units.val_mul, mul_assoc]
        rw [e]
        conv_rhs => rw [← h1]
        group
      exact eq_of_conj_pinnedX_eq hu hγr hγ.1.2 h2
    have hchar : ∀ γ ∈ parabolicRadicalRoots τ J, rootChar c γ = 1 := fun γ hγ => Units.ext (by
      have h1 := hkey γ hγ 1
      rwa [map_one, mul_one] at h1)
    obtain ⟨-, hspan, -, -⟩ := parabolic_radical_roots_span_lattice τ hJ
    let φ : (Fin τ.rank → ℤ) →+ Additive Kˣ :=
      { toFun := fun v => Additive.ofMul (rootChar c v)
        map_zero' := by rw [rootChar_zero]; rfl
        map_add' := fun u v => by rw [rootChar_add]; rfl }
    have hle : Submodule.span ℤ (parabolicRadicalRoots τ J) ≤ φ.ker.toIntSubmodule :=
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
    have hδ : δ = 1 := by
      obtain ⟨γ₀, hγ₀⟩ := exists_mem_parabolicRadicalRoots hJ
      refine RingEquiv.ext fun s => ?_
      have h1 := hkey γ₀ hγ₀ s
      rwa [hchar γ₀ hγ₀, Units.val_one, one_mul] at h1
    subst hδ
    have hba : rootDiagUnit τ b * rootDiagUnit τ a = 1 := by
      rw [← rootDiagUnit_mul, ← hc, hc1, rootDiagUnit_one]
    have hαu : ∀ x : adjointGroup τ K, (α x : ModGL τ K) = u * x * u⁻¹ := by
      intro x
      rw [hα, units_map_entrywiseHom_one_ringEquiv]
      calc u * rootDiagUnit τ b * rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹ *
            (u * rootDiagUnit τ b)⁻¹ =
          u * (rootDiagUnit τ b * rootDiagUnit τ a) * x *
            (rootDiagUnit τ b * rootDiagUnit τ a)⁻¹ * u⁻¹ := by group
        _ = u * x * u⁻¹ := by rw [hba]; group
    have huC : u ∈ parabolicSubgroup τ K J ⊓
        Subgroup.centralizer (parabolicRadical τ K J : Set (ModGL τ K)) := by
      refine Subgroup.mem_inf.2 ⟨posUnipotent_le_parabolicSubgroup J hu,
        Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have h1 := congrArg Subtype.val (hfix ⟨x, hQC hx⟩ hx)
      rw [hαu] at h1
      calc x * u = u * x * u⁻¹ * u := by rw [h1]
        _ = u * x := by group
    rw [(Chevalley_proper_parabolic_root_radical_self_centralizing τ K hJ).1] at huC
    refine ⟨rfl, u, huC, posUnipotent_le_adjointGroup hu, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hαu]
    rfl
  · obtain ⟨⟨z, hzQ⟩, hzc, rfl⟩ := hz
    refine ⟨hQC hzQ, fun x hx => Subtype.ext ?_, z, hQC hzQ, 1, fun x => ?_⟩
    · have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨x, hx⟩)
      change z * x * z⁻¹ = x
      change (x : ModGL τ K) * z = z * x at h1
      rw [← h1]
      group
    · rw [rootDiagUnit_one, units_map_entrywiseHom_one_ringEquiv]
      change z * x * z⁻¹ = _
      group

end CFSG.LieType.Chevalley
