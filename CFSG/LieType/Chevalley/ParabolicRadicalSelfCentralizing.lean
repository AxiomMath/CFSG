module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.ParabolicRadicalRootsLattice
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem mem_of_pinnedX_mem_rootSpan
    {T : Set (Fin τ.rank → ℤ)}
    (hT : ∀ β ∈ T, IsRoot τ β ∧ 0 < height β)
    (hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) {c : K} (hc : c ≠ 0)
    (hmem : pinnedX τ K α c ∈ rootSpan τ K T) : α ∈ T := by
  classical
  by_contra hαT
  obtain ⟨k, γ, hγ⟩ := ((finite_setOf_isRoot τ).subset fun β hβ => (hT β hβ).1).fin_embedding
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hT hTc γ γ.injective hγ).surjOn hmem
  set β : Fin (k + 1) → Fin τ.rank → ℤ := Fin.snoc γ α with hβ
  have hβinj : Function.Injective β := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        rw [hβ, Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd (hγ ▸ Set.mem_range_self j : γ j ∈ T) (hij ▸ hαT)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [hβ, Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd (hγ ▸ Set.mem_range_self i : γ i ∈ T) (hij.symm ▸ hαT)
      | cast j =>
        rw [hβ, Fin.snoc_castSucc, Fin.snoc_castSucc] at hij
        rw [γ.injective hij]
  have hβpos : ∀ i, IsRoot τ (β i) ∧ 0 < height (β i) := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hβ, Fin.snoc_last]; exact hα
    | cast i => rw [hβ, Fin.snoc_castSucc]; exact hT _ (hγ ▸ Set.mem_range_self i)
  have hinj := (positive_root_product_injectivity τ K β hβinj hβpos).2
  have e1 : (List.ofFn fun i => pinnedX τ K (β i) ((Fin.snoc d 0 : Fin (k + 1) → K) i)).prod =
      pinnedX τ K α c := by
    rw [List.ofFn_succ', List.prod_concat]
    simp only [hβ, Fin.snoc_castSucc, Fin.snoc_last, pinnedX_zero, mul_one]
    exact hd
  have e2 : (List.ofFn fun i =>
      pinnedX τ K (β i) ((Fin.snoc (0 : Fin k → K) c : Fin (k + 1) → K) i)).prod =
      pinnedX τ K α c := by
    rw [List.ofFn_succ', List.prod_concat]
    simp only [hβ, Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, pinnedX_zero,
      List.ofFn_const, List.prod_replicate, one_pow, one_mul]
  have h1 := congrFun (hinj (e1.trans e2.symm)) (Fin.last k)
  simp only [Fin.snoc_last] at h1
  exact hc h1.symm

theorem smul_mem_of_map_conj_rootSpan_le
    {S T : Set (Fin τ.rank → ℤ)} (w : WeylGroup τ)
    (hS : ∀ α ∈ S, IsRoot τ α) (hwS : ∀ α ∈ S, 0 < height (w • α))
    (hT : ∀ β ∈ T, IsRoot τ β ∧ 0 < height β)
    (hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T)
    (h : (rootSpan τ K S).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom ≤
      rootSpan τ K T) :
    ∀ α ∈ S, w • α ∈ T := by
  intro α hα
  rw [(canonical_weyl_root_transport τ K).1 w S hS] at h
  exact mem_of_pinnedX_mem_rootSpan hT hTc ⟨IsRoot.smul (hS α hα) w, hwS α hα⟩ one_ne_zero
    (h (pinnedX_mem_rootSpan (Set.mem_image_of_mem _ hα) 1))

theorem parabolicRadicalRootsGe_pos {J : Set (Fin τ.rank)} {h : ℤ} :
    ∀ β ∈ parabolicRadicalRootsGe τ J h, IsRoot τ β ∧ 0 < height β :=
  fun _ hβ => hβ.1.1

theorem parabolicRadicalRootsGe_closed
    {J : Set (Fin τ.rank)} {h : ℤ} :
    ∀ β ∈ parabolicRadicalRootsGe τ J h, ∀ γ ∈ parabolicRadicalRootsGe τ J h, ∀ a b : ℕ,
      1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) → a • β + b • γ ∈ parabolicRadicalRootsGe τ J h :=
  fun _ hβ _ hγ _ _ ha hb hr => add_mem_parabolicRadicalRootsGe hβ.1.1 hγ ha hb hr

theorem parabolicRadicalGe_le_parabolicRadical
    (J : Set (Fin τ.rank)) (h : ℤ) :
    parabolicRadicalGe τ K J h ≤ parabolicRadical τ K J :=
  iSup₂_le fun α hα => le_iSup₂_of_le α hα.1 le_rfl

theorem eq_one_of_forall_mapsTo_parabolicRadicalRootsGe
    {J : Set (Fin τ.rank)}
    (hJ : J ≠ Set.univ) {w : WeylGroup τ} (hwJ : w ∈ parabolicWeylGroup τ J)
    (htail : ∀ h : ℤ, ∀ α ∈ parabolicRadicalRootsGe τ J h,
      w • α ∈ parabolicRadicalRootsGe τ J h) : w = 1 := by
  obtain ⟨-, -, hbij, hht⟩ := parabolic_radical_roots_span_lattice τ hJ
  refine hht w hwJ fun α hα => ?_
  have hfin : (parabolicRadicalRootsGe τ J (height α + 1)).Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1.1.1
  have hmaps : Set.MapsTo (fun β => w • β) (parabolicRadicalRootsGe τ J (height α + 1))
      (parabolicRadicalRootsGe τ J (height α + 1)) := fun β hβ => htail _ β hβ
  have hinj : Set.InjOn (fun β => w • β) (parabolicRadicalRootsGe τ J (height α + 1)) :=
    fun β _ γ _ h => smul_left_cancel w h
  have hsurj := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj |>.surjOn
  have hge := (htail (height α) α ⟨hα, le_rfl⟩).2
  by_contra hne
  have hgt : height α + 1 ≤ height (w • α) := by omega
  obtain ⟨β, hβ, hβα⟩ := hsurj ⟨(hbij w hwJ).mapsTo hα, hgt⟩
  have := smul_left_cancel w hβα
  rw [this] at hβ
  exact absurd hβ.2 (by omega)

theorem mem_borelGroup_of_centralizes
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) {g : ModGL τ K}
    (hgP : g ∈ parabolicSubgroup τ K J) (hgC : ∀ q ∈ parabolicRadical τ K J, q * g = g * q) :
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
    have hcomm := hgC _ (parabolicRadicalGe_le_parabolicRadical J h hx')
    have e : n * x * n⁻¹ = b⁻¹ * (b'⁻¹ * x * b'⁻¹⁻¹) * b⁻¹⁻¹ :=
      calc n * x * n⁻¹ = b⁻¹ * ((b * n * b') * (b'⁻¹ * x * b'⁻¹⁻¹) * (b * n * b')⁻¹) *
            b⁻¹⁻¹ := by group
        _ = b⁻¹ * (b'⁻¹ * x * b'⁻¹⁻¹) * b⁻¹⁻¹ := by rw [← hcomm, mul_inv_cancel_right]
    rw [e]
    exact hconj _ (inv_mem hb) _ hx'
  have hw1 : w = 1 := eq_one_of_forall_mapsTo_parabolicRadicalRootsGe hJ hwJ htail
  rw [hn, hw1, canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem eq_one_of_conj_mem_borelGroup
    {J : Set (Fin τ.rank)} {q t v : ModGL τ K}
    (hq : q ∈ parabolicRadical τ K J) (ht : t ∈ torusGroup τ K)
    (hv : v ∈ parabolicLeviUnipotent τ K J) {wJ : WeylGroup τ}
    (hwJ : wJ ∈ parabolicWeylGroup τ J)
    (hwJΦ : (fun α => wJ • α) '' parabolicPosRoots τ J = (fun α => -α) '' parabolicPosRoots τ J)
    (hB : canonicalRep (coxeterSystem τ) K wJ * (q * (t * v)) *
      (canonicalRep (coxeterSystem τ) K wJ)⁻¹ ∈ borelGroup τ K) : v = 1 := by
  set n := canonicalRep (coxeterSystem τ) K wJ with hn
  have hnP : n ∈ parabolicSubgroup τ K J :=
    parabolicLevi_le_parabolicSubgroup J (canonicalRep_mem_parabolicLevi hwJ)
  have hNQ := parabolicSubgroup_le_normalizer_parabolicRadical (K := K) J
  have hnq : n * q * n⁻¹ ∈ borelGroup τ K :=
    Subgroup.mem_sup_right (parabolicRadical_le_posUnipotent J
      ((Subgroup.mem_normalizer_iff.1 (hNQ hnP) q).1 hq))
  have hnt : n * t * n⁻¹ ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 ((canonical_weyl_root_transport τ K).2.2 wJ) t).1 ht
  have hnv : n * v * n⁻¹ ∈ negUnipotent τ K := by
    have h1 := canonicalRep_conj_mem_rootSpan (w := wJ) (S := parabolicPosRoots τ J)
      (fun α hα => hα.2.1) hv
    rw [hwJΦ] at h1
    refine rootSpan_le_negUnipotent ?_ h1
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨IsRoot.neg hα.2.1, by rw [height_neg]; linarith [hα.2.2]⟩
  have hmem : n * v * n⁻¹ ∈ borelGroup τ K ⊓ negUnipotent τ K := by
    refine Subgroup.mem_inf.2 ⟨?_, hnv⟩
    have e : n * v * n⁻¹ =
        (n * t * n⁻¹)⁻¹ * ((n * q * n⁻¹)⁻¹ * (n * (q * (t * v)) * n⁻¹)) := by group
    rw [e]
    exact mul_mem (inv_mem (torusGroup_le_borelGroup hnt)) (mul_mem (inv_mem hnq) hB)
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hmem
  have e : v = n⁻¹ * (n * v * n⁻¹) * n := by group
  rw [e, hmem, mul_one, inv_mul_cancel]

theorem exists_mul_torus_of_centralizes
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {g : ModGL τ K} (hgP : g ∈ parabolicSubgroup τ K J)
    (hgC : ∀ q ∈ parabolicRadical τ K J, q * g = g * q) :
    ∃ q ∈ parabolicRadical τ K J, ∃ t ∈ torusGroup τ K, g = q * t := by
  have hgB : g ∈ (borelGroup τ K : Set (ModGL τ K)) := mem_borelGroup_of_centralizes hJ hgP hgC
  rw [borelGroup_eq_mul_parabolic J] at hgB
  obtain ⟨q, hq, _, ⟨t, ht, v, hv, rfl⟩, rfl⟩ := hgB
  obtain ⟨wJ, ⟨hwJ, hwJΦ⟩, -⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.2.2
  have hnP : canonicalRep (coxeterSystem τ) K wJ ∈ parabolicSubgroup τ K J :=
    parabolicLevi_le_parabolicSubgroup J (canonicalRep_mem_parabolicLevi hwJ)
  have hNQ := parabolicSubgroup_le_normalizer_parabolicRadical (K := K) J
  have hg'C : ∀ x ∈ parabolicRadical τ K J,
      x * (canonicalRep (coxeterSystem τ) K wJ * (q * (t * v)) *
        (canonicalRep (coxeterSystem τ) K wJ)⁻¹) =
      canonicalRep (coxeterSystem τ) K wJ * (q * (t * v)) *
        (canonicalRep (coxeterSystem τ) K wJ)⁻¹ * x := by
    intro x hx
    set n := canonicalRep (coxeterSystem τ) K wJ
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ parabolicRadical τ K J :=
      (Subgroup.mem_normalizer_iff.1 (hNQ (inv_mem hnP)) x).1 hx
    have h1 := hgC _ hx'
    calc x * (n * (q * (t * v)) * n⁻¹) =
          n * ((n⁻¹ * x * n⁻¹⁻¹) * (q * (t * v))) * n⁻¹ := by group
      _ = n * ((q * (t * v)) * (n⁻¹ * x * n⁻¹⁻¹)) * n⁻¹ := by rw [h1]
      _ = n * (q * (t * v)) * n⁻¹ * x := by group
  have hg'B := mem_borelGroup_of_centralizes hJ
    (mul_mem (mul_mem hnP hgP) (inv_mem hnP)) hg'C
  exact ⟨q, hq, t, ht, by simp [eq_one_of_conj_mem_borelGroup hq ht hv hwJ hwJΦ hg'B]⟩

theorem rootChar_single (l : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar l (Pi.single i 1) = l i := by
  have := rootChar_nsmul_single l i 1
  rwa [one_smul, pow_one] at this

theorem torus_eq_one_of_centralizes
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {q t : ModGL τ K} (hq : q ∈ parabolicRadical τ K J) (ht : t ∈ torusGroup τ K)
    (hC : ∀ x ∈ parabolicRadical τ K J, x * (q * t) = q * t * x) : t = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨-, hspan, -, -⟩ := parabolic_radical_roots_span_lattice τ hJ
  have hchar : ∀ α ∈ parabolicRadicalRoots τ J, rootChar l α = 1 := by
    intro α hα
    have hαr : IsRoot τ α := hα.1.1
    have hαp : 0 < height α := hα.1.2
    set χ : K := (rootChar l α : K) with hχ
    have hx := hC _ (pinnedX_mem_rootSpan hα (1 : K))
    have hconj : rootDiagUnit τ l * pinnedX τ K α 1 * (rootDiagUnit τ l)⁻¹ = pinnedX τ K α χ := by
      rw [rootDiagUnit_conj_pinnedX l hαr, mul_one]
    have h1 : pinnedX τ K α 1 = q * pinnedX τ K α χ * q⁻¹ := by
      rw [← hconj]
      calc pinnedX τ K α 1 = (q * rootDiagUnit τ l) * pinnedX τ K α 1 *
            (q * rootDiagUnit τ l)⁻¹ := by rw [← hx, mul_inv_cancel_right]
        _ = q * (rootDiagUnit τ l * pinnedX τ K α 1 * (rootDiagUnit τ l)⁻¹) * q⁻¹ := by group
    have h2 : ⁅q, pinnedX τ K α χ⁆ = pinnedX τ K α (1 - χ) := by
      rw [commutatorElement_def, ← h1, pinnedX_neg, ← pinnedX_add, sub_eq_add_neg]
    have hq1 : q ∈ heightSeries τ K 1 := by
      rw [heightSeries_one]
      exact parabolicRadical_le_posUnipotent J hq
    have hx2 : pinnedX τ K α χ ∈ heightSeries τ K (height α) :=
      pinnedX_mem_rootSpan (show α ∈ {β | IsRoot τ β ∧ 0 < height β ∧ height α ≤ height β} from
        ⟨hαr, hαp, le_rfl⟩) χ
    have h3 := commutator_heightSeries_le K 1 (height α)
      (Subgroup.commutator_mem_commutator hq1 hx2)
    rw [h2] at h3
    by_contra hχ1
    have hne : (1 : K) - χ ≠ 0 := sub_ne_zero.2 fun h' =>
      hχ1 (Units.ext (by rw [Units.val_one]; exact h'.symm))
    have hmem := mem_of_pinnedX_mem_rootSpan
      (T := {β | IsRoot τ β ∧ 0 < height β ∧ 1 + height α ≤ height β})
      (fun β hβ => ⟨hβ.1, hβ.2.1⟩)
      (fun β hβ γ hγ a b ha hb hr => nsmul_add_nsmul_mem_heightSet (h := 0) (k := 1 + height α)
        ⟨hβ.2.1, hβ.2.1.le⟩ ⟨hγ.2.1, hγ.2.2⟩ ha hb hr |> fun h' => ⟨h'.1, h'.2.1, by
          have := h'.2.2; omega⟩)
      ⟨hαr, hαp⟩ hne h3
    exact absurd hmem.2.2 (by omega)
  let φ : (Fin τ.rank → ℤ) →+ Additive Kˣ :=
    { toFun := fun v => Additive.ofMul (rootChar l v)
      map_zero' := by rw [rootChar_zero]; rfl
      map_add' := fun u v => by rw [rootChar_add]; rfl }
  have hle : Submodule.span ℤ (parabolicRadicalRoots τ J) ≤ φ.ker.toIntSubmodule :=
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

theorem Chevalley_proper_parabolic_root_radical_self_centralizing
    (τ : Tag) (K : Type) [Field K]
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    parabolicSubgroup τ K J ⊓ Subgroup.centralizer (parabolicRadical τ K J : Set (ModGL τ K)) =
      (Subgroup.center (parabolicRadical τ K J)).map (parabolicRadical τ K J).subtype ∧
    parabolicSubgroup τ K J ⊓ Subgroup.centralizer (parabolicRadical τ K J : Set (ModGL τ K)) ≤
      parabolicRadical τ K J := by
  have hle : parabolicSubgroup τ K J ⊓
      Subgroup.centralizer (parabolicRadical τ K J : Set (ModGL τ K)) ≤ parabolicRadical τ K J := by
    intro g hg
    obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.1 hg
    have hgC' : ∀ q ∈ parabolicRadical τ K J, q * g = g * q := fun q hq =>
      Subgroup.mem_centralizer_iff.1 hgC q hq
    obtain ⟨q, hq, t, ht, rfl⟩ := exists_mul_torus_of_centralizes hJ hgP hgC'
    rw [torus_eq_one_of_centralizes hJ hq ht hgC', mul_one]
    exact hq
  refine ⟨le_antisymm (fun g hg => ?_) ?_, hle⟩
  · refine ⟨⟨g, hle hg⟩, Subgroup.mem_center_iff.2 fun x => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 x x.2
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨(parabolic_root_radical_Levi_factors τ K J).1 x.2,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨y, hy⟩)
    exact this

end CFSG.LieType.Chevalley
