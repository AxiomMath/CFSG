module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Regular
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SignalizerFunctorTheorem.NonLocalExc

set_option linter.unusedSectionVars false


section Regular

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def regProd (τ : Tag) (K : Type) [Field K] : ModGL τ K :=
  ((List.finRange τ.rank).map fun i => xUnit τ K i 1).prod

theorem hasCoord_list_prod (i : Fin τ.rank) (l : List (Fin τ.rank)) :
    HasCoord i ((l.map fun j => xUnit τ K j 1).prod) ((l.count i : ℕ) : K) := by
  induction l with
  | nil => exact ⟨1, one_mem _, by simp [xUnit_zero]⟩
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons]
    have hj : HasCoord i (xUnit τ K j 1) (if j = i then 1 else 0) := by
      by_cases h : j = i
      · subst h
        simpa using hasCoord_xUnit j (1 : K)
      · rw [if_neg h]
        have hr : IsRoot τ (Pi.single j 1 : Fin τ.rank → ℤ) := isRoot_single τ j
        have hne : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ Pi.single i 1 := by
          intro e
          have := congrFun e j
          simp [Pi.single_apply, h] at this
        have hpos : 0 < height (Pi.single j 1 : Fin τ.rank → ℤ) := by
          rw [height_single]; exact one_pos
        have hle : rootSpan τ K {(Pi.single j 1 : Fin τ.rank → ℤ)} ≤ unipComplement τ K i :=
          biSup_mono (Set.singleton_subset_iff.2 ⟨hr, hpos, hne⟩)
        refine ⟨xUnit τ K j 1, hle ?_, by rw [xUnit_zero, one_mul]⟩
        rw [← pinnedX_single]
        exact pinnedX_mem_rootSpan (Set.mem_singleton _) _
    have := hj.mul ih
    convert this using 1
    by_cases h : j = i
    · subst h; simp; ring
    · simp [h]

theorem isRegularUnipotent_regProd : IsRegularUnipotent (regProd τ K) := by
  refine ⟨?_, fun i => ⟨1, one_ne_zero, ?_⟩⟩
  · unfold regProd
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact CFSG.SignalizerFunctorTheorem.NonLocalExc.xUnit_mem_posUnipotent j 1
  · have h := hasCoord_list_prod (τ := τ) (K := K) i (List.finRange τ.rank)
    rw [List.count_finRange] at h
    simpa [regProd] using h

theorem torus_eq_one_of_conj_regular_field {u v t : ModGL τ K} (hu : IsRegularUnipotent u)
    (hv : v ∈ posUnipotent τ K) (ht : t ∈ torusGroup τ K) (h : t * u * t⁻¹ = v⁻¹ * u * v) :
    t = 1 := by
  obtain ⟨l, hl⟩ := exists_torus_characters ht
  have hl' : ∀ α, IsRoot τ α → ∀ c : K, t * pinnedX τ K α c * t⁻¹ =
      pinnedX τ K α (((∏ j, l j ^ α j : Kˣ) : K) * c) := fun α hα => (hl α hα).2
  have hone : ∀ i, l i = 1 := by
    intro i
    obtain ⟨c, hc, hcoord⟩ := hu.2 i
    have h1 := hcoord.conj_torus_char ht hl'
    have h2 : HasCoord i (v⁻¹ * u * v) c := hcoord.conj_posUnipotent hv
    rw [h] at h1
    have h3 := HasCoord.unique h1 h2
    apply Units.ext
    have : (l i : K) * c = 1 * c := by rw [h3, one_mul]
    simpa using mul_right_cancel₀ hc this
  have hprod : ∀ α : Fin τ.rank → ℤ, (∏ j, l j ^ α j : Kˣ) = 1 := fun α => by
    simp [hone]
  have htA : t ∈ adjointGroup τ K := borelGroup_le_adjointGroup' (Subgroup.mem_sup_left ht)
  have hcent : adjointGroup τ K ≤ Subgroup.centralizer ({t} : Set (ModGL τ K)) := by
    rw [adjointGroup_eq_rootSpan]
    refine iSup₂_le fun α hα g hg => ?_
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hl' α hα c
    rw [hprod α, Units.val_one, one_mul] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hz : (⟨t, htA⟩ : adjointGroup τ K) ∈ Subgroup.center (adjointGroup τ K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hcent g.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact Subtype.ext this
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem eq_one_of_commute_regProd_longest {z w₀ : _} (hz : z ∈ adjointGroup τ K)
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hu : z * regProd τ K = regProd τ K * z)
    (hn : z * canonicalRep (coxeterSystem τ) K w₀ = canonicalRep (coxeterSystem τ) K w₀ * z) :
    z = 1 := by
  have hcomm' : z⁻¹ * regProd τ K * z = regProd τ K := by
    rw [mul_assoc, ← hu, inv_mul_cancel_left]
  have hreg : IsRegularUnipotent (regProd τ K) := isRegularUnipotent_regProd
  have hB : z ∈ borelGroup τ K :=
    mem_borelGroup_of_conj_regular hreg hz (by rw [hcomm']; exact hreg.1)
  obtain ⟨-, hmap, hinf, -⟩ := opposite_Borel_intersection τ K w₀ hw₀
  have hB' : z ∈ torusGroup τ K ⊔ negUnipotent τ K := by
    rw [← hmap]
    refine ⟨z, hB, ?_⟩
    show canonicalRep (coxeterSystem τ) K w₀ * z * (canonicalRep (coxeterSystem τ) K w₀)⁻¹ = z
    rw [← hn, mul_assoc, mul_inv_cancel, mul_one]
  have hT : z ∈ torusGroup τ K := by
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  refine torus_eq_one_of_conj_regular_field hreg (one_mem _) hT ?_
  rw [inv_one, one_mul, mul_one, hu, mul_assoc, mul_inv_cancel, mul_one]

theorem weylElt_one_eq (i : Fin τ.rank) :
    weylElt τ K i 1 = xUnit τ K i 1 * yUnit τ K i (-1) * xUnit τ K i 1 :=
  Units.ext (by simp [weylElt, xUnit, yUnit])

theorem eq_one_of_commute_generators {z : ModGL τ K} (hz : z ∈ adjointGroup τ K)
    (hx : ∀ i, z * xUnit τ K i 1 = xUnit τ K i 1 * z)
    (hy : ∀ i, z * yUnit τ K i (-1) = yUnit τ K i (-1) * z) : z = 1 := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  have hzc : ∀ i, Commute z (xUnit τ K i 1) := fun i => hx i
  have hu : z * regProd τ K = regProd τ K * z := by
    refine (Commute.list_prod_right _ _ fun a ha => ?_).eq
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact hzc j
  obtain ⟨ω, hω, hwω⟩ := (coxeterSystem τ).exists_isReduced w₀
  have hn : z * canonicalRep (coxeterSystem τ) K w₀ = canonicalRep (coxeterSystem τ) K w₀ * z := by
    rw [hwω, canonicalRep_wordProd hω]
    refine (Commute.list_prod_right _ _ fun a ha => ?_).eq
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    rw [weylElt_one_eq]
    exact ((hzc j).mul_right (show Commute z (yUnit τ K j (-1)) from hy j)).mul_right (hzc j)
  exact eq_one_of_commute_regProd_longest hz hw₀ hu hn

theorem eq_one_of_commute_image {L : Type} [Field L] (ι : K →+* L) {z : ModGL τ L}
    (hz : z ∈ adjointGroup τ L)
    (hc : ∀ h ∈ (adjointGroup τ K).map (baseChangeGL ι), z * h = h * z) : z = 1 := by
  refine eq_one_of_commute_generators hz (fun i => ?_) (fun i => ?_)
  · have := hc _ ⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1, rfl⟩
    rwa [baseChangeGL_xUnit, map_one] at this
  · have := hc _ ⟨yUnit τ K i (-1), yUnit_mem_adjointGroup i (-1), rfl⟩
    rwa [baseChangeGL_yUnit, map_neg, map_one] at this

end Regular

end CFSG.HardMathSupport.Timmesfeld.LangTorus
