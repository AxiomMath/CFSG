module

public import CFSG.LieType.Multipliers.PresentedCover

public section

namespace CFSG.LieType.Multipliers

open Subgroup CFSG.Open

variable {X : Type} [Group X] {ι : Type} {g : ι → X} {R : Set (FreeGroup ι)} {w : ι → FreeGroup ι}

abbrev relatorImages (R : Set (FreeGroup ι)) (w : ι → FreeGroup ι) : Subgroup (PresentedCover R w) :=
  closure (PresentedGroup.mk (coverRelators R w) '' R)

theorem relatorImages_le_center :
    relatorImages R w ≤ center (PresentedCover R w) := by
  rw [closure_le]
  rintro _ ⟨r, hr, rfl⟩
  exact mk_mem_center w hr

theorem ker_coverMap_le_closure (hP : IsPresentation g R)
    (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    (coverMap hP hwg).ker ≤ relatorImages R w := by
  intro x hx
  obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective _ x
  have hf : f ∈ normalClosure R := by
    rw [← hP.ker_lift]
    exact hx
  have hN : (relatorImages R w).Normal := normal_of_le_center relatorImages_le_center
  have hmap : (normalClosure R).map (PresentedGroup.mk (coverRelators R w)) ≤ relatorImages R w := by
    rw [map_normalClosure _ _ (PresentedGroup.mk_surjective _)]
    exact normalClosure_le_normal subset_closure
  exact hmap (mem_map_of_mem _ hf)

theorem relatorImages_le_ker (hP : IsPresentation g R) (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    relatorImages R w ≤ (coverMap hP hwg).ker := by
  rw [closure_le]
  rintro _ ⟨r, hr, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, coverMap_mk]
  exact hP.lift_eq_one hr

theorem multiplier_of_kernel [Finite X] (hP : IsPresentation g R)
    (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) (hwg : ∀ i, FreeGroup.lift g (w i) = g i) {M : ℕ}
    (hfin : Finite (relatorImages R w)) (hM : Nat.card (relatorImages R w) ≤ M) {E : Type*}
    [Group E] (ψ : PresentedCover R w →* E) (K₀ : Subgroup E) (hK₀ : Nat.card K₀ = M)
    (hK : K₀ ≤ (relatorImages R w).map ψ) :
    Nonempty (griessHopfMultiplier X ≃* K₀) := by
  have hker := ker_coverMap_le_closure hP hwg
  have hfk : Finite (coverMap hP hwg).ker := Finite.of_injective _ (Subgroup.inclusion_injective hker)
  have hck : Nat.card (coverMap hP hwg).ker ≤ M :=
    (Subgroup.card_le_of_le hker).trans hM
  have hq : Finite (PresentedCover R w ⧸ (coverMap hP hwg).ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivOfSurjective _
      (coverMap_surjective hP hwg)).toEquiv.symm
  have hP' : Finite (PresentedCover R w) := Finite.of_subgroup_quotient (coverMap hP hwg).ker
  have hcard : Nat.card (PresentedCover R w) ≤ M * Nat.card X := by
    rw [(coverMap hP hwg).ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (coverMap_surjective hP hwg)).toEquiv,
      mul_comm]
    exact Nat.mul_le_mul_right _ hck
  have he : ∀ r ∈ coverRelators R w, FreeGroup.lift (fun i => ψ (PresentedGroup.of i)) r = 1 := by
    intro r hr
    have hl : FreeGroup.lift (fun i => ψ (PresentedGroup.of i)) =
        ψ.comp (PresentedGroup.mk (coverRelators R w)) :=
      FreeGroup.ext_hom _ _ fun _ => by simp [PresentedGroup.of]
    rw [hl, MonoidHom.comp_apply, PresentedGroup.one_of_mem hr, map_one]
  have hψ : PresentedGroup.toGroup he = ψ := PresentedGroup.ext fun i => by
    rw [PresentedGroup.toGroup.of]
  refine nonempty_griessHopfMultiplier_mulEquiv_of_card_le hP hw hwg hcard he hK₀ ?_
  rw [hψ]
  exact hK.trans (map_mono (relatorImages_le_ker hP hwg))

theorem multiplier_of_kernel' [Finite X] (hP : IsPresentation g R)
    (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) (hwg : ∀ i, FreeGroup.lift g (w i) = g i)
    {S : Set (FreeGroup ι)} (hS : coverRelators R w = S) {M : ℕ}
    (hfin : Finite (closure (PresentedGroup.mk S '' R)))
    (hM : Nat.card (closure (PresentedGroup.mk S '' R)) ≤ M) {E : Type*} [Group E]
    (ψ : PresentedGroup S →* E) (K₀ : Subgroup E) (hK₀ : Nat.card K₀ = M)
    (hK : K₀ ≤ (closure (PresentedGroup.mk S '' R)).map ψ) :
    Nonempty (griessHopfMultiplier X ≃* K₀) := by
  subst hS
  exact multiplier_of_kernel hP hw hwg hfin hM ψ K₀ hK₀ hK

end CFSG.LieType.Multipliers

end
