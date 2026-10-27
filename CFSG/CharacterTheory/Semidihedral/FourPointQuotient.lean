module

public import CFSG.CharacterTheory.Semidihedral.ReducedQuotients
public import CFSG.CharacterTheory.Semidihedral.CentralizerAlternatives
public import CFSG.CharacterTheory.Semidihedral.FourPointLifts

public section

namespace CFSG.Semidihedral.FourPointQuotient

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual
open CFSG.Semidihedral.CoreResidual CFSG.Semidihedral.ReducedQuotients
open CFSG.Semidihedral.CentralizerAlternatives

variable {G : Type*} [Group G]

abbrev centralizerCoreQuotient (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :=
  involutionCentralizer n S f ⧸ pPrimeCore 2 (involutionCentralizer n S f)

@[expose] def coreResidual (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Subgroup (centralizerCoreQuotient n S f) :=
  (oddResidual n S f).map (QuotientGroup.mk' (pPrimeCore 2 (involutionCentralizer n S f)))

@[expose] def coreInvolution (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : centralizerCoreQuotient n S f :=
  QuotientGroup.mk' (pPrimeCore 2 (involutionCentralizer n S f)) (centralInvolution n S f)

theorem coreInvolution_mem_center (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    coreInvolution n S f ∈ Subgroup.center (centralizerCoreQuotient n S f) :=
  Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
    (Subgroup.mem_map_of_mem _ (centralInvolution_mem_center n S f))

theorem coreInvolution_order [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : orderOf (coreInvolution n S f) = 2 := by
  apply coreQuotient_involution_order (centralizerSylow n hn S f) (centralInvolution n S f)
  · rw [← centralizerCoordinates_z n hn S f]
    exact (centralizerCoordinates n hn S f (z n)).property
  · exact centralInvolution_order n hn S f

@[expose] def fullReduction (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    centralizerCoreQuotient n S f →*
      involutionCentralizer n S f ⧸ centralizerFullKernel n S f :=
  QuotientGroup.lift (pPrimeCore 2 (involutionCentralizer n S f))
    (QuotientGroup.mk' (centralizerFullKernel n S f))
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)

theorem fullReduction_coe (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (x : involutionCentralizer n S f) :
    fullReduction n S f (QuotientGroup.mk' (pPrimeCore 2 (involutionCentralizer n S f)) x) =
      QuotientGroup.mk' (centralizerFullKernel n S f) x := rfl

theorem fullReduction_surjective (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Function.Surjective (fullReduction n S f) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective _) _

theorem fullReduction_ker (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    (fullReduction n S f).ker = Subgroup.zpowers (coreInvolution n S f) := by
  rw [fullReduction, QuotientGroup.ker_lift, QuotientGroup.ker_mk', centralizerFullKernel,
    Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
    centralizerZ, MonoidHom.map_zpowers]
  rfl

theorem coreInvolution_mem_coreResidual [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    coreInvolution n S f ∈ coreResidual n S f :=
  Subgroup.mem_map_of_mem _ (centralInvolution_mem_oddResidual n hn S f hG)

theorem fullReduction_coreResidual_map (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    (coreResidual n S f).map (fullReduction n S f) = reducedResidual n S f := by
  rw [coreResidual, Subgroup.map_map]
  rfl

theorem fullReduction_residual_preimage [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    (reducedResidual n S f).comap (fullReduction n S f) = coreResidual n S f := by
  rw [← fullReduction_coreResidual_map, Subgroup.comap_map_eq_self]
  rw [fullReduction_ker]
  exact Subgroup.zpowers_le.mpr (coreInvolution_mem_coreResidual n hn S f hG)

@[expose] def fourPointProjection (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    centralizerCoreQuotient n S f →* Equiv.Perm (Fin 4) :=
  φ.toMonoidHom.comp (fullReduction n S f)

theorem fourPointProjection_surjective (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    Function.Surjective (fourPointProjection n S f φ) :=
  φ.surjective.comp (fullReduction_surjective n S f)

theorem fourPointProjection_ker (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    (fourPointProjection n S f φ).ker = Subgroup.zpowers (coreInvolution n S f) := by
  rw [fourPointProjection, MonoidHom.ker_comp_of_injective _ _ φ.injective,
    fullReduction_ker]

theorem fourPointProjection_coreResidual_map [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    (coreResidual n S f).map (fourPointProjection n S f φ) = alternatingGroup (Fin 4) := by
  rw [fourPointProjection, ← Subgroup.map_map, fullReduction_coreResidual_map]
  exact image_index_two_eq_alternating _ (reducedResidual_index n hn S f hG) φ

theorem fourPointProjection_alternating_preimage [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    (alternatingGroup (Fin 4)).comap (fourPointProjection n S f φ) = coreResidual n S f := by
  rw [← fourPointProjection_coreResidual_map n hn S f hG φ, Subgroup.comap_map_eq_self]
  rw [fourPointProjection_ker]
  exact Subgroup.zpowers_le.mpr (coreInvolution_mem_coreResidual n hn S f hG)

theorem fourPoint_parameter [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    n = 4 :=
  n_eq_four_of_symmetricFour n hn (reducedCentralizerSylow n hn S f)
    (reducedCentralizerDihedralEquiv n hn S f).symm φ


theorem fourKlein_le_alternating :
    FourPointLifts.fourKlein ≤ alternatingGroup (Fin 4) := by
  intro g hg
  rcases (FourPointLifts.mem_fourKlein g).mp hg with rfl | rfl | rfl | rfl <;>
    simp [Equiv.Perm.mem_alternatingGroup, map_mul]

theorem fourKlein_card : Nat.card FourPointLifts.fourKlein = 4 := by
  change Nat.card ({1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2} :
      Set (Equiv.Perm (Fin 4))) = 4
  rw [Nat.card_coe_set_eq]
  simp [Set.ncard_insert_of_notMem, Set.mem_insert_iff, Set.mem_singleton_iff,
    show (1 : Equiv.Perm (Fin 4)) ≠ Equiv.swap 0 1 * Equiv.swap 2 3 by decide,
    show (1 : Equiv.Perm (Fin 4)) ≠ Equiv.swap 0 2 * Equiv.swap 1 3 by decide,
    show (1 : Equiv.Perm (Fin 4)) ≠ Equiv.swap 0 3 * Equiv.swap 1 2 by decide,
    show Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ≠ Equiv.swap 0 2 * Equiv.swap 1 3 by decide,
    show Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ≠ Equiv.swap 0 3 * Equiv.swap 1 2 by decide,
    show Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3 ≠ Equiv.swap 0 3 * Equiv.swap 1 2 by decide]

theorem nativeKlein_map_eq_fourKlein :
    (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype =
      FourPointLifts.fourKlein := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    refine Subgroup.mem_map.mpr ⟨⟨g, fourKlein_le_alternating hg⟩, ?_, rfl⟩
    rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rcases (FourPointLifts.mem_fourKlein g).mp hg with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide))
    · exact Or.inr (Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide))
    · exact Or.inr (Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide))
  · rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 4)).subtype_injective,
      alternatingGroup.kleinFour_card_of_card_eq_four (by simp), fourKlein_card]

theorem every_coreResidualSylow_quaternion [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) (P : Sylow 2 (coreResidual n S f)) :
    Nonempty (P ≃* QuaternionGroup (2 ^ (n - 3))) := by
  let e : (oddResidual n S f ⧸ pPrimeCore 2 (oddResidual n S f)) ≃*
      coreResidual n S f := primeResidualCoreQuotientEquiv 2
  let T := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨d⟩ := every_residualCoreQuotientSylow_quaternion n hn S f hG T
  exact ⟨(sylowEquivMap P e.symm).trans d⟩

@[expose] def residualFourPointProjection [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    coreResidual n S f →* alternatingGroup (Fin 4) :=
  ((MulEquiv.subgroupCongr (fourPointProjection_coreResidual_map n hn S f hG φ)).toMonoidHom).comp
    ((fourPointProjection n S f φ).subgroupMap (coreResidual n S f))

theorem residualFourPointProjection_coe [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4))
    (x : coreResidual n S f) :
    (residualFourPointProjection n hn S f hG φ x : Equiv.Perm (Fin 4)) =
      fourPointProjection n S f φ x := rfl

theorem residualFourPointProjection_surjective [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    Function.Surjective (residualFourPointProjection n hn S f hG φ) :=
  (MulEquiv.subgroupCongr (fourPointProjection_coreResidual_map n hn S f hG φ)).surjective.comp
    ((fourPointProjection n S f φ).subgroupMap_surjective (coreResidual n S f))

theorem residualFourPointProjection_ker [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    (residualFourPointProjection n hn S f hG φ).ker =
      (Subgroup.zpowers (coreInvolution n S f)).subgroupOf (coreResidual n S f) := by
  rw [residualFourPointProjection, MonoidHom.ker_comp_of_injective _ _
    (MulEquiv.subgroupCongr (fourPointProjection_coreResidual_map n hn S f hG φ)).injective,
    Subgroup.ker_subgroupMap, fourPointProjection_ker]

theorem odd_square_one_isSwap (g : Equiv.Perm (Fin 4))
    (hg : g ^ 2 = 1) (hodd : g ∉ alternatingGroup (Fin 4)) : g.IsSwap := by
  have h : ∀ g : Equiv.Perm (Fin 4), g ^ 2 = 1 → Equiv.Perm.sign g ≠ 1 →
      ∃ i j : Fin 4, i ≠ j ∧ g = Equiv.swap i j := by decide
  rcases h g hg (fun hs => hodd (Equiv.Perm.mem_alternatingGroup.mpr hs)) with ⟨i, j, hij, heq⟩
  exact ⟨i, j, hij, heq⟩


theorem residualFourPointProjection_ker_isPGroup [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    IsPGroup 2 (residualFourPointProjection n hn S f hG φ).ker := by
  rw [residualFourPointProjection_ker]
  have hz : IsPGroup 2 (Subgroup.zpowers (coreInvolution n S f)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, coreInvolution_order n hn S f]; norm_num)
  exact hz.comap_subtype

theorem fourKlein_preimage_eq_sylow_image [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    ∃ P : Sylow 2 (coreResidual n S f),
      (P : Subgroup (coreResidual n S f)).map (coreResidual n S f).subtype =
        FourPointLifts.fourKlein.comap (fourPointProjection n S f φ) := by
  let ρ := residualFourPointProjection n hn S f hG φ
  let T : Sylow 2 (alternatingGroup (Fin 4)) := Classical.choice Sylow.nonempty
  have hT : (T : Subgroup (alternatingGroup (Fin 4))) = alternatingGroup.kleinFour (Fin 4) :=
    alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by simp) T
  have hρ := residualFourPointProjection_surjective n hn S f hG φ
  let P := T.comapOfKerIsPGroup ρ
    (residualFourPointProjection_ker_isPGroup n hn S f hG φ)
    (by rw [MonoidHom.range_eq_top.mpr hρ]; exact le_top)
  refine ⟨P, ?_⟩
  rw [Sylow.coe_comapOfKerIsPGroup, hT]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change fourPointProjection n S f φ y ∈ FourPointLifts.fourKlein
    rw [← nativeKlein_map_eq_fourKlein]
    exact Subgroup.mem_map.mpr ⟨ρ y, hy, rfl⟩
  · intro hx
    have hxL : x ∈ coreResidual n S f := by
      rw [← fourPointProjection_alternating_preimage n hn S f hG φ]
      exact fourKlein_le_alternating hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, ?_, rfl⟩
    change ρ ⟨x, hxL⟩ ∈ alternatingGroup.kleinFour (Fin 4)
    have hxV : (ρ ⟨x, hxL⟩ : Equiv.Perm (Fin 4)) ∈
        (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype :=
      nativeKlein_map_eq_fourKlein.symm ▸ hx
    rcases Subgroup.mem_map.mp hxV with ⟨a, ha, he⟩
    have he' : a = ρ ⟨x, hxL⟩ := Subtype.ext he
    exact he' ▸ ha

theorem fourKlein_preimage_quaternion [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    Nonempty (FourPointLifts.fourKlein.comap (fourPointProjection n S f φ) ≃* QuaternionGroup 2) := by
  obtain ⟨P, hP⟩ := fourKlein_preimage_eq_sylow_image n hn S f hG φ
  obtain ⟨d⟩ := every_coreResidualSylow_quaternion n hn S f hG P
  have hparam : 2 ^ (n - 3) = 2 := by rw [fourPoint_parameter n hn S f φ]; norm_num
  rw [hparam] at d
  have e : (P : Subgroup (coreResidual n S f)) ≃*
      (P : Subgroup (coreResidual n S f)).map (coreResidual n S f).subtype :=
    MulEquiv.ofBijective ((coreResidual n S f).subtype.subgroupMap (P : Subgroup _))
      ⟨((coreResidual n S f).subtype.subgroupMap_injective _ Subtype.val_injective),
        ((coreResidual n S f).subtype.subgroupMap_surjective _)⟩
  exact ⟨(MulEquiv.subgroupCongr hP).symm.trans (e.symm.trans d)⟩

theorem exists_original_involution_swap_lift [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (φ : (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) ≃* Equiv.Perm (Fin 4)) :
    ∃ u : centralizerCoreQuotient n S f,
      orderOf u = 2 ∧ (fourPointProjection n S f φ u).IsSwap := by
  let s₀ : involutionCentralizer n S f := centralizerCoordinates n hn S f (s n)
  let u : centralizerCoreQuotient n S f := QuotientGroup.mk' (pPrimeCore 2 _) s₀
  have hu : orderOf u = 2 := coreQuotient_involution_order (centralizerSylow n hn S f) s₀
    (centralizerCoordinates n hn S f (s n)).property (s_order n hn S f)
  have hsL : u ∉ coreResidual n S f := by
    intro hs
    have hpre : (coreResidual n S f).comap (QuotientGroup.mk' (pPrimeCore 2 _)) =
        oddResidual n S f := by
      rw [coreResidual, Subgroup.comap_map_eq_self]
      rw [QuotientGroup.ker_mk']
      exact centralizerCore_le_residual n S f
    have hs' : s₀ ∈ (coreResidual n S f).comap (QuotientGroup.mk' (pPrimeCore 2 _)) := hs
    rw [hpre] at hs'
    exact s_not_mem_oddResidual n hn S f hG hs'
  refine ⟨u, hu, odd_square_one_isSwap _ ?_ ?_⟩
  · rw [← map_pow, FourPointLifts.square_eq_one_of_order_two u hu, map_one]
  · intro ha
    apply hsL
    rw [← fourPointProjection_alternating_preimage n hn S f hG φ]
    exact ha

end CFSG.Semidihedral.FourPointQuotient
