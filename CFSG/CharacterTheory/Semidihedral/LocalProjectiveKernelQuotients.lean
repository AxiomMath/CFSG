module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public noncomputable section

namespace CFSG.Semidihedral.LocalProjectiveKernelQuotients

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

universe u

variable {G : Type u} [Group G]

abbrev originalCentralizerSubgroup (i : G) (W : Subgroup G) : Subgroup (C i) :=
  W.comap (C i).subtype

abbrev originalProjectiveComposite (i : G) : C i →* Gamma i :=
  (barKappa i).comp (nu i)

abbrev originalLayer (i : G) : Subgroup (Gamma i) :=
  CFSG.generalizedFitting (Gamma i)

abbrev originalLayerPreimage (i : G) : Subgroup (C i) :=
  ((originalLayer i).comap (barKappa i)).comap (nu i)

abbrev originalAmbientLayerPreimage (i : G) : Subgroup G :=
  (originalLayerPreimage i).map (C i).subtype

abbrev originalAmbientOddCore (i : G) : Subgroup G :=
  (N i).map (C i).subtype

abbrev originalAmbientInverted (i : G) (U : Subgroup (N i)) : Subgroup G :=
  (U.map (N i).subtype).map (C i).subtype

abbrev originalInvertedKernel (i : G) (W : Subgroup G) (U : Subgroup (N i)) : Subgroup W :=
  (W ⊓ originalAmbientInverted i U).comap W.subtype

@[expose] def originalCentralizerEquiv (i : G) (W : Subgroup G) (hWC : W ≤ C i) :
    W ≃* originalCentralizerSubgroup i W where
  toFun w := ⟨Subgroup.inclusion hWC w, w.property⟩
  invFun w := ⟨((w : C i) : G), w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem originalCentralizerEquiv_card (i : G) (W : Subgroup G) (hWC : W ≤ C i) :
    Nat.card (originalCentralizerSubgroup i W) = Nat.card W :=
  Nat.card_congr (originalCentralizerEquiv i W hWC).toEquiv.symm

theorem originalCentralizerSubgroup_map (i : G) (W : Subgroup G) (hWC : W ≤ C i) :
    (originalCentralizerSubgroup i W).map (C i).subtype = W := by
  rw [originalCentralizerSubgroup, Subgroup.map_comap_eq, Subgroup.range_subtype,
    inf_eq_right.mpr hWC]

@[expose] def originalCentralizerRestriction (i : G) (W : Subgroup G) :
    originalCentralizerSubgroup i W →* Gamma i :=
  (originalProjectiveComposite i).domRestrict (originalCentralizerSubgroup i W)

@[expose] def originalProjectiveRestriction (i : G) (W : Subgroup G) (hWC : W ≤ C i) :
    W →* Gamma i :=
  (originalProjectiveComposite i).comp (Subgroup.inclusion hWC)

theorem originalProjectiveRestriction_apply (i : G) (W : Subgroup G) (hWC : W ≤ C i)
    (w : W) :
    originalProjectiveRestriction i W hWC w = barKappa i (nu i (Subgroup.inclusion hWC w)) :=
  rfl

theorem originalCentralizerRestriction_apply (i : G) (W : Subgroup G)
    (w : originalCentralizerSubgroup i W) :
    originalCentralizerRestriction i W w = barKappa i (nu i (w : C i)) := rfl

theorem originalCentralizerRestriction_transport (i : G) (W : Subgroup G)
    (hWC : W ≤ C i) (w : W) :
    originalCentralizerRestriction i W (originalCentralizerEquiv i W hWC w) =
      originalProjectiveRestriction i W hWC w := rfl

theorem originalProjectiveComposite_ker (i : G) :
    (originalProjectiveComposite i).ker = N i ⊔ Subgroup.zpowers (tInC i) := by
  rw [originalProjectiveComposite, barKappa_comp_nu, QuotientGroup.ker_mk']

theorem original_mem_ambientOddCore (i : G) (x : C i) :
    (x : G) ∈ originalAmbientOddCore i ↔ x ∈ N i := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem original_mem_ambientLayerPreimage (i : G) (x : C i) :
    (x : G) ∈ originalAmbientLayerPreimage i ↔ x ∈ originalLayerPreimage i := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem originalInvertedKernel_map (i : G) (W : Subgroup G) (U : Subgroup (N i)) :
    (originalInvertedKernel i W U).map W.subtype = W ⊓ originalAmbientInverted i U := by
  rw [originalInvertedKernel, Subgroup.map_comap_eq, Subgroup.range_subtype,
    ← inf_assoc, inf_idem]

theorem original_layer_containment_iff (i : G) (W : Subgroup G) (hWC : W ≤ C i) :
    originalCentralizerSubgroup i W ≤ originalLayerPreimage i ↔
      W ≤ originalAmbientLayerPreimage i := by
  constructor
  · intro h x hx
    exact ⟨Subgroup.inclusion hWC (⟨x, hx⟩ : W), h hx, rfl⟩
  · intro h x hx
    exact (original_mem_ambientLayerPreimage i x).mp (h hx)

theorem original_odd_projective_eq_one_iff (i : G) (hi : orderOf i = 2)
    (W : Subgroup G) (hodd : Odd (Nat.card W)) (x : C i) (hxW : (x : G) ∈ W) :
    originalProjectiveComposite i x = 1 ↔ x ∈ N i := by
  constructor
  · intro hx
    have hq : nu i x ∈ Subgroup.zpowers (nu i (tInC i)) := by
      rw [← barKappa_kernel i]
      exact hx
    have hiC : orderOf (tInC i) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hi
    have htwo : orderOf (nu i x) ∣ 2 :=
      (orderOf_dvd_of_mem_zpowers hq).trans
        ((orderOf_map_dvd (nu i) (tInC i)).trans (dvd_of_eq hiC))
    have hcard : orderOf (nu i x) ∣ Nat.card W :=
      (orderOf_map_dvd (nu i) x).trans (by
        rw [← Subgroup.orderOf_coe]
        exact W.orderOf_dvd_natCard hxW)
    have horder : orderOf (nu i x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left htwo hcard
    exact (QuotientGroup.eq_one_iff (N := N i) x).mp (orderOf_eq_one_iff.mp horder)
  · intro hx
    have hnu : nu i x = 1 := (QuotientGroup.eq_one_iff (N := N i) x).mpr hx
    change barKappa i (nu i x) = 1
    rw [hnu, map_one]

theorem originalProjectiveRestriction_ker (i : G) (hi : orderOf i = 2)
    (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W)) :
    (originalProjectiveRestriction i W hWC).ker = (N i).comap (Subgroup.inclusion hWC) := by
  ext w
  exact original_odd_projective_eq_one_iff i hi W hodd (Subgroup.inclusion hWC w) w.property

theorem originalCentralizerRestriction_ker (i : G) (hi : orderOf i = 2)
    (W : Subgroup G) (hodd : Odd (Nat.card W)) :
    (originalCentralizerRestriction i W).ker =
      (N i).comap (originalCentralizerSubgroup i W).subtype := by
  ext w
  exact original_odd_projective_eq_one_iff i hi W hodd (w : C i) w.property

theorem originalCentralizerRestriction_ambient_ker (i : G) (hi : orderOf i = 2)
    (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W)) :
    ((originalCentralizerRestriction i W).ker.map
      (originalCentralizerSubgroup i W).subtype).map (C i).subtype =
        W ⊓ originalAmbientOddCore i := by
  rw [originalCentralizerRestriction_ker i hi W hodd, Subgroup.map_comap_eq,
    Subgroup.range_subtype, Subgroup.map_inf _ _ _ (C i).subtype_injective,
    originalCentralizerSubgroup_map i W hWC]

theorem originalProjectiveRestriction_ambient_ker (i : G) (hi : orderOf i = 2)
    (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W)) :
    (originalProjectiveRestriction i W hWC).ker.map W.subtype =
      W ⊓ originalAmbientOddCore i := by
  rw [originalProjectiveRestriction_ker i hi W hWC hodd]
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, ⟨Subgroup.inclusion hWC w, hw, rfl⟩⟩
  · rintro ⟨hxW, c, hc, hcx⟩
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    change Subgroup.inclusion hWC (⟨x, hxW⟩ : W) ∈ N i
    have he : Subgroup.inclusion hWC (⟨x, hxW⟩ : W) = c := Subtype.ext hcx.symm
    rw [he]
    exact hc

theorem original_inverted_intersection (i : G) (t : C i) (W : Subgroup G)
    (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹) :
    W ⊓ originalAmbientOddCore i = W ⊓ originalAmbientInverted i U := by
  ext x
  constructor
  · rintro ⟨hxW, c, hc, rfl⟩
    have hu : (⟨c, hc⟩ : N i) ∈ U := (hU ⟨c, hc⟩).mpr (hWinv ⟨(c : G), hxW⟩)
    exact ⟨hxW, ⟨c, ⟨⟨c, hc⟩, hu, rfl⟩, rfl⟩⟩
  · rintro ⟨hxW, c, hc, hcx⟩
    obtain ⟨n, hn, rfl⟩ := hc
    exact ⟨hxW, ⟨(n : C i), n.property, hcx⟩⟩

theorem originalProjectiveRestriction_ker_inverted (i : G) (hi : orderOf i = 2)
    (t : C i) (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W))
    (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹) :
    (originalProjectiveRestriction i W hWC).ker = originalInvertedKernel i W U := by
  apply Subgroup.map_injective W.subtype_injective
  rw [originalProjectiveRestriction_ambient_ker i hi W hWC hodd,
    originalInvertedKernel_map, original_inverted_intersection i t W U hU hWinv]

@[expose] def originalLayerRestriction (i : G) (W : Subgroup G) (hWC : W ≤ C i)
    (hWY : W ≤ originalAmbientLayerPreimage i) : W →* originalLayer i :=
  (originalProjectiveRestriction i W hWC).codRestrict (originalLayer i) fun w =>
    (original_mem_ambientLayerPreimage i (Subgroup.inclusion hWC w)).mp (hWY w.property)

theorem originalLayerRestriction_apply (i : G) (W : Subgroup G) (hWC : W ≤ C i)
    (hWY : W ≤ originalAmbientLayerPreimage i) (w : W) :
    (originalLayerRestriction i W hWC hWY w : Gamma i) =
      barKappa i (nu i (Subgroup.inclusion hWC w)) := rfl

theorem originalLayerRestriction_comp_subtype (i : G) (W : Subgroup G) (hWC : W ≤ C i)
    (hWY : W ≤ originalAmbientLayerPreimage i) :
    (originalLayer i).subtype.comp (originalLayerRestriction i W hWC hWY) =
      originalProjectiveRestriction i W hWC := rfl

theorem originalLayerRestriction_ker (i : G) (W : Subgroup G) (hWC : W ≤ C i)
    (hWY : W ≤ originalAmbientLayerPreimage i) :
    (originalLayerRestriction i W hWC hWY).ker =
      (originalProjectiveRestriction i W hWC).ker := by
  exact MonoidHom.ker_codRestrict _ _ _

theorem originalLayerRestriction_ker_inverted (i : G) (hi : orderOf i = 2)
    (t : C i) (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W))
    (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹)
    (hWY : W ≤ originalAmbientLayerPreimage i) :
    (originalLayerRestriction i W hWC hWY).ker = originalInvertedKernel i W U := by
  rw [originalLayerRestriction_ker,
    originalProjectiveRestriction_ker_inverted i hi t W hWC hodd U hU hWinv]

theorem originalInvertedKernel_normal (i : G) (hi : orderOf i = 2)
    (t : C i) (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W))
    (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹) :
    (originalInvertedKernel i W U).Normal := by
  rw [← originalProjectiveRestriction_ker_inverted i hi t W hWC hodd U hU hWinv]
  infer_instance

@[expose] def originalLayerQuotient (i : G) (hi : orderOf i = 2)
    (t : C i) (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W))
    (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹)
    (hWY : W ≤ originalAmbientLayerPreimage i) :
    letI := originalInvertedKernel_normal i hi t W hWC hodd U hU hWinv
    W ⧸ originalInvertedKernel i W U →* originalLayer i := by
  letI := originalInvertedKernel_normal i hi t W hWC hodd U hU hWinv
  let f := originalLayerRestriction i W hWC hWY
  let e := QuotientGroup.quotientMulEquivOfEq
    (originalLayerRestriction_ker_inverted i hi t W hWC hodd U hU hWinv hWY).symm
  exact f.range.subtype.comp ((QuotientGroup.quotientKerEquivRange f).toMonoidHom.comp
    e.toMonoidHom)

theorem originalLayerQuotient_injective (i : G) (hi : orderOf i = 2)
    (t : C i) (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W))
    (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹)
    (hWY : W ≤ originalAmbientLayerPreimage i) :
    letI := originalInvertedKernel_normal i hi t W hWC hodd U hU hWinv
    Function.Injective (originalLayerQuotient i hi t W hWC hodd U hU hWinv hWY) := by
  let := originalInvertedKernel_normal i hi t W hWC hodd U hU hWinv
  exact (originalLayerRestriction i W hWC hWY).range.subtype_injective.comp
    ((QuotientGroup.quotientKerEquivRange _).injective.comp
      (QuotientGroup.quotientMulEquivOfEq _).injective)

theorem originalLayerQuotient_apply (i : G) (hi : orderOf i = 2)
    (t : C i) (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W))
    (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹)
    (hWY : W ≤ originalAmbientLayerPreimage i) (w : W) :
    letI := originalInvertedKernel_normal i hi t W hWC hodd U hU hWinv
    (originalLayerQuotient i hi t W hWC hodd U hU hWinv hWY (QuotientGroup.mk w) : Gamma i) =
      barKappa i (nu i (Subgroup.inclusion hWC w)) := rfl

theorem originalLayerRestriction_injective_of_inter_eq_bot
    (i : G) (hi : orderOf i = 2) (t : C i) (W : Subgroup G) (hWC : W ≤ C i)
    (hodd : Odd (Nat.card W)) (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹)
    (hWY : W ≤ originalAmbientLayerPreimage i)
    (hinter : W ⊓ originalAmbientInverted i U = ⊥) :
    Function.Injective (originalLayerRestriction i W hWC hWY) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [originalLayerRestriction_ker_inverted i hi t W hWC hodd U hU hWinv hWY]
  apply Subgroup.map_injective W.subtype_injective
  rw [originalInvertedKernel_map, hinter, Subgroup.map_bot]

theorem original_local_projective_kernel_quotient_toolkit
    (i : G) (hi : orderOf i = 2) (t : C i) (W : Subgroup G) (hWC : W ≤ C i)
    (hodd : Odd (Nat.card W)) (U : Subgroup (N i))
    (hU : ∀ n : N i, n ∈ U ↔
      (t : G) * ((n : C i) : G) * (t : G)⁻¹ = (((n : C i) : G))⁻¹)
    (hWinv : ∀ w : W, (t : G) * (w : G) * (t : G)⁻¹ = (w : G)⁻¹)
    (hWY : W ≤ originalAmbientLayerPreimage i) :
    letI := originalInvertedKernel_normal i hi t W hWC hodd U hU hWinv
    (∀ w : W, originalProjectiveRestriction i W hWC w =
      barKappa i (nu i (Subgroup.inclusion hWC w))) ∧
    (originalProjectiveRestriction i W hWC).ker = (N i).comap (Subgroup.inclusion hWC) ∧
    (originalProjectiveRestriction i W hWC).ker.map W.subtype =
      W ⊓ originalAmbientOddCore i ∧
    W ⊓ originalAmbientOddCore i = W ⊓ originalAmbientInverted i U ∧
    (originalLayerRestriction i W hWC hWY).ker =
      (W ⊓ originalAmbientInverted i U).comap W.subtype ∧
    ∃ q : W ⧸ (W ⊓ originalAmbientInverted i U).comap W.subtype →* originalLayer i,
      Function.Injective q ∧ ∀ w : W, (q (QuotientGroup.mk w) : Gamma i) =
        barKappa i (nu i (Subgroup.inclusion hWC w)) := by
  refine ⟨originalProjectiveRestriction_apply i W hWC,
    originalProjectiveRestriction_ker i hi W hWC hodd,
    originalProjectiveRestriction_ambient_ker i hi W hWC hodd,
    original_inverted_intersection i t W U hU hWinv,
    originalLayerRestriction_ker_inverted i hi t W hWC hodd U hU hWinv hWY,
    originalLayerQuotient i hi t W hWC hodd U hU hWinv hWY,
    originalLayerQuotient_injective i hi t W hWC hodd U hU hWinv hWY, ?_⟩
  exact originalLayerQuotient_apply i hi t W hWC hodd U hU hWinv hWY

end CFSG.Semidihedral.LocalProjectiveKernelQuotients
