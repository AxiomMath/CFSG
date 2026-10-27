module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourFrobenius
public import CFSG.LieType.Chevalley.C2E6MinusSixForm
public import CFSG.LieType.Chevalley.C2E6MinusSixBase
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module Matrix CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem coe_fixed_L_uPlane (j : Fin 27) :
    (L (uPlane j) : Set W) ∩ (W₀ : Set W) = {0, vP j} := by
  ext x
  have := congrArg (fun S : Submodule (ZMod 2) W => x ∈ S) (fixed_L_uPlane j)
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, eq_iff_iff] at this
  rw [Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe, this, mem_span_singleton_zmod_two]
  simp

theorem ncard_L_inter_W₀ {P : Submodule K V} (hP : IsTotallyIsotropic P)
    (h2 : finrank K P = 2) : ((L P : Set W) ∩ (W₀ : Set W)).ncard = 2 := by
  obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
  rw [coe_fixed_L_uPlane, Set.ncard_pair (vP_ne_zero j).symm]

theorem pointMap_eq_span {P : Submodule K V} (hP : IsTotallyIsotropic P)
    (h2 : finrank K P = 2) {v : W} (hv : v ∈ L P) (hv₀ : v ∈ W₀) (hv0 : v ≠ 0) :
    pointMap P = (ZMod 2) ∙ psiLin v := by
  obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
  have hmem : v ∈ (L (uPlane j) : Set W) ∩ (W₀ : Set W) := ⟨hv, hv₀⟩
  rw [coe_fixed_L_uPlane] at hmem
  rcases hmem with h | h
  · exact absurd h hv0
  · rw [Set.mem_singleton_iff] at h
    rw [h, pointMap_uPlane, psiLin_vP]
    rfl

theorem lw₁_ne_lw₂ (k : Fin 45) : lw₁ k ≠ lw₂ k := fun h =>
  nPt_ne_mPt k (ptVec_injective (by rw [← psiLin_lw₁, ← psiLin_lw₂, h]))

theorem lw₁_ne_zero (k : Fin 45) : lw₁ k ≠ 0 := fun h =>
  ptVec_ne_zero (nPt k) (by rw [← psiLin_lw₁, h, map_zero])

theorem lw₂_ne_zero (k : Fin 45) : lw₂ k ≠ 0 := fun h =>
  ptVec_ne_zero (mPt k) (by rw [← psiLin_lw₂, h, map_zero])

theorem finrank_M_inter_W₀ {ℓ : Submodule K V} (hℓ : IsTotallyIsotropic ℓ)
    (h1 : finrank K ℓ = 1) :
    finrank (ZMod 2) ((M ℓ).restrictScalars (ZMod 2) ⊓ W₀ : Submodule (ZMod 2) W) = 2 := by
  obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
  rw [fixed_M_uLine]
  exact finrank_span_pair_zmod_two (lw₁_ne_zero k) (lw₂_ne_zero k) (lw₁_ne_lw₂ k)

theorem Pf_eq_zero_of_mem_M {ℓ : Submodule K V} (hℓ : IsTotallyIsotropic ℓ)
    (h1 : finrank K ℓ = 1) {w : W} (hw : w ∈ M ℓ) (hw₀ : w ∈ W₀) : Pf w = 0 := by
  obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
  have hx : psiLin w ∈ lineMap (uLine k) := ⟨w, ⟨hw, hw₀⟩, rfl⟩
  rw [lineMap_uLine] at hx
  rw [Pf_eq_Q hw₀, isTotallySingular_lnSub (tau k) _ hx, map_zero]

theorem bijOn_pointMap :
    Set.BijOn pointMap {P : Submodule K V | IsTotallyIsotropic P ∧ finrank K P = 2}
      {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 1} := by
  refine ⟨fun P ⟨hP, h2⟩ => ?_, fun P ⟨hP, h2⟩ P' ⟨hP', h2'⟩ h => ?_, fun U ⟨hU, h1⟩ => ?_⟩
  · obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
    rw [Set.mem_ofPred_eq, pointMap_uPlane]
    exact ⟨isTotallySingular_ptSub _, finrank_ptSub _⟩
  · obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
    obtain ⟨j', rfl⟩ := exists_uPlane_eq hP' h2'
    rw [pointMap_uPlane, pointMap_uPlane] at h
    rw [sigma_injective (ptSub_injective h)]
  · obtain ⟨i, rfl⟩ := exists_ptSub_eq hU h1
    obtain ⟨j, rfl⟩ := sigma_surjective i
    exact ⟨uPlane j, ⟨isTotallyIsotropic_uPlane j, finrank_uPlane j⟩, pointMap_uPlane j⟩

theorem bijOn_lineMap :
    Set.BijOn lineMap {ℓ : Submodule K V | IsTotallyIsotropic ℓ ∧ finrank K ℓ = 1}
      {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 2} := by
  refine ⟨fun ℓ ⟨hℓ, h1⟩ => ?_, fun ℓ ⟨hℓ, h1⟩ ℓ' ⟨hℓ', h1'⟩ h => ?_, fun U ⟨hU, h2⟩ => ?_⟩
  · obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
    rw [Set.mem_ofPred_eq, lineMap_uLine]
    exact ⟨isTotallySingular_lnSub _, finrank_lnSub _⟩
  · obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
    obtain ⟨k', rfl⟩ := exists_uLine_eq hℓ' h1'
    rw [lineMap_uLine, lineMap_uLine] at h
    rw [tau_injective (lnSub_injective h)]
  · obtain ⟨j, rfl⟩ := exists_lnSub_eq hU h2
    obtain ⟨k, rfl⟩ := tau_surjective j
    exact ⟨uLine k, ⟨isTotallyIsotropic_uLine k, finrank_uLine k⟩, lineMap_uLine k⟩

theorem le_iff_pointMap_le_lineMap {ℓ P : Submodule K V} (hℓ : IsTotallyIsotropic ℓ)
    (h1 : finrank K ℓ = 1) (hP : IsTotallyIsotropic P) (h2 : finrank K P = 2) :
    ℓ ≤ P ↔ pointMap P ≤ lineMap ℓ := by
  obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
  obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
  rw [uLine_le_uPlane_iff, pointMap_uPlane, lineMap_uLine, ptSub_le_lnSub_iff, uOn_iff_ptOn]

theorem uPlanes_eq_range :
    {P : Submodule K V | IsTotallyIsotropic P ∧ finrank K P = 2} = Set.range uPlane := by
  ext P
  constructor
  · rintro ⟨hP, h2⟩
    obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨isTotallyIsotropic_uPlane j, finrank_uPlane j⟩

theorem uLines_eq_range :
    {ℓ : Submodule K V | IsTotallyIsotropic ℓ ∧ finrank K ℓ = 1} = Set.range uLine := by
  ext ℓ
  constructor
  · rintro ⟨hℓ, h1⟩
    obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨isTotallyIsotropic_uLine k, finrank_uLine k⟩

theorem qPoints_eq_range :
    {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 1} =
      Set.range ptSub := by
  ext U
  constructor
  · rintro ⟨hU, h1⟩
    obtain ⟨i, rfl⟩ := exists_ptSub_eq hU h1
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨isTotallySingular_ptSub i, finrank_ptSub i⟩

theorem qPlanes_eq_range :
    {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 2} =
      Set.range lnSub := by
  ext U
  constructor
  · rintro ⟨hU, h2⟩
    obtain ⟨j, rfl⟩ := exists_lnSub_eq hU h2
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨isTotallySingular_lnSub j, finrank_lnSub j⟩

theorem ncard_uPlanes :
    {P : Submodule K V | IsTotallyIsotropic P ∧ finrank K P = 2}.ncard = 27 := by
  rw [uPlanes_eq_range, Set.ncard_range_of_injective uPlane_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem ncard_uLines :
    {ℓ : Submodule K V | IsTotallyIsotropic ℓ ∧ finrank K ℓ = 1}.ncard = 45 := by
  rw [uLines_eq_range, Set.ncard_range_of_injective uLine_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem ncard_qPoints :
    {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 1}.ncard = 27 := by
  rw [qPoints_eq_range, Set.ncard_range_of_injective ptSub_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem ncard_qPlanes :
    {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 2}.ncard = 45 := by
  rw [qPlanes_eq_range, Set.ncard_range_of_injective lnSub_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem uVec_zero : uVec 0 = u 0 := by decide

theorem uVec_one : uVec 1 = u 3 := by decide

theorem uVec_two : uVec 2 = u 1 := by decide

theorem uVec_six : uVec 6 = u 2 := by decide

theorem pointMap_base₀ : pointMap (Submodule.span K {u 0, u 1}) = (ZMod 2) ∙ e₁ := by
  have : Submodule.span K {u 0, u 1} = uPlane 0 := by
    rw [uPlane, show plA 0 = 0 from rfl, show plB 0 = 2 from rfl, uVec_zero, uVec_two]
  rw [this, pointMap_uPlane, show sigma 0 = 0 from rfl, ptSub, ptVec_zero]

theorem pointMap_base₁ : pointMap (Submodule.span K {u 2, u 3}) = (ZMod 2) ∙ f₁ := by
  have : Submodule.span K {u 2, u 3} = uPlane 1 := by
    rw [uPlane, show plA 1 = 6 from rfl, show plB 1 = 1 from rfl, uVec_six, uVec_one]
  rw [this, pointMap_uPlane, show sigma 1 = 2 from rfl, ptSub, ptVec_two]

theorem lineMap_base₀ : lineMap (K ∙ u 0) = Submodule.span (ZMod 2) {e₁, e₂} := by
  rw [← uVec_zero, show K ∙ uVec 0 = uLine 0 from rfl, lineMap_uLine, show tau 0 = 0 from rfl,
    lnSub, show lnA 0 = 0 from rfl, show lnB 0 = 1 from rfl, ptVec_zero, ptVec_one]

theorem lineMap_base₁ : lineMap (K ∙ u 3) = Submodule.span (ZMod 2) {f₁, f₂} := by
  rw [← uVec_one, show K ∙ uVec 1 = uLine 1 from rfl, lineMap_uLine, show tau 1 = 1 from rfl,
    lnSub, show lnA 1 = 2 from rfl, show lnB 1 = 3 from rfl, ptVec_two, ptVec_three]

theorem finrank_two_of_ne_one {x : UVertex} (h : finrank K x.1 ≠ 1) : finrank K x.1 = 2 :=
  x.2.2.resolve_left h

@[expose] def dualMap (x : UVertex) : QVertex :=
  if h : finrank K x.1 = 1 then
    ⟨lineMap x.1, (bijOn_lineMap.mapsTo ⟨x.2.1, h⟩).1,
      Or.inr (bijOn_lineMap.mapsTo ⟨x.2.1, h⟩).2⟩
  else
    ⟨pointMap x.1, (bijOn_pointMap.mapsTo ⟨x.2.1, finrank_two_of_ne_one h⟩).1,
      Or.inl (bijOn_pointMap.mapsTo ⟨x.2.1, finrank_two_of_ne_one h⟩).2⟩

theorem dualMap_of_line {x : UVertex} (h : finrank K x.1 = 1) : (dualMap x).1 = lineMap x.1 := by
  rw [dualMap, dite_eq_left h]

theorem dualMap_of_plane {x : UVertex} (h : finrank K x.1 ≠ 1) :
    (dualMap x).1 = pointMap x.1 := by
  rw [dualMap, dite_eq_right h]

theorem type_dualMap (x : UVertex) : (dualMap x).type = 3 - x.type := by
  simp only [QVertex.type, UVertex.type]
  by_cases h : finrank K x.1 = 1
  · rw [dualMap_of_line h, h, (bijOn_lineMap.mapsTo ⟨x.2.1, h⟩).2]
  · rw [dualMap_of_plane h, finrank_two_of_ne_one h,
      (bijOn_pointMap.mapsTo ⟨x.2.1, finrank_two_of_ne_one h⟩).2]

theorem le_iff_eq_of_finrank {E : Type*} [AddCommGroup E] {F : Type*} [Field F] [Module F E]
    [FiniteDimensional F E] {U U' : Submodule F E} (h : finrank F U = finrank F U') :
    (U ≤ U' ∨ U' ≤ U) ↔ U = U' := by
  constructor
  · rintro (hle | hle)
    · exact Submodule.eq_of_le_of_finrank_eq hle h
    · exact (Submodule.eq_of_le_of_finrank_eq hle h.symm).symm
  · rintro rfl
    exact Or.inl le_rfl

theorem not_le_of_finrank_lt {E : Type*} [AddCommGroup E] {F : Type*} [Field F] [Module F E]
    [FiniteDimensional F E] {U U' : Submodule F E} (h : finrank F U' < finrank F U) :
    ¬ U ≤ U' := fun hle => absurd (Submodule.finrank_mono hle) (not_le.mpr h)

theorem incident_dualMap_iff (x y : UVertex) :
    (dualMap x).Incident (dualMap y) ↔ x.Incident y := by
  simp only [QVertex.Incident, UVertex.Incident]
  by_cases hx : finrank K x.1 = 1 <;> by_cases hy : finrank K y.1 = 1
  · have hx' := bijOn_lineMap.mapsTo ⟨x.2.1, hx⟩
    have hy' := bijOn_lineMap.mapsTo ⟨y.2.1, hy⟩
    rw [dualMap_of_line hx, dualMap_of_line hy, le_iff_eq_of_finrank (hx'.2.trans hy'.2.symm),
      le_iff_eq_of_finrank (hx.trans hy.symm)]
    exact ⟨fun h => bijOn_lineMap.injOn ⟨x.2.1, hx⟩ ⟨y.2.1, hy⟩ h, fun h => h ▸ rfl⟩
  · have hy2 := finrank_two_of_ne_one hy
    have hx' := bijOn_lineMap.mapsTo ⟨x.2.1, hx⟩
    have hy' := bijOn_pointMap.mapsTo ⟨y.2.1, hy2⟩
    rw [dualMap_of_line hx, dualMap_of_plane hy,
      or_iff_right (not_le_of_finrank_lt (by rw [hx'.2, hy'.2]; omega)),
      or_iff_left (not_le_of_finrank_lt (by rw [hx, hy2]; omega))]
    exact (le_iff_pointMap_le_lineMap x.2.1 hx y.2.1 hy2).symm
  · have hx2 := finrank_two_of_ne_one hx
    have hx' := bijOn_pointMap.mapsTo ⟨x.2.1, hx2⟩
    have hy' := bijOn_lineMap.mapsTo ⟨y.2.1, hy⟩
    rw [dualMap_of_plane hx, dualMap_of_line hy,
      or_iff_left (not_le_of_finrank_lt (by rw [hx'.2, hy'.2]; omega)),
      or_iff_right (not_le_of_finrank_lt (by rw [hy, hx2]; omega))]
    exact (le_iff_pointMap_le_lineMap y.2.1 hy x.2.1 hx2).symm
  · have hx2 := finrank_two_of_ne_one hx
    have hy2 := finrank_two_of_ne_one hy
    have hx' := bijOn_pointMap.mapsTo ⟨x.2.1, hx2⟩
    have hy' := bijOn_pointMap.mapsTo ⟨y.2.1, hy2⟩
    rw [dualMap_of_plane hx, dualMap_of_plane hy,
      le_iff_eq_of_finrank (hx'.2.trans hy'.2.symm), le_iff_eq_of_finrank (hx2.trans hy2.symm)]
    exact ⟨fun h => bijOn_pointMap.injOn ⟨x.2.1, hx2⟩ ⟨y.2.1, hy2⟩ h, fun h => h ▸ rfl⟩

theorem dualMap_bijective : Function.Bijective dualMap := by
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · have ht := congrArg QVertex.type h
    rw [type_dualMap, type_dualMap] at ht
    have hxy : x.type = y.type := by
      simp only [UVertex.type] at ht ⊢
      rcases x.2.2 with hx | hx <;> rcases y.2.2 with hy | hy <;> omega
    apply Subtype.ext
    simp only [UVertex.type] at hxy
    by_cases hx : finrank K x.1 = 1
    · have hy : finrank K y.1 = 1 := hxy ▸ hx
      have := congrArg Subtype.val h
      rw [dualMap_of_line hx, dualMap_of_line hy] at this
      exact bijOn_lineMap.injOn ⟨x.2.1, hx⟩ ⟨y.2.1, hy⟩ this
    · have hy : finrank K y.1 ≠ 1 := hxy ▸ hx
      have := congrArg Subtype.val h
      rw [dualMap_of_plane hx, dualMap_of_plane hy] at this
      exact bijOn_pointMap.injOn ⟨x.2.1, finrank_two_of_ne_one hx⟩
        ⟨y.2.1, finrank_two_of_ne_one hy⟩ this
  · rcases z with ⟨U, hU, h1 | h2⟩
    · obtain ⟨P, ⟨hP, hP2⟩, hPU⟩ := bijOn_pointMap.surjOn ⟨hU, h1⟩
      have hP1 : finrank K P ≠ 1 := by omega
      refine ⟨⟨P, hP, Or.inr hP2⟩, Subtype.ext ?_⟩
      rw [dualMap_of_plane hP1]
      exact hPU
    · obtain ⟨ℓ, ⟨hℓ, hℓ1⟩, hℓU⟩ := bijOn_lineMap.surjOn ⟨hU, h2⟩
      refine ⟨⟨ℓ, hℓ, Or.inl hℓ1⟩, Subtype.ext ?_⟩
      rw [dualMap_of_line hℓ1]
      exact hℓU

@[expose] def dualEquiv : UVertex ≃ QVertex := Equiv.ofBijective dualMap dualMap_bijective

theorem frobW_mem_W₀ {w : W} (hw : w ∈ W₀) : frobW w ∈ W₀ := by
  rw [mem_W₀] at hw ⊢
  rw [T_frobW, hw]

theorem unitary_four_exterior_square_incidence_isomorphism :
    (∀ w : W₀, Pf w.1 = algebraMap (ZMod 2) K (Q (Ψ w))) ∧
    (QuadraticMap.polarBilin Q).Nondegenerate ∧ Q.Nondegenerate ∧
    Nonempty (QuadraticMap.IsometryEquiv Q
      (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1)) ∧
    ((∃ U : Submodule (ZMod 2) X, IsTotallySingular U ∧ finrank (ZMod 2) U = 2) ∧
      ∀ U : Submodule (ZMod 2) X, IsTotallySingular U → finrank (ZMod 2) U ≤ 2) ∧
    (∀ P : Submodule K V, IsTotallyIsotropic P → finrank K P = 2 →
      ((L P : Set W) ∩ (W₀ : Set W)).ncard = 2 ∧
      ∀ v ∈ L P, ∀ hv : v ∈ W₀, v ≠ 0 → pointMap P = (ZMod 2) ∙ Ψ ⟨v, hv⟩) ∧
    (∀ ℓ : Submodule K V, IsTotallyIsotropic ℓ → finrank K ℓ = 1 →
      finrank (ZMod 2) ((M ℓ).restrictScalars (ZMod 2) ⊓ W₀ : Submodule (ZMod 2) W) = 2 ∧
      (∀ w ∈ M ℓ, w ∈ W₀ → Pf w = 0) ∧ (lineMap ℓ : Set X) = Ψ '' {w : W₀ | w.1 ∈ M ℓ}) ∧
    Set.BijOn pointMap {P : Submodule K V | IsTotallyIsotropic P ∧ finrank K P = 2}
      {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 1} ∧
    Set.BijOn lineMap {ℓ : Submodule K V | IsTotallyIsotropic ℓ ∧ finrank K ℓ = 1}
      {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 2} ∧
    (∀ ℓ P : Submodule K V, IsTotallyIsotropic ℓ → finrank K ℓ = 1 → IsTotallyIsotropic P →
      finrank K P = 2 → (ℓ ≤ P ↔ pointMap P ≤ lineMap ℓ)) ∧
    (∀ x : UVertex, (dualEquiv x).type = 3 - x.type) ∧
    (∀ x y : UVertex, (dualEquiv x).Incident (dualEquiv y) ↔ x.Incident y) ∧
    {P : Submodule K V | IsTotallyIsotropic P ∧ finrank K P = 2}.ncard = 27 ∧
    {ℓ : Submodule K V | IsTotallyIsotropic ℓ ∧ finrank K ℓ = 1}.ncard = 45 ∧
    {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 1}.ncard = 27 ∧
    {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 2}.ncard = 45 ∧
    (∀ (g : GL (Fin 4) K) (hg : g ∈ SU),
      (∀ u v : V, ext2GL g *ᵥ wedge u v =
        wedge ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ u) ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ v)) ∧
      (∀ w : W, T (ext2GL g *ᵥ w) = ext2GL g *ᵥ T w) ∧
      (∀ w ∈ W₀, ext2GL g *ᵥ w ∈ W₀ ∧ Pf (ext2GL g *ᵥ w) = Pf w) ∧
      (∀ w ∈ W₀, suIso hg (psiLin w) = psiLin (ext2GL g *ᵥ w)) ∧
      (∀ P : Submodule K V, pointMap (P.map (linOf g)) =
        (pointMap P).map ((suIso hg).toLinearEquiv : X →ₗ[ZMod 2] X)) ∧
      ∀ ℓ : Submodule K V, lineMap (ℓ.map (linOf g)) =
        (lineMap ℓ).map ((suIso hg).toLinearEquiv : X →ₗ[ZMod 2] X)) ∧
    (∀ u v : V, frobW (wedge u v) = wedge (frobV u) (frobV v)) ∧
    (∀ w : W, T (frobW w) = frobW (T w)) ∧
    (∀ w ∈ W₀, frobW w ∈ W₀ ∧ Pf (frobW w) = Pf w) ∧
    (∀ w ∈ W₀, frobIso (psiLin w) = psiLin (frobW w)) ∧
    (∀ x : X, frobIso x = ![x 0, x 1, x 2, x 3, x 4 + x 5, x 5]) ∧
    (∀ P : Submodule K V,
      pointMap (P.map frobV) = (pointMap P).map (frobIso.toLinearEquiv : X →ₗ[ZMod 2] X)) ∧
    (∀ ℓ : Submodule K V,
      lineMap (ℓ.map frobV) = (lineMap ℓ).map (frobIso.toLinearEquiv : X →ₗ[ZMod 2] X)) ∧
    pointMap (Submodule.span K {u 0, u 1}) = (ZMod 2) ∙ e₁ ∧
    lineMap (K ∙ u 0) = Submodule.span (ZMod 2) {e₁, e₂} ∧
    pointMap (Submodule.span K {u 2, u 3}) = (ZMod 2) ∙ f₁ ∧
    lineMap (K ∙ u 3) = Submodule.span (ZMod 2) {f₁, f₂} :=
  ⟨fun w => Pf_eq_Q w.2, nondegenerate_polarBilin_Q, nondegenerate_Q,
    ⟨isometryEquivQuadMinus⟩, wittIndex_two,
    fun _ hP h2 => ⟨ncard_L_inter_W₀ hP h2, fun _ hv hv₀ hv0 => pointMap_eq_span hP h2 hv hv₀ hv0⟩,
    fun ℓ hℓ h1 => ⟨finrank_M_inter_W₀ hℓ h1, fun _ hw hw₀ => Pf_eq_zero_of_mem_M hℓ h1 hw hw₀,
      coe_lineMap ℓ⟩,
    bijOn_pointMap, bijOn_lineMap, fun _ _ hℓ h1 hP h2 => le_iff_pointMap_le_lineMap hℓ h1 hP h2,
    fun x => type_dualMap x, fun x y => incident_dualMap_iff x y,
    ncard_uPlanes, ncard_uLines, ncard_qPoints, ncard_qPlanes,
    fun _ hg => ⟨fun u v => ext2_mulVec_wedge _ u v, T_ext2 hg,
      fun w hw => ⟨ext2GL_mem_W₀ hg hw, Pf_ext2GL hg w⟩, fun _ hw => suIso_psiLin hg hw,
      pointMap_map_SU hg, lineMap_map_SU hg⟩,
    frobW_wedge, T_frobW, fun _ hw => ⟨frobW_mem_W₀ hw, Pf_frobLinW hw⟩,
    fun _ hw => frobIso_psiLin hw, frobIso_apply, pointMap_map_frob, lineMap_map_frob,
    pointMap_base₀, lineMap_base₀, pointMap_base₁, lineMap_base₁⟩

end CFSG.LieType.Chevalley.C2E6Overlap
