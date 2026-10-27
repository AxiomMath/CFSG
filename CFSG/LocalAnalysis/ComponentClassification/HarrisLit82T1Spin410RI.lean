module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RO

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def perpEmbLin (b : Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) :
    Module.End K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  LinearMap.id + perpIncl ∘ₗ (b - 1) ∘ₗ perpCoords

theorem perpEmbLin_apply (b : Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K))
    (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    perpEmbLin b x = x + perpIncl (b (perpCoords x) - perpCoords x) := by
  simp [perpEmbLin]

theorem perpCoords_perpEmbLin (b : Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K))
    (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) : perpCoords (perpEmbLin b x) = b (perpCoords x) := by
  rw [perpEmbLin_apply, map_add, perpCoords_perpIncl]
  abel

theorem perpEmbLin_one : perpEmbLin (1 : Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [perpEmbLin_apply, Module.End.one_apply, sub_self, map_zero, add_zero]
  rfl

theorem perpEmbLin_mul (b b' : Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) :
    perpEmbLin (b * b') = perpEmbLin b * perpEmbLin b' := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, perpEmbLin_apply b, perpCoords_perpEmbLin, perpEmbLin_apply,
    perpEmbLin_apply, Module.End.mul_apply, add_assoc, ← map_add]
  congr 2
  abel

theorem coe_mul_coe_symm {M : Type*} [AddCommGroup M] [Module K M] (b : M ≃ₗ[K] M) :
    (b : Module.End K M) * (b.symm : Module.End K M) = 1 :=
  LinearMap.ext fun x => b.apply_symm_apply x

theorem coe_symm_mul_coe {M : Type*} [AddCommGroup M] [Module K M] (b : M ≃ₗ[K] M) :
    (b.symm : Module.End K M) * (b : Module.End K M) = 1 :=
  LinearMap.ext fun x => b.symm_apply_apply x

@[expose] noncomputable def perpEmb :
    ((Fin 1 ⊕ Fin 1 ⊕ Unit → K) ≃ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) →*
      ((Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) where
  toFun b := LinearEquiv.ofLinearMap (perpEmbLin b) (perpEmbLin b.symm)
    (by rw [← Module.End.mul_eq_comp, ← perpEmbLin_mul, coe_mul_coe_symm, perpEmbLin_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← perpEmbLin_mul, coe_symm_mul_coe, perpEmbLin_one]; rfl)
  map_one' := LinearEquiv.ext fun x => by
    show perpEmbLin (1 : Module.End K _) x = x
    rw [perpEmbLin_one]
    rfl
  map_mul' b b' := LinearEquiv.ext fun x => by
    show perpEmbLin ((b * b' : _ ≃ₗ[K] _) : Module.End K _) x = perpEmbLin b (perpEmbLin b' x)
    rw [show ((b * b' : _ ≃ₗ[K] _) : Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) =
      (b : Module.End K _) * (b' : Module.End K _) from rfl, perpEmbLin_mul]
    rfl

theorem perpEmb_apply (b : (Fin 1 ⊕ Fin 1 ⊕ Unit → K) ≃ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K))
    (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) : perpEmb b x = perpEmbLin b x :=
  rfl

theorem quadOdd_three_eq (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    quadOdd 3 K v = v (.inl 0) * v (.inr (.inl 0)) + v (.inl 1) * v (.inr (.inl 1)) +
      quadOdd 1 K (perpCoords v) := by
  rw [quadOdd_apply, quadOdd_apply, Fin.sum_univ_three, Fin.sum_univ_one]
  simp only [perpCoords, LinearMap.funLeft_apply, perpIdx]
  ring

theorem perpIncl_inl (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) {i : Fin 3} (hi : i ≠ 2) :
    perpIncl w (.inl i) = 0 := by
  simp [perpIncl, oddZ, hi]

theorem perpIncl_inr_inl (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) {i : Fin 3} (hi : i ≠ 2) :
    perpIncl w (.inr (.inl i)) = 0 := by
  simp [perpIncl, oddZ, hi]

theorem quadOdd_perpEmbLin {b : Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K)}
    (hb : ∀ w, quadOdd 1 K (b w) = quadOdd 1 K w) (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    quadOdd 3 K (perpEmbLin b x) = quadOdd 3 K x := by
  rw [quadOdd_three_eq, quadOdd_three_eq x, perpCoords_perpEmbLin, hb]
  simp only [perpEmbLin_apply, Pi.add_apply, perpIncl_inl _ (show (0 : Fin 3) ≠ 2 by decide),
    perpIncl_inl _ (show (1 : Fin 3) ≠ 2 by decide),
    perpIncl_inr_inl _ (show (0 : Fin 3) ≠ 2 by decide),
    perpIncl_inr_inl _ (show (1 : Fin 3) ≠ 2 by decide), add_zero]

@[expose] noncomputable def perpEmbO : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K) →*
    TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  (perpEmb.comp (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K)).subtype).codRestrict _
    fun b => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x =>
      quadOdd_perpEmbLin (fun w => CFSG.ClassicalGroups.Orthogonal.map_of_mem b.2 w) x

theorem coe_perpEmbO (b : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K)) :
    ((perpEmbO b : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) :
      (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) = perpEmb b :=
  rfl

theorem polar_perpIncl (u : Fin 1 ⊕ Fin 1 ⊕ Unit → K) (y : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    polar (quadOdd 3 K) (perpIncl u) y = polar (quadOdd 1 K) u (perpCoords y) := by
  simp only [polar, quadOdd_three_eq, map_add, perpCoords_perpIncl, Pi.add_apply,
    perpIncl_inl _ (show (0 : Fin 3) ≠ 2 by decide),
    perpIncl_inl _ (show (1 : Fin 3) ≠ 2 by decide),
    perpIncl_inr_inl _ (show (0 : Fin 3) ≠ 2 by decide),
    perpIncl_inr_inl _ (show (1 : Fin 3) ≠ 2 by decide), zero_add]
  ring

theorem perpEmb_reflection (u : Fin 1 ⊕ Fin 1 ⊕ Unit → K) [Invertible (quadOdd 1 K u)]
    [Invertible (quadOdd 3 K (perpIncl u))] :
    perpEmb (TauCeti.QuadraticMap.reflection (quadOdd 1 K) u) =
      TauCeti.QuadraticMap.reflection (quadOdd 3 K) (perpIncl u) := by
  refine LinearEquiv.ext fun y => ?_
  rw [perpEmb_apply, perpEmbLin_apply, LinearEquiv.coe_coe,
    TauCeti.QuadraticMap.reflection_apply, TauCeti.QuadraticMap.reflection_apply,
    sub_sub_cancel_left, map_neg, map_smul, polar_perpIncl, invOf_eq_inv, invOf_eq_inv,
    quadOdd_perpIncl, sub_eq_add_neg]

section Finite

variable [Finite K] [Invertible (2 : K)]

theorem detSpinorNorm_perpEmbO (b : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K)) :
    detSpinorNorm (nondegenerate_quadOdd 3 K) (perpEmbO b) =
      detSpinorNorm (nondegenerate_quadOdd 1 K) b := by
  have : NeZero (2 : K) := ⟨(isUnit_of_invertible (2 : K)).ne_zero⟩
  have h := TauCeti.QuadraticMap.orthogonalGroup_hom_ext (quadOdd 1 K)
    (nondegenerate_quadOdd 1 K) (f := (detSpinorNorm (nondegenerate_quadOdd 3 K)).comp perpEmbO)
    (g := detSpinorNorm (nondegenerate_quadOdd 1 K)) fun u _ => by
      let _ : Invertible (quadOdd 3 K (perpIncl u)) :=
        invertibleOfNonzero (by rw [quadOdd_perpIncl]; exact (isUnit_of_invertible _).ne_zero)
      have hr : perpEmbO (TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 1 K) u) =
          TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 3 K) (perpIncl u) := by
        apply Subtype.ext
        rw [coe_perpEmbO, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
          TauCeti.QuadraticMap.coe_reflectionOrthogonal, perpEmb_reflection]
      rw [MonoidHom.comp_apply, hr, detSpinorNorm_reflectionOrthogonal,
        detSpinorNorm_reflectionOrthogonal]
      congr 2
      exact Units.ext (by rw [val_unitOfInvertible, val_unitOfInvertible, quadOdd_perpIncl])
  exact DFunLike.congr_fun h b

theorem detSpinorNorm_eq_one_of_mem_elementaryGroup
    {g : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)}
    (hg : (g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadOdd 3 K)) :
    detSpinorNorm (nondegenerate_quadOdd 3 K) g = 1 := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  exact ((orthogonalGroup_index_four (nondegenerate_polarBilin_quadOdd 3 K h2)
    (CFSG.ClassicalGroups.Orthogonal.oddPair_orth (K := K) (i := (0 : Fin 3)) (j := 1)
      (by decide))
    (CFSG.ClassicalGroups.Orthogonal.oddPair_orth (K := K) (i := (0 : Fin 3)) (j := 2)
      (by decide))
    (CFSG.ClassicalGroups.Orthogonal.oddPair_orth (K := K) (i := (1 : Fin 3)) (j := 2)
      (by decide))).2 g).mp hg

end Finite

theorem two_mul_card_ker_le {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) {x : G}
    (hx : f x ≠ 1) : 2 * Nat.card f.ker ≤ Nat.card G := by
  have h := card_ker_mul_card_range f
  have hne : f.range ≠ ⊥ := fun hb => hx (by
    have hmem : f x ∈ f.range := ⟨x, rfl⟩
    rw [hb, mem_bot] at hmem
    exact hmem)
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hr : 2 ≤ Nat.card f.range := (one_lt_card_iff_ne_bot _).mpr hne
  calc 2 * Nat.card f.ker ≤ Nat.card f.range * Nat.card f.ker := Nat.mul_le_mul_right _ hr
    _ = Nat.card G := by rw [mul_comm, h]

section Finite

variable [Finite K] [Invertible (2 : K)]

theorem four_mul_card_ker_detSpinorNorm_le :
    4 * Nat.card (detSpinorNorm (nondegenerate_quadOdd 1 K)).ker ≤
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K)) := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hring : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := (ringChar.spec K 2).2 (by rw [h])
    exact_mod_cast this
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hring
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact ⟨0, by simp⟩)
  set w₁ : Fin 1 ⊕ Fin 1 ⊕ Unit → K := Pi.single (.inr (.inr ())) 1 with hw₁def
  set wν : Fin 1 ⊕ Fin 1 ⊕ Unit → K := Pi.single (.inl 0) 1 + Pi.single (.inr (.inl 0)) ν
    with hwνdef
  have hw₁ : quadOdd 1 K w₁ = 1 := by simp [w₁, quadOdd_apply]
  have hwν : quadOdd 1 K wν = ν := by simp [wν, quadOdd_apply, Pi.single_apply]
  let _ : Invertible (quadOdd 1 K w₁) := invertibleOfNonzero (by rw [hw₁]; exact one_ne_zero)
  let _ : Invertible (quadOdd 1 K wν) := invertibleOfNonzero (by rw [hwν]; exact hν0)
  set r₁ := TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 1 K) w₁ with hr₁
  set rν := TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 1 K) wν with hrν
  set d := QuadraticMap.orthogonalDet (quadOdd 1 K) with hd
  set θ := orthogonalSpinorNorm (quadOdd 1 K) (nondegenerate_quadOdd 1 K) with hθdef
  have hd₁ : d r₁ = -1 := QuadraticMap.orthogonalDet_reflectionOrthogonal (quadOdd 1 K) w₁
  have hdν : d rν = -1 := QuadraticMap.orthogonalDet_reflectionOrthogonal (quadOdd 1 K) wν
  have hneg : (-1 : Kˣ) ≠ 1 := fun h => h2 (by
    have h' : (-1 : K) = 1 := by simpa using congrArg Units.val h
    calc (2 : K) = 1 - (-1) := by ring
      _ = 0 := by rw [h']; ring)
  have hA := two_mul_card_ker_le d (x := r₁) (by rw [hd₁]; exact hneg)
  have hx : r₁ * rν ∈ d.ker := by
    rw [MonoidHom.mem_ker, map_mul, hd₁, hdν]
    simp
  have hθ : (θ.comp d.ker.subtype) ⟨r₁ * rν, hx⟩ ≠ 1 := by
    rw [MonoidHom.comp_apply, coe_subtype, map_mul, hθdef,
      orthogonalSpinorNorm_reflectionOrthogonal, orthogonalSpinorNorm_reflectionOrthogonal]
    have hu₁ : unitOfInvertible (quadOdd 1 K w₁) = 1 :=
      Units.ext (by rw [val_unitOfInvertible, hw₁, Units.val_one])
    rw [hu₁, map_one, one_mul, TauCeti.squareClassHom_apply]
    intro h
    have h' : TauCeti.squareClass (unitOfInvertible (quadOdd 1 K wν)) = 0 := by
      simpa using congrArg Multiplicative.toAdd h
    rw [TauCeti.squareClass_eq_zero_iff] at h'
    apply hν
    have := h'.map (Units.coeHom K)
    rwa [Units.coeHom_apply, val_unitOfInvertible, hwν] at this
  have hB := two_mul_card_ker_le (θ.comp d.ker.subtype) hθ
  have hC : Nat.card (detSpinorNorm (nondegenerate_quadOdd 1 K)).ker =
      Nat.card (θ.comp d.ker.subtype).ker := by
    have hmap : (θ.comp d.ker.subtype).ker.map d.ker.subtype =
        (detSpinorNorm (nondegenerate_quadOdd 1 K)).ker := by
      ext g
      rw [mem_map, MonoidHom.mem_ker, detSpinorNorm_apply, Prod.mk_eq_one]
      constructor
      · rintro ⟨g', hg', rfl⟩
        exact ⟨g'.2, hg'⟩
      · rintro ⟨hg1, hg2⟩
        exact ⟨⟨g, hg1⟩, hg2, rfl⟩
    rw [← hmap, card_map_of_injective (subtype_injective _)]
  omega

end Finite

theorem perpCoords_incl (Y : Matrix (Fin 2) (Fin 2) K) : perpCoords ((frame01 K).incl Y) = 0 := by
  funext σ
  rcases σ with i | i | ⟨⟩ <;>
    simp [perpCoords, perpIdx, LinearMap.funLeft_apply, Frame.incl_apply, Frame.e₁, Frame.f₁,
      Frame.e₂, Frame.f₂, CFSG.LieType.Universal.Spin.HypFrame.toFrame]

theorem spinAction_eq_perpEmb (h2 : (2 : K) ≠ 0)
    {c : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))}
    (hW : transportHom h2 (spinCent K c) = 1) :
    spinAction (quadOdd 3 K) c =
      perpEmb ((perpHom h2 (spinCent K c) : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K)) :
        (Fin 1 ⊕ Fin 1 ⊕ Unit → K) ≃ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K)) := by
  set g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) := (spinCent K c).1 with hg
  have hcomm : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g :=
    comm_of_mem_isoCentLa (spinCent K c).2
  have hW' : ∀ Y, (frame01 K).transport g Y = Y := fun Y =>
    LinearEquiv.congr_fun (congrArg Subtype.val hW) Y
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨r, hrdef⟩ : ∃ r, r = v - (frame01 K).incl ((frame01 K).coords v) := ⟨_, rfl⟩
  have hr : (frame01 K).La (-1) r = r := by
    rw [hrdef]
    exact ((frame01 K).mem_perp_iff_fix h2).mp (by rw [(frame01 K).mem_perp_iff, map_sub,
      (frame01 K).coords_incl, sub_self])
  have hdec : v = (frame01 K).incl ((frame01 K).coords v) + r := by rw [hrdef]; abel
  have hCv : perpCoords v = perpCoords r := by
    rw [hrdef, map_sub, perpCoords_incl, sub_zero]
  have hgw : g ((frame01 K).incl ((frame01 K).coords v)) =
      (frame01 K).incl ((frame01 K).coords v) := by
    rw [← Frame.incl_transport h2 hcomm, hW']
  have hgr : g r = perpIncl (perpTransport g (perpCoords r)) := by
    rw [perpIncl_perpTransport h2 hcomm, perpIncl_perpCoords h2 hr]
  have e1 : g v = (frame01 K).incl ((frame01 K).coords v) +
      perpIncl (perpTransport g (perpCoords r)) := by
    conv_lhs => rw [hdec]
    rw [map_add, hgw, hgr]
  show g v = perpEmbLin (perpTransportEquiv h2 hcomm : Module.End K _) v
  rw [perpEmbLin_apply, LinearEquiv.coe_coe, perpTransportEquiv_apply, hCv, map_sub,
    perpIncl_perpCoords h2 hr, e1]
  have hvr : v - r = (frame01 K).incl ((frame01 K).coords v) := by rw [hrdef]; abel
  rw [← hvr]
  abel

section Card

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem det_transportHom_spinCent (c : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :
    QuadraticMap.orthogonalDet (detQ (K := K))
      (transportHom (two_ne_zero_spin hp hp2 hK) (spinCent K c)) = 1 := by
  have h2 := two_ne_zero_spin hp hp2 hK
  set g := spinAction (quadOdd 3 K) (c : spinGroup (quadOdd 3 K)) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ _)
  have hgc : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g :=
    comm_of_mem_isoCentLa (spinCent K c).2
  have hn := (normal_subgroupOf_iff (spinJ_le_centralizer (K := K) hp hp2 hK).2.1).mp
    (normal_spinJ (K := K) hp hp2 hK h5).2.1
  have hmap := CFSG.ClassicalInvolution.ModelFacts.map_longSL2_range
    (oddFrame 3 K).toHypFrame fin3_zero_ne_one true true
  have hconj : conjSubgroup g (frame01 K).La.range = (frame01 K).La.range := by
    rw [← hmap]
    ext x
    rw [mem_conjSubgroup]
    constructor
    · rintro ⟨j, hj, hjx⟩
      refine ⟨(c : spinGroup (quadOdd 3 K)) * j * (c : spinGroup (quadOdd 3 K))⁻¹,
        hn j c hj c.2, ?_⟩
      rw [map_mul, map_mul, map_inv, hjx, ← hg]
      group
    · rintro ⟨j, hj, rfl⟩
      refine ⟨(c : spinGroup (quadOdd 3 K))⁻¹ * j * (c : spinGroup (quadOdd 3 K))⁻¹⁻¹,
        hn j _ hj (inv_mem c.2), ?_⟩
      rw [inv_inv, map_mul, map_mul, map_inv]
  rcases Frame.conjSubgroup_La_range h2 hgO hgc with ⟨hd, -, -⟩ | ⟨-, h1, -⟩
  · rw [QuadraticMap.orthogonalDet_apply]
    exact hd
  · exact absurd (hconj.symm.trans h1) (Frame.La_range_ne_swap_La_range _)

theorem card_centralizer_tSeven_le :
    Nat.card (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) ≤
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  set C := centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  set φ₁ : C →* TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) :=
    (transportHom h2).comp (spinCent K) with hφ₁
  have hrange : φ₁.range ≤ (QuadraticMap.orthogonalDet (detQ (K := K))).ker := by
    rintro _ ⟨c, rfl⟩
    exact det_transportHom_spinCent hp hp2 hK h5 c
  let _ : Invertible (detQ (K := K) 1) := invertibleOfNonzero (by simp [detQ_apply])
  have hneg : (-1 : Kˣ) ≠ 1 := fun h => h2 (by
    have h' : (-1 : K) = 1 := by simpa using congrArg Units.val h
    calc (2 : K) = 1 - (-1) := by ring
      _ = 0 := by rw [h']; ring)
  have hdet := two_mul_card_ker_le (QuadraticMap.orthogonalDet (detQ (K := K)))
    (x := TauCeti.QuadraticMap.reflectionOrthogonal (detQ (K := K)) 1)
    (by rw [QuadraticMap.orthogonalDet_reflectionOrthogonal]; exact hneg)
  rw [card_orthogonalGroup_detQ h2] at hdet
  have hR : Nat.card φ₁.range ≤ Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
    have := card_le_of_le hrange
    nlinarith
  set φ₂ : φ₁.ker →* TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K) :=
    (perpHom h2).comp ((spinCent K).comp φ₁.ker.subtype) with hφ₂
  have hrange₂ : φ₂.range ≤ (detSpinorNorm (nondegenerate_quadOdd 1 K)).ker := by
    rintro _ ⟨c, rfl⟩
    rw [MonoidHom.mem_ker, ← detSpinorNorm_perpEmbO]
    apply detSpinorNorm_eq_one_of_mem_elementaryGroup
    rw [coe_perpEmbO, ← range_spinAction_quadOdd h2 (le_refl 3)]
    refine ⟨(c : C), ?_⟩
    exact spinAction_eq_perpEmb h2 c.2
  have hker₂ : Nat.card φ₂.ker ≤ 2 := by
    have hZ : Nat.card (center (spinGroup (quadOdd 3 K))) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [center_spinGroup_quadOdd h2 le_rfl, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact spinGroup.negOne_mul_self _ _)
          (spinGroup.negOne_ne_one _ _)]
    refine le_trans (Nat.card_le_card_of_injective
      (fun k => (⟨((k : φ₁.ker) : C), ker_spinAction_le_center _ ?_⟩ :
        center (spinGroup (quadOdd 3 K)))) ?_) hZ.le
    · rw [MonoidHom.mem_ker]
      apply spinAction_eq_one_of_resHom_eq_one h2
      exact Prod.ext (k : φ₁.ker).2 k.2
    · intro k k' h
      have h' := congrArg Subtype.val h
      dsimp only at h'
      apply Subtype.ext
      apply Subtype.ext
      exact Subtype.ext h'
  have h4 := four_mul_card_ker_detSpinorNorm_le (K := K)
  rw [card_orthogonalGroup_quadOdd_one h2] at h4
  have hK₁ : Nat.card φ₁.ker ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
    have e := card_ker_mul_card_range φ₂
    have := card_le_of_le hrange₂
    nlinarith
  calc Nat.card C = Nat.card φ₁.ker * Nat.card φ₁.range := (card_ker_mul_card_range φ₁).symm
    _ ≤ (Nat.card K * (Nat.card K ^ 2 - 1)) * (Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) :=
      Nat.mul_le_mul hK₁ hR
    _ = Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by ring

end Card

end CFSG.ComponentClassification.HarrisLit.T1
