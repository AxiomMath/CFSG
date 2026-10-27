module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {K : Type} [Field K]

@[expose] noncomputable def perpIncl :
    (Fin 1 ⊕ Fin 1 ⊕ Unit → K) →ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) where
  toFun w := w (.inl 0) • oddVec 3 K 2 true + w (.inr (.inl 0)) • oddVec 3 K 2 false +
    w (.inr (.inr ())) • oddZ 3 K
  map_add' u w := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c w := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

@[expose] def perpIdx : Fin 1 ⊕ Fin 1 ⊕ Unit → Fin 3 ⊕ Fin 3 ⊕ Unit
  | .inl _ => .inl 2
  | .inr (.inl _) => .inr (.inl 2)
  | .inr (.inr u) => .inr (.inr u)

@[expose] noncomputable def perpCoords :
    (Fin 3 ⊕ Fin 3 ⊕ Unit → K) →ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K) :=
  LinearMap.funLeft K K perpIdx

theorem perpCoords_perpIncl (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) : perpCoords (perpIncl w) = w := by
  funext σ
  rcases σ with i | i | ⟨⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [perpCoords, perpIdx, perpIncl, LinearMap.funLeft_apply, oddZ]
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [perpCoords, perpIdx, perpIncl, LinearMap.funLeft_apply, oddZ]
  · simp [perpCoords, perpIdx, perpIncl, LinearMap.funLeft_apply, oddZ]

theorem perpIncl_perpCoords (h2 : (2 : K) ≠ 0) {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hv : (frame01 K).La (-1) v = v) : perpIncl (perpCoords v) = v :=
  (eq_of_La_neg_one_apply_eq h2 hv).symm

theorem La_neg_one_perpIncl (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    (frame01 K).La (-1) (perpIncl w) = perpIncl w := by
  simp only [perpIncl, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul, La_neg_one_apply_e2,
    La_neg_one_apply_f2, La_neg_one_apply_z]

theorem quadOdd_perpIncl (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    quadOdd 3 K (perpIncl w) = quadOdd 1 K w := by
  rw [quadOdd_apply, quadOdd_apply]
  simp [perpIncl, oddZ, Pi.single_apply]

section Transport

@[expose] noncomputable def perpTransport
    (g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) :
    Module.End K (Fin 1 ⊕ Fin 1 ⊕ Unit → K) :=
  perpCoords ∘ₗ (g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) →ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∘ₗ perpIncl

variable {g h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}

theorem perpTransport_apply (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    perpTransport g w = perpCoords (g (perpIncl w)) :=
  rfl

theorem perpIncl_perpTransport (h2 : (2 : K) ≠ 0)
    (hg : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g) (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    perpIncl (perpTransport g w) = g (perpIncl w) := by
  apply perpIncl_perpCoords h2
  have h1 := LinearEquiv.congr_fun hg (perpIncl w)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_neg_one_perpIncl] at h1
  exact h1.symm

theorem perpTransport_mul (h2 : (2 : K) ≠ 0)
    (hh : h * (frame01 K).La (-1) = (frame01 K).La (-1) * h) :
    perpTransport (g * h) = perpTransport g * perpTransport h := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, perpTransport_apply (g := g), perpIncl_perpTransport h2 hh w]
  rfl

theorem perpTransport_one : perpTransport (1 : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] _) = 1 :=
  LinearMap.ext fun w => perpCoords_perpIncl w

theorem perpTransport_mul_inv (h2 : (2 : K) ≠ 0)
    (hg : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g) :
    perpTransport g * perpTransport g⁻¹ = 1 := by
  rw [← perpTransport_mul h2 (Frame.inv_commute_La hg), mul_inv_cancel, perpTransport_one]

theorem perpTransport_inv_mul (h2 : (2 : K) ≠ 0)
    (hg : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g) :
    perpTransport g⁻¹ * perpTransport g = 1 := by
  rw [← perpTransport_mul h2 hg, inv_mul_cancel, perpTransport_one]

@[expose] noncomputable def perpTransportEquiv (h2 : (2 : K) ≠ 0)
    (hg : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g) :
    (Fin 1 ⊕ Fin 1 ⊕ Unit → K) ≃ₗ[K] (Fin 1 ⊕ Fin 1 ⊕ Unit → K) :=
  LinearEquiv.ofLinearMap (perpTransport g) (perpTransport g⁻¹)
    (by rw [← Module.End.mul_eq_comp]; exact perpTransport_mul_inv h2 hg)
    (by rw [← Module.End.mul_eq_comp]; exact perpTransport_inv_mul h2 hg)

theorem perpTransportEquiv_apply (h2 : (2 : K) ≠ 0)
    (hg : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g) (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    perpTransportEquiv h2 hg w = perpTransport g w :=
  rfl

theorem perpTransportEquiv_mem_orthogonalGroup (h2 : (2 : K) ≠ 0)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K))
    (hg : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g) :
    perpTransportEquiv h2 hg ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => ?_
  rw [← quadOdd_perpIncl, ← quadOdd_perpIncl, perpTransportEquiv_apply,
    perpIncl_perpTransport h2 hg, CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO]

end Transport

@[expose] noncomputable def isoCentLa (K : Type) [Field K] :
    Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) :=
  TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓
    Subgroup.centralizer {(frame01 K).La (-1)}

theorem comm_of_mem_isoCentLa {g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hg : g ∈ isoCentLa K) : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g :=
  mem_centralizer_singleton_iff.mp hg.2

@[expose] noncomputable def transportHom (h2 : (2 : K) ≠ 0) :
    isoCentLa K →* TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) where
  toFun g := ⟨(frame01 K).transportEquiv h2 (comm_of_mem_isoCentLa g.2),
    Frame.transportEquiv_mem_orthogonalGroup h2 g.2.1 (comm_of_mem_isoCentLa g.2)⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun Y => (frame01 K).coords_incl Y)
  map_mul' _ h := Subtype.ext (LinearEquiv.ext fun Y =>
    LinearMap.congr_fun ((frame01 K).transport_mul h2 (comm_of_mem_isoCentLa h.2)) Y)

@[expose] noncomputable def perpHom (h2 : (2 : K) ≠ 0) :
    isoCentLa K →* TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K) where
  toFun g := ⟨perpTransportEquiv h2 (comm_of_mem_isoCentLa g.2),
    perpTransportEquiv_mem_orthogonalGroup h2 g.2.1 (comm_of_mem_isoCentLa g.2)⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun w => perpCoords_perpIncl w)
  map_mul' _ h := Subtype.ext (LinearEquiv.ext fun w =>
    LinearMap.congr_fun (perpTransport_mul h2 (comm_of_mem_isoCentLa h.2)) w)

theorem eq_one_of_transportHom_perpHom (h2 : (2 : K) ≠ 0) {x : isoCentLa K}
    (hW : transportHom h2 x = 1) (hP : perpHom h2 x = 1) :
    (x : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) = 1 := by
  set g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) := x.1 with hg
  have hcomm : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g := comm_of_mem_isoCentLa x.2
  have hW' : ∀ Y, (frame01 K).transport g Y = Y := fun Y =>
    LinearEquiv.congr_fun (congrArg Subtype.val hW) Y
  have hP' : ∀ w, perpTransport g w = w := fun w =>
    LinearEquiv.congr_fun (congrArg Subtype.val hP) w
  refine LinearEquiv.ext fun v => ?_
  have hr : (frame01 K).La (-1) (v - (frame01 K).incl ((frame01 K).coords v)) =
      v - (frame01 K).incl ((frame01 K).coords v) :=
    ((frame01 K).mem_perp_iff_fix h2).mp (by rw [(frame01 K).mem_perp_iff, map_sub,
      (frame01 K).coords_incl, sub_self])
  have hdec : v = (frame01 K).incl ((frame01 K).coords v) +
      (v - (frame01 K).incl ((frame01 K).coords v)) := by abel
  show g v = v
  conv_lhs => rw [hdec]
  rw [map_add, ← Frame.incl_transport h2 hcomm, hW', ← perpIncl_perpCoords h2 hr,
    ← perpIncl_perpTransport h2 hcomm, hP', perpIncl_perpCoords h2 hr]
  exact hdec.symm

theorem spinAction_mem_isoCentLa
    (c : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :
    spinAction (quadOdd 3 K) c ∈ isoCentLa K := by
  refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ _),
    mem_centralizer_singleton_iff.mpr ?_⟩
  have hct : (c : spinGroup (quadOdd 3 K)) * tSeven K = tSeven K * c :=
    mem_centralizer_singleton_iff.mp c.2
  rw [← spinAction_tSeven, ← map_mul, ← map_mul, hct]

@[expose] noncomputable def spinCent (K : Type) [Field K] :
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) →* isoCentLa K :=
  ((spinAction (quadOdd 3 K)).comp (centralizer _).subtype).codRestrict _
    spinAction_mem_isoCentLa

@[expose] noncomputable def resHom (h2 : (2 : K) ≠ 0) :
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) →*
      TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) ×
        TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K) :=
  ((transportHom h2).prod (perpHom h2)).comp (spinCent K)

theorem spinAction_eq_one_of_resHom_eq_one (h2 : (2 : K) ≠ 0)
    {c : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))} (hc : resHom h2 c = 1) :
    spinAction (quadOdd 3 K) c = 1 :=
  eq_one_of_transportHom_perpHom h2 (x := spinCent K c) (congrArg Prod.fst hc)
    (congrArg Prod.snd hc)

@[expose] noncomputable def detQIsometryEquiv : (detQ (K := K)).IsometryEquiv (quadPlus 2 K) where
  toFun X := Sum.elim ![X 0 0, X 0 1] ![X 1 1, -X 1 0]
  invFun w := !![w (.inl 0), w (.inl 1); -w (.inr 1), w (.inr 0)]
  map_add' X Y := by
    funext σ
    rcases σ with i | i <;> fin_cases i <;> simp [add_comm]
  map_smul' c X := by
    funext σ
    rcases σ with i | i <;> fin_cases i <;> simp
  left_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  right_inv w := by
    funext σ
    rcases σ with i | i <;> fin_cases i <;> simp
  map_app' X := by
    rw [detQ_apply, quadPlus_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

variable [Finite K]

theorem card_orthogonalGroup_detQ (h2 : (2 : K) ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
  rw [Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr detQIsometryEquiv]
  have h := CFSG.ClassicalInvolution.card_orthogonalGroup_quadPlus_of_two_ne_zero h2 1
  have hq : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have h' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)) : ℤ) =
      ((2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub hq]
    simp [Finset.Icc_self]
    ring
  exact_mod_cast h'

theorem card_orthogonalGroup_quadOdd_one (h2 : (2 : K) ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K)) =
      2 * Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h := CFSG.ClassicalInvolution.card_orthogonalGroup_quadOdd_of_two_ne_zero h2 1
  have hq : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have h' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 K)) : ℤ) =
      ((2 * Nat.card K * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub hq]
    simp [Finset.Icc_self]
  exact_mod_cast h'

theorem card_centralizer_tSeven_dvd (h2 : (2 : K) ≠ 0) :
    Nat.card (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) ∣
      8 * Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Finite (spinGroup (quadOdd 3 K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  set C := centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  have hker : Nat.card (resHom h2).ker ∣ 2 := by
    have hle : (resHom h2).ker.map C.subtype ≤ center (spinGroup (quadOdd 3 K)) := by
      rintro _ ⟨c, hc, rfl⟩
      exact ker_spinAction_le_center _
        (MonoidHom.mem_ker.mpr (spinAction_eq_one_of_resHom_eq_one h2 hc))
    have h1 := card_dvd_of_le hle
    rw [card_map_of_injective C.subtype_injective, center_spinGroup_quadOdd h2 le_rfl,
      Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact spinGroup.negOne_mul_self _ _)
        (spinGroup.negOne_ne_one _ _)] at h1
    exact h1
  have hrange : Nat.card (resHom h2).range ∣
      (2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) *
        (2 * Nat.card K * (Nat.card K ^ 2 - 1)) := by
    have h1 := card_subgroup_dvd_card (resHom h2).range
    rwa [Nat.card_prod, card_orthogonalGroup_detQ h2, card_orthogonalGroup_quadOdd_one h2] at h1
  rw [← card_ker_mul_card_range (resHom h2)]
  calc Nat.card (resHom h2).ker * Nat.card (resHom h2).range ∣
      2 * ((2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2) *
        (2 * Nat.card K * (Nat.card K ^ 2 - 1))) := mul_dvd_mul hker hrange
    _ = 8 * Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by ring

end CFSG.ComponentClassification.HarrisLit.T1
