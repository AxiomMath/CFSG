module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesLevi
public import CFSG.RankThree.PartOne.CTP.SpinMinusEven
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (coordEmbedGL)
open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_conj eichler_smul_left toLinEquiv
  toLinEquiv_apply)
open scoped MatrixGroups

variable {K : Type} [Field K] {r : ℕ}

section Torus

theorem kOmM_toLinEquiv_diag_single (t : Fin r → Kˣ)
    (a : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) (x : K) :
    toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K (kOmMDiag K r t) (Pi.single a x) =
      kOmMWeight K r t a • (Pi.single a x : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) := by
  rw [toLinEquiv_apply, kOmMDiag_coe, diagonal_mulVec_single, ← Pi.single_smul, smul_eq_mul]

theorem kOmM_toLinEquiv_diag_planeVec (t : Fin r → Kˣ) (p : Fin 2 → K) :
    toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K (kOmMDiag K r t) (planeVec (r + 1) p) =
      planeVec (r + 1) p := by
  rw [toLinEquiv_apply, kOmMDiag_coe]
  funext y
  rw [mulVec_diagonal]
  rcases y with i | i | j
  · simp [planeVec]
  · simp [planeVec]
  · rw [kOmMWeight_inr_inr, one_mul]

variable [Finite K] [CharP K 2]

theorem kOmM_toLinEquiv_diag_mem_orthogonalGroup (b c : K) (t : Fin r → Kˣ) :
    toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K (kOmMDiag K r t) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (r + 1) K b c) := by
  rw [kOmM_toLinEquiv_diag b c]
  exact Subgroup.commutator_le_self _ ((kOmM_isHypFrame b c).frameLin_mem_orthDerived t)

omit [Finite K] [CharP K 2] in
theorem kOmM_conj_eichler_eq {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {D : V ≃ₗ[K] V} (hD : D ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u w : V} {l : K}
    (hl : l ≠ 0) (hu : D u = l • u) (hw : D w = l⁻¹ • w) :
    D * eichler Q u w * D⁻¹ = eichler Q u w := by
  rw [eichler_conj hD, hu, hw, eichler_smul_left, smul_smul, mul_inv_cancel₀ hl, one_smul]

end Torus

section Commute

variable [Finite K] [CharP K 2] {b c : K}

omit [Finite K] [CharP K 2] in
theorem kOmM_commute_spinMatrix_of_conj {x : spinGroup (quadMinus (r + 1) K b c)}
    {t : Fin r → Kˣ}
    (h : toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K (kOmMDiag K r t) *
        spinAction (quadMinus (r + 1) K b c) x *
        (toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K (kOmMDiag K r t))⁻¹ =
      spinAction (quadMinus (r + 1) K b c) x) :
    kOmMDiag K r t * spinMatrix (quadMinus (r + 1) K b c) x =
      spinMatrix (quadMinus (r + 1) K b c) x * kOmMDiag K r t := by
  apply (toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K).injective
  rw [map_mul, map_mul, toLinEquiv_spinMatrix]
  conv_rhs => rw [← h]
  group

theorem kOmM_spinMatrix_rLong_le_centralizer {k : Fin (r + 1 - 1)} (hk : k.val + 1 < r + 1 - 1)
    {Ts : Set (Fin r → Kˣ)} (hTs : ∀ t ∈ Ts, t k = t ⟨k.val + 1, hk⟩) :
    (rLong (r + 1) b c hk).range.map (spinMatrix (quadMinus (r + 1) K b c)) ≤
      centralizer (kOmMDiag K r '' Ts) := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  set D := toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K (kOmMDiag K r t) with hDdef
  have hD := kOmM_toLinEquiv_diag_mem_orthogonalGroup b c t
  have hl : ((t k : Kˣ) : K) ≠ 0 := (t k).ne_zero
  have hf : ∀ i : Fin (r + 1 - 1), D (fVec (r + 1) i) = ((t i : Kˣ) : K)⁻¹ • fVec (r + 1) i :=
    fun i => by
      rw [hDdef, fVec, kOmM_toLinEquiv_diag_single, kOmMWeight_inr_inl, Units.val_inv_eq_inv_val]
  have he : ∀ i : Fin (r + 1 - 1) , ∀ x : K, D (x • eVec (r + 1) i) =
      (((t i : Kˣ) : K)⁻¹)⁻¹ • (x • eVec (r + 1) i) := fun i x => by
    rw [map_smul, hDdef, eVec, kOmM_toLinEquiv_diag_single, kOmMWeight_inl, inv_inv, smul_comm]
  have htk : t ⟨k.val + 1, hk⟩ = t k := (hTs t ht).symm
  have key : (MulAut.conj D).toMonoidHom.comp ((spinAction (quadMinus (r + 1) K b c)).comp
      (rLong (r + 1) b c hk)) =
        (spinAction (quadMinus (r + 1) K b c)).comp (rLong (r + 1) b c hk) := by
    refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [rLong_tv01, HypFrame.spinAction_longRoot_eq_eichler, minusFrame_vec, minusVec_false,
        minusVec_true]
      refine kOmM_conj_eichler_eq hD (inv_ne_zero (t _).ne_zero) (hf _) ?_
      rw [he, htk]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [rLong_tv10, HypFrame.spinAction_longRoot_eq_eichler, minusFrame_vec, minusVec_false,
        minusVec_true]
      refine kOmM_conj_eichler_eq hD (inv_ne_zero (t _).ne_zero) (hf _) ?_
      rw [he, htk]
  exact kOmM_commute_spinMatrix_of_conj (DFunLike.congr_fun key A)

variable [Fact (∀ s : K, s ^ 2 ≠ -c + b * s)]

theorem kOmM_spinMatrix_shortBlock_le_centralizer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {l : Fin (r + 1 - 1)} {Ts : Set (Fin r → Kˣ)} (hTs : ∀ t ∈ Ts, t l = 1) :
    (shortBlock hirr (r + 1) l).range.map (spinMatrix (quadMinus (r + 1) K b c)) ≤
      centralizer (kOmMDiag K r '' Ts) := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  set D := toLinEquiv (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K (kOmMDiag K r t) with hDdef
  have hD := kOmM_toLinEquiv_diag_mem_orthogonalGroup b c t
  have htl : ((t l : Kˣ) : K) = 1 := by rw [hTs t ht, Units.val_one]
  have hp : ∀ p : Fin 2 → K, D (planeVec (r + 1) p) = (1 : K)⁻¹ • planeVec (r + 1) p :=
    fun p => by rw [inv_one, one_smul, hDdef, kOmM_toLinEquiv_diag_planeVec]
  have hu : ∀ s : Bool, D (minusVec (r + 1) l s) = (1 : K) • minusVec (r + 1) l s := by
    intro s
    cases s
    · rw [minusVec_false, hDdef, fVec, kOmM_toLinEquiv_diag_single, kOmMWeight_inr_inl,
        Units.val_inv_eq_inv_val, htl, inv_one]
    · rw [minusVec_true, hDdef, eVec, kOmM_toLinEquiv_diag_single, kOmMWeight_inl, htl]
  have key : (MulAut.conj D).toMonoidHom.comp ((spinAction (quadMinus (r + 1) K b c)).comp
      (shortBlock hirr (r + 1) l)) =
      (spinAction (quadMinus (r + 1) K b c)).comp (shortBlock hirr (r + 1) l) := by
    refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [shortBlock_tv01, ← twShortRoot_true, spinAction_twShortRoot_eq_eichler]
      exact kOmM_conj_eichler_eq hD one_ne_zero (hu true) (hp _)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [shortBlock_tv10, ← twShortRoot_false, spinAction_twShortRoot_eq_eichler]
      exact kOmM_conj_eichler_eq hD one_ne_zero (hu false) (hp _)
  exact kOmM_commute_spinMatrix_of_conj (DFunLike.congr_fun key A)

end Commute

section Theta

variable [Finite K] [CharP K 2] {b c : K}

omit [Finite K] [CharP K 2] in
theorem kOmM_commutator_range_of_isPerfect {X Y : Type*} [Group X] [Group Y] [Group.IsPerfect X]
    (f : X →* Y) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

variable (b c) in
@[expose] noncomputable def kOmMThetaGL (hr : 3 ≤ r) :
    spinGroup (quadMinus 3 K b c) →* GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K :=
  (spinMatrix (quadMinus (r + 1) K b c)).comp (minusShift (r + 1) (by omega) b c).spinGroupMap

theorem kOmMThetaGL_injective (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (kOmMThetaGL b c hr) :=
  ((MonoidHom.ker_eq_bot_iff _).1 (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)).comp
    (CFSG.RankThree.PartOne.CTP.spinGroupMap_minusShift_injective_even (r + 1) (by omega) hirr)

omit [CharP K 2] in
theorem kOmMThetaGL_mem (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : spinGroup (quadMinus 3 K b c)) :
    kOmMThetaGL b c hr g ∈ StatedOmega (StatedQuadMinus (r + 1) K b c) := by
  rw [← range_spinMatrix_quadMinus (by omega : 4 ≤ r + 1) hirr]
  exact ⟨_, rfl⟩

@[expose] noncomputable def kOmMTheta (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    spinGroup (quadMinus 3 K b c) →* StatedOmega (StatedQuadMinus (r + 1) K b c) :=
  (kOmMThetaGL b c hr).codRestrict _ (kOmMThetaGL_mem hr hirr)

theorem kOmMTheta_injective (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (kOmMTheta hr hirr) :=
  fun _ _ h => kOmMThetaGL_injective hr hirr (congrArg Subtype.val h)

omit [CharP K 2] in
theorem kOmMTheta_map_subtype (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (H : Subgroup (spinGroup (quadMinus 3 K b c))) :
    (H.map (kOmMTheta hr hirr)).map (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype =
      H.map (kOmMThetaGL b c hr) := by
  rw [Subgroup.map_map]
  rfl

theorem kOmMTheta_longBlock (hK : 4 ≤ Nat.card K) (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Fin r} (hk3 : k.val + 3 = r + 1) :
    ((minusLongBlock b c).range.map (kOmMTheta hr hirr)).map
        (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype =
      (OmegaPilot.siegelBlockGL K {k, ⟨k.val + 1, by omega⟩}).map
        (coordEmbedGL (kOmMEmb r) kOmMEmb_injective) := by
  have hk : k.val + 1 < r + 1 - 1 := by omega
  have hl : (kOmMThetaGL b c hr).comp (minusLongBlock b c) =
      (spinMatrix (quadMinus (r + 1) K b c)).comp (rLong (r + 1) b c hk) := by
    rw [kOmMThetaGL, MonoidHom.comp_assoc,
      minusShift_comp_longBlock (n := r + 1) (by omega) (k := k) hk3 hk]
  have hinj : Function.Injective ((spinMatrix (quadMinus (r + 1) K b c)).comp
      (rLong (r + 1) b c hk)) :=
    ((MonoidHom.ker_eq_bot_iff _).1 (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)).comp
      (rLong_injective hk)
  have hkj : k ≠ ⟨k.val + 1, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
  have hshort := kOmM_perfectCore_short hK hirr hkj
    (Ts := {t : Fin r → Kˣ | t k = t ⟨k.val + 1, by omega⟩}) (fun t => Iff.rfl)
  rw [kOmMTheta_map_subtype, ← MonoidHom.range_comp, hl, ← hshort]
  refine Subgroup.eq_of_le_of_card_ge (le_perfectCore_of_perfect (le_inf ?_ ?_) ?_) ?_
  · rintro _ ⟨y, rfl⟩
    rw [← range_spinMatrix_quadMinus (by omega : 4 ≤ r + 1) hirr]
    exact ⟨_, rfl⟩
  · rw [MonoidHom.range_comp]
    exact kOmM_spinMatrix_rLong_le_centralizer hk (fun t ht => ht)
  · have := CFSG.RankThree.PartOne.KCRootAxis.sl2_isPerfect hK
    exact kOmM_commutator_range_of_isPerfect _
  · rw [hshort, kOmM_card_short hkj]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).le

variable [Fact (∀ s : K, s ^ 2 ≠ -c + b * s)]

theorem kOmMTheta_shortBlock (hK : 4 ≤ Nat.card K) (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Fin r} (hk3 : k.val + 3 = r + 1) :
    ((shortBlock hirr 3 finOne).range.map (kOmMTheta hr hirr)).map
        (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype =
      (StatedOmega (StatedQuadMinus 2 K b c)).map
        (coordEmbedGL (kOmMLongEmb r ⟨k.val + 1, by omega⟩) (kOmMLongEmb_injective _)) := by
  set l : Fin (r + 1 - 1) := ⟨k.val + 1, by omega⟩ with hldef
  have hl2 : l.val + 2 = r + 1 := by simp only [hldef]; omega
  have hs : (kOmMThetaGL b c hr).comp (shortBlock hirr 3 finOne) =
      (spinMatrix (quadMinus (r + 1) K b c)).comp (shortBlock hirr (r + 1) l) := by
    rw [kOmMThetaGL, MonoidHom.comp_assoc, minusShift_comp_shortBlock (by omega) hirr hl2]
  have hinj : Function.Injective ((spinMatrix (quadMinus (r + 1) K b c)).comp
      (shortBlock hirr (r + 1) l)) :=
    ((MonoidHom.ker_eq_bot_iff _).1 (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)).comp
      (CFSG.RankThree.PartOne.CTP.shortBlock_injective_even hirr (r + 1) l)
  have hlong := kOmM_perfectCore_long hK hirr (l := ⟨k.val + 1, by omega⟩)
    (Ts := {t : Fin r → Kˣ | t ⟨k.val + 1, by omega⟩ = 1}) (fun t => Iff.rfl)
  rw [kOmMTheta_map_subtype, ← MonoidHom.range_comp, hs, ← hlong]
  refine Subgroup.eq_of_le_of_card_ge (le_perfectCore_of_perfect (le_inf ?_ ?_) ?_) ?_
  · rintro _ ⟨y, rfl⟩
    rw [← range_spinMatrix_quadMinus (by omega : 4 ≤ r + 1) hirr]
    exact ⟨_, rfl⟩
  · rw [MonoidHom.range_comp]
    exact kOmM_spinMatrix_shortBlock_le_centralizer hirr (fun t ht => ht)
  · have := CFSG.RankThree.PartOne.KCRootAxis.sl2_isPerfect
      (four_le_card_shortField' (b := b) (c := c))
    exact kOmM_commutator_range_of_isPerfect _
  · have := finite_shortField (b := b) (c := c)
    have hE : Nat.card (ShortField b c) = Nat.card K ^ 2 := by
      rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, _root_.sq]
    rw [hlong, kOmM_card_long hirr, ← (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv),
      F4Pilot.natCard_specialLinearGroup_eq_ordSL (by norm_num), hE]

theorem kOmM_exists_twisted_model (hK : 4 ≤ Nat.card K) (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Fin r} (hk3 : k.val + 3 = r + 1) :
    ∃ Θ : spinGroup (quadMinus 3 K b c) →* StatedOmega (StatedQuadMinus (r + 1) K b c),
      Function.Injective Θ ∧ Function.Injective (Θ.comp (minusLongBlock b c)) ∧
      Function.Injective (Θ.comp (shortBlock hirr 3 finOne)) ∧
      ((minusLongBlock b c).range.map Θ).map
          (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype =
        (OmegaPilot.siegelBlockGL K {k, ⟨k.val + 1, by omega⟩}).map
          (coordEmbedGL (kOmMEmb r) kOmMEmb_injective) ∧
      ((shortBlock hirr 3 finOne).range.map Θ).map
          (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype =
        (StatedOmega (StatedQuadMinus 2 K b c)).map
          (coordEmbedGL (kOmMLongEmb r ⟨k.val + 1, by omega⟩) (kOmMLongEmb_injective _)) :=
  ⟨kOmMTheta hr hirr, kOmMTheta_injective hr hirr,
    (kOmMTheta_injective hr hirr).comp (CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ _ _ _),
    (kOmMTheta_injective hr hirr).comp
      (CFSG.RankThree.PartOne.CTP.shortBlock_injective_even hirr 3 finOne),
    kOmMTheta_longBlock hK hr hirr hk3, kOmMTheta_shortBlock hK hr hirr hk3⟩

end Theta

end CFSG.SeitzReduction.SymplecticPilot
