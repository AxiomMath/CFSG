module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddMain
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat
  conj_injective_of_mulEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def OddShape {Q : QuadraticForm K (Fin d → K)} {X : Type} [Group X]
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)) (t : X) : Prop :=
  ∃ U : Submodule K (Fin d → K), Module.finrank K U ≤ 2 ∧
    ∀ x ∈ oddCentralizerCore t, ∃ (B : GL (Fin d) K) (hB : B ∈ matrixIsometries Q),
      socleAction θ x = oκ Q (linPair B hB) ∧
      ∀ v, ((B : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v ∈ U

theorem transPair_linPair {Q Q' : QuadraticForm K (Fin d → K)} (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) {B : GL (Fin d) K}
    (hB : B ∈ matrixIsometries Q) (hB' : S * B * S⁻¹ ∈ matrixIsometries Q') :
    transPair S ν hS (linPair B hB) = linPair (S * B * S⁻¹) hB' := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rw [transPair_left, linPair_right, map_one, MulAut.one_apply, linPair_left, linPair_left]
  · rfl

theorem conj_mem_matrixIsometries {Q Q' : QuadraticForm K (Fin d → K)} (S : GL (Fin d) K)
    (ν : Kˣ) (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) {B : GL (Fin d) K}
    (hB : B ∈ matrixIsometries Q) : S * B * S⁻¹ ∈ matrixIsometries Q' := by
  rw [← map_matrixIsometries_conj S ν hS]
  exact ⟨B, hB, rfl⟩

theorem conj_sub_one_mulVec (S B : GL (Fin d) K) (v : Fin d → K) :
    (((S * B * S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v =
      (S : Matrix (Fin d) (Fin d) K) *ᵥ (((B : Matrix (Fin d) (Fin d) K) - 1) *ᵥ
        (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v)) := by
  have e : (S : Matrix (Fin d) (Fin d) K) *ᵥ (((S⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [sub_mulVec, sub_mulVec, mulVec_sub, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
    ← mulVec_mulVec, one_mulVec, one_mulVec, e]

theorem OddShape.transport {Q Q' : QuadraticForm K (Fin d → K)} {X : Type} [Group X]
    {θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)} {t : X}
    (h : OddShape θ t) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    OddShape (θ.trans (oTransport S ν hS)) t := by
  obtain ⟨U, hU, hx⟩ := h
  refine ⟨U.map (Matrix.mulVecLin (S : Matrix (Fin d) (Fin d) K)),
    (Submodule.finrank_map_le _ _).trans hU, fun x hxO => ?_⟩
  obtain ⟨B, hB, hBx, hBU⟩ := hx x hxO
  have hB' := conj_mem_matrixIsometries S ν hS hB
  refine ⟨S * B * S⁻¹, hB', ?_, fun v => ?_⟩
  · rw [socleAction_trans, hBx, oTransport_kappa, transPair_linPair S ν hS hB hB']
  · rw [conj_sub_one_mulVec]
    exact ⟨_, hBU _, rfl⟩

theorem OddShape.of_transport {Q Q' : QuadraticForm K (Fin d → K)} {X : Type} [Group X]
    {θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)} {t : X}
    (S : GL (Fin d) K) (ν : Kˣ) (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)
    (h : OddShape (θ.trans (oTransport S ν hS)) t) : OddShape θ t := by
  obtain ⟨U, hU, hx⟩ := h
  have hSi := inv_similarity S ν hS
  refine ⟨U.map (Matrix.mulVecLin ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)),
    (Submodule.finrank_map_le _ _).trans hU, fun x hxO => ?_⟩
  obtain ⟨B', hB', hBx, hBU⟩ := hx x hxO
  have hB := conj_mem_matrixIsometries S⁻¹ ν⁻¹ hSi hB'
  refine ⟨S⁻¹ * B' * S⁻¹⁻¹, hB, ?_, fun v => ?_⟩
  · apply (MulAut.congr (oTransport S ν hS)).injective
    have e1 : S * (S⁻¹ * B' * S⁻¹⁻¹) * S⁻¹ = B' := by group
    have hB'' := conj_mem_matrixIsometries S ν hS hB
    rw [← socleAction_trans, hBx, oTransport_kappa, transPair_linPair S ν hS hB hB'']
    congr 1
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rw [linPair_left, linPair_left, e1]
    · rfl
  · rw [conj_sub_one_mulVec]
    exact ⟨_, hBU _, rfl⟩

variable (K) in
@[expose] def suppOn (J : Finset (Fin d)) : Submodule K (Fin d → K) where
  carrier := {v | ∀ i ∉ J, v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    rw [Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c a ha i hi
    rw [Pi.smul_apply, ha i hi, smul_zero]

theorem finrank_suppOn_le (J : Finset (Fin d)) : Module.finrank K (suppOn K J) ≤ J.card := by
  let f : suppOn K J →ₗ[K] (J → K) :=
    { toFun := fun v j => (v : Fin d → K) j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J
    · exact congrFun hab ⟨i, hi⟩
    · rw [a.2 i hi, b.2 i hi]
  have := LinearMap.finrank_le_finrank_of_injective hf
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this

theorem sub_one_mulVec_mem_suppOn {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {R : GL (Fin d) K} (hR : R ∈ oIsoBlock K hw J) (v : Fin d → K) :
    ((R : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v ∈ suppOn K J := by
  intro i hi
  have hsupp := ((mem_oIsoBlock_iff hw).1 hR).2
  rw [sub_mulVec, one_mulVec, Pi.sub_apply, mulVec, dotProduct,
    Finset.sum_eq_single i (fun j _ hj => by rw [hsupp i j (Or.inl hi), ite_eq_right (Ne.symm hj),
      zero_mul]) (by simp), hsupp i i (Or.inl hi), ite_eq_left rfl, one_mul, sub_self]

variable [Finite K]

theorem torus_shape (hK : ringChar K ≠ 2) (hd : 7 ≤ d) (hdodd : Odd d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hJ2 : J.card = 2) (hNFc : BlockNF w Jᶜ)
    (hker : OKer (oQ (diagGL hw))) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ (diagGL hw))))
    {t : X} (hsurj : OSurjX θ t)
    (ht : socleAction θ t = oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) :
    oddCentralizerCore t = ⊥ ∨ OddShape θ t := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ (socleAction θ).range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction _ x
  have hcore := (hsurj.core hsimple hnab).of_eq ht
  have hJd : 2 * J.card ≠ d := by
    obtain ⟨k, hk⟩ := hdodd
    omega
  have hJc5 : 5 ≤ Jᶜ.card := by
    have := card_compl_add J
    omega
  have hJc : BlockOK K w Jᶜ := hNFc.blockOK (by omega) (fun h => by omega)
  have hmem : ∀ x ∈ oddCentralizerCore t,
      socleAction θ x ∈ oddCoreIn (socleAction θ).range (oκ _ (sgnPair h2 hw J)) := by
    intro x hx
    rw [← ht, ← map_oddCentralizerCore_of_injective hψ]
    exact ⟨x, hx, rfl⟩
  by_cases h3 : Nat.card K = 3
  · left
    have hbot := split_two_oddCoreIn_eq_bot_three h3 hK hw hker hcore hinj hB hJ2 hJd hJc
    rw [eq_bot_iff]
    intro x hx
    have h1 := hmem x hx
    rw [hbot, mem_bot, ← map_one (socleAction θ)] at h1
    exact hψ h1
  · right
    refine ⟨suppOn K J, (finrank_suppOn_le J).trans hJ2.le, fun x hx => ?_⟩
    obtain ⟨R, hR, hRJ, hRx⟩ := split_two_oddCoreIn hK hw hker hcore hinj hB hJd hJc (hmem x hx)
    exact ⟨R, hR, hRx, sub_one_mulVec_mem_suppOn hw hRJ⟩

theorem inner_odd_shape (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d) (hdodd : Odd d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right = 1) (htg : socleAction θ t = oκ _ g) :
    oddCentralizerCore t = ⊥ ∨ OddShape θ t := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have htorus : ∀ (A'' : GL (Fin d) K) (hA'' : A'' ∈ matrixIsometries (oQ R)),
      oκ _ g = oκ _ (linPair A'' hA'') →
      (A'' : Matrix (Fin d) (Fin d) K)ᵀ * Rm * A'' = Rm →
      (A'' : Matrix (Fin d) (Fin d) K) * A'' = 1 →
      Module.finrank K (eigM (A'' : Matrix (Fin d) (Fin d) K)) = 2 →
      oddCentralizerCore t = ⊥ ∨ OddShape θ t := by
    intro A'' hA'' hκ'' hAR'' hA2'' hM2''
    obtain ⟨hab, c, hcA, horth, hdiag, -, hNFc⟩ := exists_split_nf hK hR hAR'' hA2''
    obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA'' hab c hcA horth hdiag
    have hJ2 : (famJ hab).card = 2 := by rw [card_famJ]; exact hM2''
    have hP : 3 ≤ Module.finrank K (eigP (A'' : Matrix (Fin d) (Fin d) K)) := by
      have := finrank_eig_add h2 hA2''
      omega
    have ht' : socleAction (θ.trans (oTransport S 1 hS)) t =
        oκ _ (sgnPair h2 hw (famJ hab)) := by
      rw [socleAction_trans, htg, hκ'', oTransport_kappa, heq]
    rcases torus_shape hK hd7 hdodd hw hJ2 (hNFc hP) (hker.transport S 1 hS) hsimple hnab
      (θ.trans (oTransport S 1 hS)) (hsurj.transport S 1 hS) ht' with h | h
    · exact Or.inl h
    · exact Or.inr (OddShape.of_transport S 1 hS h)
  have hκ1 : oκ (oQ R) g ≠ 1 := by
    intro h1
    rw [h1, ← map_one (socleAction θ)] at htg
    have := hψ htg
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← htg, ← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨-, c, hc⟩ := hker _ hgg
  have hc' : g.val.left * g.val.left = GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc]
    change _ = g.val.left * glFieldAut (Fin d) K g.val.right g.val.left
    rw [hg1, map_one, MulAut.one_apply]
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 R hR g.val).1 g.2
  rw [hg1, show (R : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = R from by ext; rfl] at hμ
  obtain ⟨m, hm0, hA'R, hA'2⟩ := exists_isometric_involution hdodd hμ hc'
  obtain ⟨A', hA'def⟩ : ∃ A' : GL (Fin d) K,
      A' = GeneralLinearGroup.scalar (Fin d) (Units.mk0 m hm0)⁻¹ * g.val.left := ⟨_, rfl⟩
  have hA'c : (A' : Matrix (Fin d) (Fin d) K) = m⁻¹ • (g.val.left : Matrix (Fin d) (Fin d) K) := by
    rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d) (Fin d) K, Am = A' := ⟨_, rfl⟩
  have hAR : Amᵀ * Rm * Am = Rm := by rw [hAm, hA'c]; exact hA'R
  have hA2 : Am * Am = 1 := by rw [hAm, hA'c]; exact hA'2
  have hA' : A' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR A').2 ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2
      (by rw [← hAm]; exact hAR))
  have hκ : oκ _ g = oκ _ (linPair A' hA') := by
    refine oκ_eq_of_left_eq (c := Units.mk0 m hm0) (by rw [hg1, linPair_right]) ?_
    rw [linPair_left, hA'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hnegR : (-Am)ᵀ * Rm * (-Am) = Rm := by
    rw [transpose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hAR]
  have hneg : -A' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR (-A')).2 ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2
      (by rw [Units.val_neg, ← hAm]; exact hnegR))
  have hnegA : GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) * (-A') = A' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_neg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Units.val_neg, Units.val_one, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul, neg_one_smul, neg_neg]
  have hκneg : oκ _ g = oκ _ (linPair (-A') hneg) := by
    rw [hκ]
    refine oκ_eq_of_left_eq (c := -1) rfl ?_
    rw [linPair_left, linPair_left, hnegA]
  have hsum := finrank_eig_add h2 hA2
  have hM1 : 1 ≤ Module.finrank K (eigM Am) := by
    by_contra h0
    have hbot : eigM Am = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have htop : eigP Am = ⊤ := by
      have := (isCompl_eig h2 hA2).sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    have h1 : Am = 1 := eq_one_of_forall_mulVec fun v => mem_eigP.1 (htop ▸ Submodule.mem_top)
    apply hκ1
    rw [hκ]
    have : linPair A' hA' = 1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact Units.ext (by rw [linPair_left, ← hAm]; exact h1)
      · rfl
    rw [this, map_one]
  have hP1 : 1 ≤ Module.finrank K (eigP Am) := by
    by_contra h0
    have hbot : eigP Am = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have htop : eigM Am = ⊤ := by
      have := (isCompl_eig h2 hA2).sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    have h1 : -Am = 1 := eq_one_of_forall_mulVec fun v => by
      rw [neg_mulVec, mem_eigM.1 (htop ▸ Submodule.mem_top), neg_neg]
    apply hκ1
    rw [hκneg]
    have : linPair (-A') hneg = 1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact Units.ext (by rw [linPair_left, Units.val_neg, ← hAm]; exact h1)
      · rfl
    rw [this, map_one]
  by_cases hM2 : Module.finrank K (eigM Am) = 2
  · exact htorus A' hA' hκ (by rw [← hAm]; exact hAR) (by rw [← hAm]; exact hA2)
      (by rw [← hAm]; exact hM2)
  by_cases hP2 : Module.finrank K (eigP Am) = 2
  · refine htorus (-A') hneg hκneg (by rw [Units.val_neg, ← hAm]; exact hnegR)
      (by rw [Units.val_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← hAm]; exact hA2) ?_
    rw [Units.val_neg, ← hAm, eigM_neg]
    exact hP2
  left
  obtain ⟨hab, c, hcA, horth, hdiag, hNF, hNFc⟩ := exists_split_nf hK hR hAR hA2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA' hab c
    (by rw [← hAm]; exact hcA) horth hdiag
  have hJcard : (famJ hab).card = Module.finrank K (eigM Am) := card_famJ hab
  have hJccard : (famJ hab)ᶜ.card = Module.finrank K (eigP Am) := by
    rw [Finset.card_compl, Fintype.card_fin, hJcard]
    omega
  set θ' := θ.trans (oTransport S 1 hS) with hθ'
  have ht' : socleAction θ' t = oκ _ (sgnPair h2 hw (famJ hab)) := by
    rw [hθ', socleAction_trans, htg, hκ, oTransport_kappa, heq]
  have hψ' := socleAction_injective hsimple hnab θ'
  have hbot := split_oddCoreIn_eq_bot_of_nf hK hd7 hdodd hw (hker.transport S 1 hS)
    (((hsurj.transport S 1 hS).core hsimple hnab).of_eq ht')
    (conj_injective_of_mulEquiv hsimple hnab θ')
    (by rintro _ ⟨x, rfl⟩; exact conj_mem_range_socleAction _ x)
    (by omega) (by omega) (by omega) (by omega) (fun h3 => hNF (by omega))
    (fun h3 => hNFc (by omega))
  rw [eq_bot_iff]
  intro x hx
  have h1 : socleAction θ' x ∈ oddCoreIn (socleAction θ').range (socleAction θ' t) := by
    rw [← map_oddCentralizerCore_of_injective hψ']
    exact ⟨x, hx, rfl⟩
  rw [ht', hbot, mem_bot, ← map_one (socleAction θ')] at h1
  exact hψ' h1

theorem field_oddCentralizerCore_eq_bot (hK : ringChar K ≠ 2) (hd5 : 5 ≤ d) {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right ≠ 1) (htg : socleAction θ t = oκ _ g) : oddCentralizerCore t = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← htg, ← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨hσ2', c, hc⟩ := hker _ hgg
  have hσ2 : g.val.right ^ 2 = 1 := by rw [← (sq_val _ g).2]; exact hσ2'
  have hc' : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c := by rw [← (sq_val _ g).1, hc]
  obtain ⟨e', hu, hσ⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hg1
  obtain ⟨wF, hwF, S, ν, hS, heq⟩ := exists_field_transport hu hℓ2 h2 (by omega) hR hσ hc'
  set θ' := θ.trans (oTransport S ν hS) with hθ'
  have ht' : socleAction θ' t = oκ _ (barPair hu h2 hwF.1) := by
    rw [hθ', socleAction_trans, htg, oTransport_kappa, heq]
  have hψ' := socleAction_injective hsimple hnab θ'
  have hbot := field_oddCoreIn_eq_bot hu hℓ2 h2 hd5 hwF (hker.transport S ν hS)
    (conj_injective_of_mulEquiv hsimple hnab θ')
    (by rintro _ ⟨x, rfl⟩; exact conj_mem_range_socleAction _ x)
    (((hsurj.transport S ν hS).core hsimple hnab).of_eq ht')
  rw [eq_bot_iff]
  intro x hx
  have h1 : socleAction θ' x ∈ oddCoreIn (socleAction θ').range (socleAction θ' t) := by
    rw [← map_oddCentralizerCore_of_injective hψ']
    exact ⟨x, hx, rfl⟩
  rw [ht', hbot, mem_bot, ← map_one (socleAction θ')] at h1
  exact hψ' h1

end CFSG.ComponentClassification.Burgoyne.C
