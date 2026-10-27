module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthMain
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self)
open CFSG.ComponentClassification.GSThmB.X10Orth (E8Triple map_projH_conj e8Triple_kron_sign
  kron_signPair_mem kron_perm_mem pi4 commutator_perm4 pi4_permMatrix_sq sign01_pi4 sign02_pi4
  kronI_diag_pi4_ne projH_ne_one projH_sq_of_scalar projH_comm_of_scalar signGL_mul_signGL
  signGL_ne_scalar pairSet_props pairSet_symmDiff symmDiff_pair_pair exists_perfect_lift
  even_of_skew)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

structure PcData (R : GL (Fin d) K) (g : similarityPairs (oQ R))
    (M : Subgroup (GL (Fin d) K)) : Prop where
  le : M ≤ matrixDerived (oQ R)
  perf : ⁅M, M⁆ = M
  fix : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ g)
  comp : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
    (autFixed (oκ _ g)))
  noE8 : ∀ u ∈ (M.subgroupOf (matrixDerived (oQ R))).map (projH _),
    ∀ v ∈ (M.subgroupOf (matrixDerived (oQ R))).map (projH _),
    ∀ w ∈ (M.subgroupOf (matrixDerived (oQ R))).map (projH _), ¬ E8Triple u v w

namespace PcData

variable {R : GL (Fin d) K} {g : similarityPairs (oQ R)} {M : Subgroup (GL (Fin d) K)}

theorem transport [Finite K] {R' : GL (Fin d) K} (h : PcData R g M) (S : GL (Fin d) K)
    (ν : Kˣ) (hS : ∀ v, oQ R' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * oQ R v) :
    PcData R' (transPair S ν hS g) (M.map (MulAut.conj S).toMonoidHom) := by
  obtain ⟨hQs, hQc⟩ := DX.transport_comp h.le S ν hS h.fix h.comp
  refine ⟨?_, ?_, hQs, hQc, ?_⟩
  · rw [← map_matrixDerived_conj S ν hS]
    exact map_mono h.le
  · rw [← Subgroup.map_commutator, h.perf]
  · rw [map_projH_conj h.le S ν hS]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hT
    exact h.noE8 u hu v hv w hw (X10Orth.E8Triple.comap (φ := (oTransport S ν hS).toMonoidHom)
      (oTransport S ν hS).injective hT)

theorem commute_left (h : PcData R g M) (hσ : g.val.right = 1) :
    ∀ X ∈ M, X * g.val.left = g.val.left * X := by
  set H := matrixDerived (oQ R) with hH
  set S := g.val.left with hSdef
  have hperfH : ⁅M.subgroupOf H, M.subgroupOf H⁆ = M.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.le, h.perf]
  have hfixP : ∀ X ∈ M.subgroupOf H, oκ _ g (projH H X) = projH H X :=
    fun X hX => h.fix ⟨X, hX, rfl⟩
  intro X hX
  have e := kappa_eq_of_fix g hperfH hfixP (X := ⟨X, h.le hX⟩) (mem_subgroupOf.2 hX)
  rw [hσ] at e
  have e2 : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = X := by
    ext
    rfl
  change (S : Matrix (Fin d) (Fin d) K) * ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map
    ⇑(1 : K ≃+* K) * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = X at e
  rw [e2] at e
  have e' : S * X * S⁻¹ = X := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact e)
  calc X * S = S * X * S⁻¹ * S := by rw [e']
    _ = S * X := by group

theorem map_eq_isoCent [Finite K] (hK : ringChar K ≠ 2)
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (h : PcData R g M) (hσ : g.val.right = 1)
    (hN : Group.IsSolvable (⁅isoCent R g.val.left, isoCent R g.val.left⁆ :
        Subgroup (GL (Fin d) K)) ∨
      IsQuasisimple (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K))) :
    (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)) ≤
        matrixDerived (oQ R) ∧
      (M.subgroupOf (matrixDerived (oQ R))).map (projH _) =
        ((⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)).subgroupOf
          (matrixDerived (oQ R))).map (projH _) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ R) with hH
  set S := g.val.left with hSdef
  set N : Subgroup (GL (Fin d) K) := ⁅isoCent R S, isoCent R S⁆ with hNdef
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  have hSM := h.commute_left hσ
  have hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K R := fun X hX =>
    (mem_matrixIsometries_oQ h2 R hR X).1 (matrixDerived_le_isometries _ (h.le hX))
  have hMC : M ≤ isoCent R S := fun X hX =>
    ⟨hiso X hX, mem_centralizer_singleton_iff.2 (hSM X hX)⟩
  have hMN : M ≤ N := by
    rw [← h.perf]
    exact commutator_mono hMC hMC
  have hNH : N ≤ H := by
    rw [hH, matrixDerived_oQ h2 R hR]
    exact commutator_mono inf_le_left inf_le_left
  refine ⟨hNH, ?_⟩
  set Pn := (N.subgroupOf H).map (projH H) with hPn
  have hQP : Qb ≤ Pn := map_mono fun g hg => mem_subgroupOf.2 (hMN (mem_subgroupOf.1 hg))
  have hPs : Pn ≤ autFixed (oκ _ g) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [DX.mem_autFixed_iff, kappa_proj]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, hσ, map_one, MulAut.one_apply]
    have hxC : (x : GL (Fin d) K) ∈ isoCent R S := commutator_le_self _ (mem_subgroupOf.1 hx)
    have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 hxC).2
    change S * (x : GL (Fin d) K) * S⁻¹ = x
    rw [← hc, mul_inv_cancel_right]
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs h.comp
  set φ := (projH H).comp ((N.subgroupOf H).subtype.comp
    (subgroupOfEquivOfLe hNH).symm.toMonoidHom) with hφ
  have hφr : φ.range = Pn := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (subgroupOfEquivOfLe hNH).symm.surjective, Subgroup.map_top, Subgroup.range_subtype]
  rcases hN with hsol | hqs
  · have : Group.IsSolvable φ.range := Group.isSolvable_of_surjective φ.rangeRestrict_surjective
    rw [hφr] at this
    exact (C.not_le_of_isSolvable hQP hQc' this hQP).elim
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hqs φ with hb | hqr
  · rw [hφr] at hb
    rw [hb] at hQP
    exact (C.ne_bot_of_isPComponent h.fix h.comp (le_bot_iff.1 hQP)).elim
  rw [hφr] at hqr
  exact C.eq_of_le_of_isQuasisimple hQP le_rfl hQc' hqr

theorem false_of_isoCent_e8 [Finite K] (hK : ringChar K ≠ 2)
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (h : PcData R g M) (hσ : g.val.right = 1)
    (hN : Group.IsSolvable (⁅isoCent R g.val.left, isoCent R g.val.left⁆ :
        Subgroup (GL (Fin d) K)) ∨
      IsQuasisimple (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    {X Y Z : GL (Fin d) K}
    (hX : X ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    (hY : Y ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    (hZ : Z ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    (hT : ∀ (hXH : X ∈ matrixDerived (oQ R)) (hYH : Y ∈ matrixDerived (oQ R))
      (hZH : Z ∈ matrixDerived (oQ R)),
      E8Triple (projH _ (⟨X, hXH⟩ : matrixDerived (oQ R))) (projH _ ⟨Y, hYH⟩)
        (projH _ ⟨Z, hZH⟩)) : False := by
  obtain ⟨hNH, heq⟩ := h.map_eq_isoCent hK hR hσ hN
  have hin : ∀ (W : GL (Fin d) K) (hW : W ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ :
      Subgroup (GL (Fin d) K))), projH _ (⟨W, hNH hW⟩ : matrixDerived (oQ R)) ∈
        (M.subgroupOf (matrixDerived (oQ R))).map (projH _) := fun W hW => by
    rw [heq]
    exact ⟨⟨W, hNH hW⟩, mem_subgroupOf.2 hW, rfl⟩
  exact h.noE8 _ (hin X hX) _ (hin Y hY) _ (hin Z hZ) (hT _ _ _)

end PcData

theorem false_of_pc_data [Finite K] (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ f) {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K}
    (hRm : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1)
    (hgA : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    {M : Subgroup (GL (Fin (2 * n)) K)} (h : PcData R gs M) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hRm, blkDiag_transpose, wMat, diagonal_transpose]
  have hN := C.isQuasisimple_isoCent_pc hK hℓ hKc hc (by omega) hRm hgA
  have hsign : ∀ i i' : Fin n, i ≠ i' → signGL K (pairSet {i, i'}) ∈
      (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * n)) K)) :=
    fun i i' hii' => kron_signPair_mem hRm hgA hii'
  rcases Nat.lt_or_ge 4 n with h5 | h4
  ·
    set i₀ : Fin n := ⟨0, by omega⟩
    set i₁ : Fin n := ⟨1, by omega⟩
    set i₂ : Fin n := ⟨2, by omega⟩
    set i₃ : Fin n := ⟨3, by omega⟩
    have hd : ∀ a b : Fin n, (a : ℕ) ≠ b → a ≠ b := fun a b hab h' => hab (by rw [h'])
    have h01 := hd i₀ i₁ (by simp [i₀, i₁])
    have h02 := hd i₀ i₂ (by simp [i₀, i₂])
    have h03 := hd i₀ i₃ (by simp [i₀, i₃])
    have h12 := hd i₁ i₂ (by simp [i₁, i₂])
    have h13 := hd i₁ i₃ (by simp [i₁, i₃])
    have h23 := hd i₂ i₃ (by simp [i₂, i₃])
    exact h.false_of_isoCent_e8 hK hRs hσ (Or.inr hN) (hsign _ _ h01) (hsign _ _ h02)
      (hsign _ _ h03) fun hX hY hZ => e8Triple_kron_sign h2 h5 h01 h02 h03 h12 h13 h23 hX hY hZ
  ·
    obtain rfl : n = 4 := by omega
    set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
    set τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1
    set W := kronGL K 4 ⁅permGL K 4 σ, permGL K 4 τ⁆ with hWdef
    have hWm : (W : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (pi4.permMatrix K) := by
      rw [hWdef, coe_kronGL, coe_commutator_permGL, commutator_perm4]
    have hW := kron_perm_mem (K := K) hRm hgA σ τ
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    have h02 : (0 : Fin 4) ≠ 2 := by decide
    have h12 : (1 : Fin 4) ≠ 2 := by decide
    refine h.false_of_isoCent_e8 hK hRs hσ (Or.inr hN) (hsign _ _ h01) (hsign _ _ h02) hW
      fun hX hY hZ => ?_
    have hXm : ((signGL K (pairSet ({0, 1} : Finset (Fin 4))) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (signMat K {0, 1}) := by
      rw [coe_signGL, kronI_signMat]
    have hYm : ((signGL K (pairSet ({0, 2} : Finset (Fin 4))) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (signMat K {0, 2}) := by
      rw [coe_signGL, kronI_signMat]
    have hsq : ∀ T : Finset (Fin (2 * 4)), signGL K T * signGL K T = 1 := fun T =>
      Units.ext (by rw [Units.val_mul, coe_signGL, signMat_mul_self, Units.val_one])
    have hWW : W * W = 1 := Units.ext (by
      rw [Units.val_mul, hWm, ← map_mul, pi4_permMatrix_sq, map_one, Units.val_one])
    have hXW : signGL K (pairSet ({0, 1} : Finset (Fin 4))) * W =
        GeneralLinearGroup.scalar (Fin (2 * 4)) 1 * (W * signGL K (pairSet {0, 1})) := by
      rw [map_one, one_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hXm, hWm, ← map_mul, ← map_mul, sign01_pi4]
    have hYW : signGL K (pairSet ({0, 2} : Finset (Fin 4))) * W =
        GeneralLinearGroup.scalar (Fin (2 * 4)) (-1) * (W * signGL K (pairSet {0, 2})) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hYm, hWm, ← map_mul, ← map_mul,
        sign02_pi4, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_neg, Units.val_one,
        ← Matrix.smul_one_eq_diagonal, neg_one_smul, Matrix.neg_mul, Matrix.one_mul, map_neg]
    have hXY : signGL K (pairSet ({0, 1} : Finset (Fin 4))) * signGL K (pairSet {0, 2}) =
        GeneralLinearGroup.scalar (Fin (2 * 4)) 1 *
          (signGL K (pairSet {0, 2}) * signGL K (pairSet {0, 1})) := by
      rw [map_one, one_mul, signGL_mul_signGL, signGL_mul_signGL, symmDiff_comm]
    have hne_d : ∀ (v : Fin 4 → K) (Z : matrixDerived (oQ R)),
        ((Z : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
          kronI K 4 (diagonal v * pi4.permMatrix K) → projH _ Z ≠ 1 := fun v Z hZ =>
      projH_ne_one fun c' hc' => kronI_diag_pi4_ne v c' (by rw [← hZ, hc'])
    have hsgn : ∀ (T : Finset (Fin 4)) (Z : matrixDerived (oQ R)), T.Nonempty → Tᶜ.Nonempty →
        (Z : GL (Fin (2 * 4)) K) = signGL K (pairSet T) → projH _ Z ≠ 1 :=
      fun T Z h1 h1' hZ => projH_ne_one fun c' hc' => signGL_ne_scalar h2
        (pairSet_props ⟨h1, h1'⟩).1 (pairSet_props ⟨h1, h1'⟩).2 c' (hZ.symm.trans hc')
    have hone : GeneralLinearGroup.scalar (Fin (2 * 4)) (1 : Kˣ) = 1 := map_one _
    refine ⟨projH_sq_of_scalar 1 (by rw [hone]; exact hsq _),
      projH_sq_of_scalar 1 (by rw [hone]; exact hsq _),
      projH_sq_of_scalar 1 (by rw [hone]; exact hWW),
      projH_comm_of_scalar 1 hXY, projH_comm_of_scalar 1 hXW, projH_comm_of_scalar (-1) hYW,
      hsgn {0, 1} _ (by decide) ⟨2, by decide⟩ rfl, hsgn {0, 2} _ (by decide) ⟨1, by decide⟩ rfl,
      hne_d (fun _ => 1) _ (by rw [hWm, diagonal_one, Matrix.one_mul]), ?_, ?_, ?_, ?_⟩
    · rw [← map_mul]
      refine hsgn {1, 2} _ (by decide) ⟨0, by decide⟩ ?_
      change signGL K (pairSet {0, 1}) * signGL K (pairSet {0, 2}) = _
      rw [signGL_mul_signGL, ← pairSet_symmDiff, symmDiff_pair_pair h01 h02 h12]
    · rw [← map_mul]
      refine hne_d (fun i => if i ∈ ({0, 1} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 1}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, hXm, hWm, ← map_mul]
      rfl
    · rw [← map_mul]
      refine hne_d (fun i => if i ∈ ({0, 2} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 2}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, hYm, hWm, ← map_mul]
      rfl
    · rw [← map_mul, ← map_mul]
      refine hne_d ((fun i => if i ∈ ({0, 1} : Finset (Fin 4)) then -1 else 1) *
        fun i => if i ∈ ({0, 2} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 1}) * signGL K (pairSet {0, 2}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, Units.val_mul, hXm, hYm, hWm, ← map_mul, ← map_mul, signMat, signMat,
        diagonal_mul_diagonal]
      rfl

theorem false_of_pc_noE8 {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (hKc : Nat.card K = ℓ ^ e) {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = -1)
    {J : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hJt : J ≤ centralizer ({projH _ ⟨T, hT⟩} : Set _))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({projH _ ⟨T, hT⟩} : Set _))))
    (hE8 : ∀ u ∈ J, ∀ v ∈ J, ∀ w ∈ J, ¬ X10Orth.E8Triple u v w) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨M, hMH, hMperf, hMJ⟩ := exists_perfect_lift (C.commutator_eq_of_isPComponent hJt hJ)
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  set g := linPair T hTiso with hg
  have hκ : oκ _ g = conjProjH (matrixDerived (oQ R)) ⟨T, hT⟩ := oκ_linPair_eq_conj hTiso hT
  have hfixC : autFixed (oκ _ g) =
      centralizer ({projH _ ⟨T, hT⟩} : Set (StatedProj (matrixDerived (oQ R)))) := by
    ext y
    rw [DX.mem_autFixed_iff, hκ, mem_centralizer_singleton_iff]
    change projH _ ⟨T, hT⟩ * y * (projH _ ⟨T, hT⟩)⁻¹ = y ↔
      y * projH _ ⟨T, hT⟩ = projH _ ⟨T, hT⟩ * y
    constructor
    · intro hy
      calc y * projH _ ⟨T, hT⟩ =
          projH _ ⟨T, hT⟩ * y * (projH _ ⟨T, hT⟩)⁻¹ * projH _ ⟨T, hT⟩ := by rw [hy]
        _ = projH _ ⟨T, hT⟩ * y := by group
    · intro hy
      rw [← hy, mul_inv_cancel_right]
  have hdata : PcData R g M := by
    refine ⟨hMH, hMperf, ?_, ?_, ?_⟩
    · rw [hMJ, hfixC]
      exact hJt
    · rw [hMJ, hfixC]
      exact hJ
    · rw [hMJ]
      exact hE8
  have hσ : g.val.right = 1 := linPair_right T hTiso
  set Tm := (T : Matrix (Fin d) (Fin d) K) with hTm
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hiso : Tmᵀ * Rm * Tm = Rm := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  have hTT' : Tm * (-Tm) = 1 := by rw [Matrix.mul_neg, hT2, neg_neg]
  have hε : Tmᵀ * Rm = (-1 : K) • (Rm * Tm) := by
    calc Tmᵀ * Rm = Tmᵀ * Rm * (Tm * (-Tm)) := by rw [hTT', Matrix.mul_one]
      _ = Tmᵀ * Rm * Tm * (-Tm) := by rw [Matrix.mul_assoc (Tmᵀ * Rm)]
      _ = Rm * (-Tm) := by rw [hiso]
      _ = (-1 : K) • (Rm * Tm) := by rw [Matrix.mul_neg, neg_one_smul]
  have hS2 : Tm * Tm = (-1 : K) • 1 := by rw [neg_one_smul]; exact hT2
  have hc0 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨n, hn⟩ := even_of_skew h2 hε
  obtain rfl : d = 2 * n := by omega
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc0 hS2 hε (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨hS, hl, hr⟩ := exists_transport_of_gram hgramR₁ hσ
  have hgA : ((transPair H₁⁻¹ 1 hS g).val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat (-1 : K)) := by
    rw [hl, Units.val_mul, Units.val_mul]
    exact inv_mul_mul_eq hAH₁
  exact false_of_pc_data hK hℓ hKc hc0 (by omega) hR₁m hr hgA (hdata.transport H₁⁻¹ 1 hS)

end CFSG.ComponentClassification.GSThmB.QPUCl
