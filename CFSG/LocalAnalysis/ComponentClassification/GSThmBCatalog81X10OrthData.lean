module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthHyp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcTrans
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThreeTools

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self)

variable {K : Type} [Field K] {d : ℕ}

structure X10Data (R : GL (Fin d) K) (g : similarityPairs (oQ R))
    (M : Subgroup (GL (Fin d) K)) (Q : ℕ) : Prop where
  le : M ≤ matrixDerived (oQ R)
  perf : ⁅M, M⁆ = M
  fix : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ g)
  comp : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
    (autFixed (oκ _ g)))
  hyp : X10Hyp (oκ _ g) ((M.subgroupOf (matrixDerived (oQ R))).map (projH _)) Q

theorem map_projH_conj {R R' : GL (Fin d) K} {M : Subgroup (GL (Fin d) K)}
    (hM : M ≤ matrixDerived (oQ R)) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, oQ R' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * oQ R v) :
    ((M.map (MulAut.conj S).toMonoidHom).subgroupOf (matrixDerived (oQ R'))).map (projH _) =
      ((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).map
        (oTransport S ν hS).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨X', hX', rfl⟩
    obtain ⟨m, hm, hmX⟩ := mem_subgroupOf.1 hX'
    refine ⟨projH _ ⟨m, hM hm⟩, ⟨⟨m, hM hm⟩, mem_subgroupOf.2 hm, rfl⟩, ?_⟩
    change oTransport S ν hS (projH _ ⟨m, hM hm⟩) = projH _ X'
    rw [oTransport_proj]
    congr 1
    apply Subtype.ext
    rw [coe_derivedTransport, ← hmX]
    rfl
  · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨derivedTransport S ν hS X, mem_subgroupOf.2 ⟨X, mem_subgroupOf.1 hX, ?_⟩, ?_⟩
    · rw [coe_derivedTransport]
      rfl
    · change projH _ (derivedTransport S ν hS X) = oTransport S ν hS (projH _ X)
      rw [oTransport_proj]

namespace X10Data

variable {R : GL (Fin d) K} {g : similarityPairs (oQ R)} {M : Subgroup (GL (Fin d) K)} {Q : ℕ}

theorem transport [Finite K] {R' : GL (Fin d) K} (h : X10Data R g M Q) (S : GL (Fin d) K)
    (ν : Kˣ) (hS : ∀ v, oQ R' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * oQ R v) :
    X10Data R' (transPair S ν hS g) (M.map (MulAut.conj S).toMonoidHom) Q := by
  obtain ⟨hQs, hQc⟩ := DX.transport_comp h.le S ν hS h.fix h.comp
  refine ⟨?_, ?_, hQs, hQc, ?_⟩
  · rw [← map_matrixDerived_conj S ν hS]
    exact map_mono h.le
  · rw [← Subgroup.map_commutator, h.perf]
  · rw [map_projH_conj h.le S ν hS, ← oTransport_kappa]
    exact h.hyp.map (oTransport S ν hS)

theorem of_kappa_eq {g' : similarityPairs (oQ R)} (h : X10Data R g M Q)
    (hg : oκ _ g = oκ _ g') : X10Data R g' M Q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [hg] at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

theorem false_of_e8 (h : X10Data R g M Q) {X Y Z : matrixDerived (oQ R)}
    (hX : projH _ X ∈ (M.subgroupOf (matrixDerived (oQ R))).map (projH _))
    (hY : projH _ Y ∈ (M.subgroupOf (matrixDerived (oQ R))).map (projH _))
    (hZ : projH _ Z ∈ (M.subgroupOf (matrixDerived (oQ R))).map (projH _))
    (hT : E8Triple (projH _ X) (projH _ Y) (projH _ Z)) : False :=
  h.hyp.noE8 _ hX _ hY _ hZ hT

end X10Data

theorem projH_ne_one {Q : QuadraticForm K (Fin d → K)} {X : matrixDerived Q}
    (hX : ∀ c : Kˣ, (X : GL (Fin d) K) ≠ GeneralLinearGroup.scalar (Fin d) c) :
    projH _ X ≠ 1 := by
  intro h1
  have h1' : X ∈ (StatedScalars (Fin d) K).subgroupOf (matrixDerived Q) :=
    (QuotientGroup.eq_one_iff X).mp h1
  rw [mem_subgroupOf] at h1'
  obtain ⟨c, hc⟩ := h1'
  exact hX c hc.symm

theorem signGL_mul_signGL (A B : Finset (Fin d)) :
    signGL K A * signGL K B = signGL K (symmDiff A B) := by
  apply Units.ext
  rw [Units.val_mul, coe_signGL, coe_signGL, coe_signGL, signMat, signMat, signMat,
    diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    simp [hA, hB, Finset.mem_symmDiff]

theorem signGL_ne_scalar (h2 : (2 : K) ≠ 0) {T : Finset (Fin d)} (hT : T.Nonempty)
    (hTc : Tᶜ.Nonempty) (c : Kˣ) : signGL K T ≠ GeneralLinearGroup.scalar (Fin d) c := by
  intro h
  obtain ⟨i, hi⟩ := hT
  obtain ⟨j, hj⟩ := hTc
  have e : ∀ k, (signGL K T : Matrix (Fin d) (Fin d) K) k k = c := fun k => by
    rw [h, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq]
  have ei := e i
  have ej := e j
  rw [coe_signGL, signMat, diagonal_apply_eq] at ei ej
  simp only [hi, ↓reduceIte, Finset.mem_compl.1 hj] at ei ej
  exact h2 (by linear_combination ej - ei)

theorem e8Triple_sign (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K (Fin d → K)}
    {A B C : Finset (Fin d)} (hA : signGL K A ∈ matrixDerived Q)
    (hB : signGL K B ∈ matrixDerived Q) (hC : signGL K C ∈ matrixDerived Q)
    (h7 : ∀ T ∈ ({A, B, C, symmDiff A B, symmDiff A C, symmDiff B C,
      symmDiff (symmDiff A B) C} : Finset (Finset (Fin d))), T.Nonempty ∧ Tᶜ.Nonempty) :
    E8Triple (projH _ (⟨signGL K A, hA⟩ : matrixDerived Q)) (projH _ ⟨signGL K B, hB⟩)
      (projH _ ⟨signGL K C, hC⟩) := by
  have hsq : ∀ (T : Finset (Fin d)) (hT : signGL K T ∈ matrixDerived Q),
      projH _ (⟨signGL K T, hT⟩ : matrixDerived Q) * projH _ ⟨signGL K T, hT⟩ = 1 := by
    intro T hT
    rw [← map_mul]
    have : (⟨signGL K T, hT⟩ : matrixDerived Q) * ⟨signGL K T, hT⟩ = 1 :=
      Subtype.ext (Units.ext (by
        rw [Subgroup.coe_mul, Units.val_mul, coe_signGL, signMat_mul_self]
        rfl))
    rw [this, map_one]
  have hmul : ∀ (T U : Finset (Fin d)) (hT : signGL K T ∈ matrixDerived Q)
      (hU : signGL K U ∈ matrixDerived Q),
      projH _ (⟨signGL K T, hT⟩ : matrixDerived Q) * projH _ ⟨signGL K U, hU⟩ =
        projH _ (⟨signGL K (symmDiff T U), signGL_mul_signGL (K := K) T U ▸ mul_mem hT hU⟩ :
          matrixDerived Q) := by
    intro T U hT hU
    rw [← map_mul]
    congr 1
    exact Subtype.ext (signGL_mul_signGL T U)
  have hcomm : ∀ (T U : Finset (Fin d)) (hT : signGL K T ∈ matrixDerived Q)
      (hU : signGL K U ∈ matrixDerived Q),
      projH _ (⟨signGL K T, hT⟩ : matrixDerived Q) * projH _ ⟨signGL K U, hU⟩ =
        projH _ (⟨signGL K U, hU⟩ : matrixDerived Q) * projH _ ⟨signGL K T, hT⟩ := by
    intro T U hT hU
    rw [hmul, hmul]
    congr 1
    exact Subtype.ext (show signGL K (symmDiff T U) = signGL K (symmDiff U T) by
      rw [symmDiff_comm])
  have hne : ∀ (T : Finset (Fin d)) (hT : signGL K T ∈ matrixDerived Q), T.Nonempty →
      Tᶜ.Nonempty → projH _ (⟨signGL K T, hT⟩ : matrixDerived Q) ≠ 1 := fun T hT h1 h2' =>
    projH_ne_one fun c => signGL_ne_scalar h2 h1 h2' c
  have hm := fun T hT => h7 T hT
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hm
  obtain ⟨⟨hA1, hA2⟩, ⟨hB1, hB2⟩, ⟨hC1, hC2⟩, ⟨hAB1, hAB2⟩, ⟨hAC1, hAC2⟩, ⟨hBC1, hBC2⟩,
    ⟨hABC1, hABC2⟩⟩ := hm
  refine ⟨hsq A hA, hsq B hB, hsq C hC, hcomm A B hA hB, hcomm A C hA hC, hcomm B C hB hC,
    hne A hA hA1 hA2, hne B hB hB1 hB2, hne C hC hC1 hC2, ?_, ?_, ?_, ?_⟩
  · rw [hmul]
    exact hne _ _ hAB1 hAB2
  · rw [hmul]
    exact hne _ _ hAC1 hAC2
  · rw [hmul]
    exact hne _ _ hBC1 hBC2
  · rw [hmul, hmul]
    exact hne _ _ hABC1 hABC2

section Images

variable {H : Subgroup (GL (Fin d) K)}

theorem projH_comm_of_scalar {X Y : H} (c : Kˣ)
    (h : (X : GL (Fin d) K) * Y = GeneralLinearGroup.scalar (Fin d) c * (Y * X)) :
    projH H X * projH H Y = projH H Y * projH H X := by
  rw [← map_mul, ← map_mul, projH_eq_projH_iff, mem_subgroupOf]
  refine ⟨c⁻¹, ?_⟩
  change _ = ((X * Y)⁻¹ : GL (Fin d) K) * (Y * X)
  rw [h, _root_.mul_inv_rev, mul_assoc, ← map_inv,
    ← (commute_scalar c⁻¹ ((Y : GL (Fin d) K) * (X : GL (Fin d) K))).eq, ← mul_assoc,
    inv_mul_cancel, one_mul]

theorem projH_sq_of_scalar {X : H} (c : Kˣ)
    (h : (X : GL (Fin d) K) * X = GeneralLinearGroup.scalar (Fin d) c) :
    projH H X * projH H X = 1 := by
  rw [← map_mul]
  exact (QuotientGroup.eq_one_iff (X * X)).mpr (mem_subgroupOf.mpr ⟨c, h.symm⟩)

end Images

theorem left_mul_inv {Q : QuadraticForm K (Fin d → K)} {g h : similarityPairs Q}
    (hg : g.val.right = 1) (hh : h.val.right = 1) :
    (g * h⁻¹ : similarityPairs Q).val.left = g.val.left * h.val.left⁻¹ := by
  change (g.val * h.val⁻¹).left = _
  simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, hg, hh, inv_one, map_one,
    MulAut.one_apply]

theorem X10Data.false_of_e4 {R : GL (Fin d) K} {g : similarityPairs (oQ R)}
    {M : Subgroup (GL (Fin d) K)} {Q : ℕ} (h : X10Data R g M Q) (hker : OKer (oQ R))
    (hσ : g.val.right = 1) {X Y : GL (Fin d) K} (hXH : X ∈ matrixDerived (oQ R))
    (hYH : Y ∈ matrixDerived (oQ R)) {a b e : Kˣ}
    (hXX : X * X = GeneralLinearGroup.scalar (Fin d) a)
    (hYY : Y * Y = GeneralLinearGroup.scalar (Fin d) b)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin d) e * (Y * X))
    (hXS : X * g.val.left = g.val.left * X) (hYS : Y * g.val.left = g.val.left * Y)
    (hXM : ∀ m ∈ M, X * m = m * X) (hYM : ∀ m ∈ M, Y * m = m * Y)
    (hX1 : ∀ c : Kˣ, X ≠ GeneralLinearGroup.scalar (Fin d) c)
    (hY1 : ∀ c : Kˣ, Y ≠ GeneralLinearGroup.scalar (Fin d) c)
    (hXY1 : ∀ c : Kˣ, X * Y ≠ GeneralLinearGroup.scalar (Fin d) c)
    (hXs : ∀ c : Kˣ, X ≠ GeneralLinearGroup.scalar (Fin d) c * g.val.left)
    (hYs : ∀ c : Kˣ, Y ≠ GeneralLinearGroup.scalar (Fin d) c * g.val.left)
    (hXYs : ∀ c : Kˣ, X * Y ≠ GeneralLinearGroup.scalar (Fin d) c * g.val.left) : False := by
  set H := matrixDerived (oQ R) with hH
  set x := projH H ⟨X, hXH⟩ with hx
  set y := projH H ⟨Y, hYH⟩ with hy
  have hfix : ∀ (Z : GL (Fin d) K) (hZ : Z ∈ H), Z * g.val.left = g.val.left * Z →
      oκ _ g (projH H ⟨Z, hZ⟩) = projH H ⟨Z, hZ⟩ := fun Z hZ hZS => by
    rw [kappa_proj]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, hσ, map_one, MulAut.one_apply, ← hZS, mul_inv_cancel_right]
  have hcen : ∀ (Z : GL (Fin d) K) (hZ : Z ∈ H), (∀ m ∈ M, Z * m = m * Z) →
      ∀ j ∈ (M.subgroupOf H).map (projH H), projH H ⟨Z, hZ⟩ * j = j * projH H ⟨Z, hZ⟩ := by
    rintro Z hZ hZM _ ⟨m, hm, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hZM _ (mem_subgroupOf.1 hm))
  have hiso : ∀ Z ∈ H, Z ∈ matrixIsometries (oQ R) := fun Z hZ =>
    matrixDerived_le_isometries _ hZ
  have hconj : ∀ (Z : GL (Fin d) K) (hZ : Z ∈ H),
      (∀ c : Kˣ, Z ≠ GeneralLinearGroup.scalar (Fin d) c * g.val.left) →
      MulAut.conj (projH H ⟨Z, hZ⟩) ≠ oκ _ g := by
    intro Z hZ hZs he
    have e : oκ _ (linPair Z (hiso Z hZ) * g⁻¹) = 1 := by
      rw [map_mul, map_inv, oκ_linPair_eq_conj (hiso Z hZ) hZ]
      change MulAut.conj (projH H ⟨Z, hZ⟩) * (oκ _ g)⁻¹ = 1
      rw [he, mul_inv_cancel]
    obtain ⟨-, c, hc⟩ := hker _ e
    rw [left_mul_inv (linPair_right Z (hiso Z hZ)) hσ, linPair_left] at hc
    apply hZs c
    rw [hc, inv_mul_cancel_right]
  have hmulxy : x * y = projH H ⟨X * Y, mul_mem hXH hYH⟩ := by
    rw [hx, hy, ← map_mul]
    rfl
  refine h.hyp.noE4 x y (hfix X hXH hXS) (hfix Y hYH hYS) (hcen X hXH hXM) (hcen Y hYH hYM)
    (projH_sq_of_scalar (X := ⟨X, hXH⟩) a hXX) (projH_sq_of_scalar (X := ⟨Y, hYH⟩) b hYY)
    (projH_comm_of_scalar (X := ⟨X, hXH⟩) (Y := ⟨Y, hYH⟩) e hXY) (projH_ne_one hX1)
    (projH_ne_one hY1) ?_ (hconj X hXH hXs) (hconj Y hYH hYs) ?_
  · rw [hmulxy]
    exact projH_ne_one hXY1
  · rw [hmulxy]
    refine hconj _ _ fun c hc => hXYs c ?_
    exact hc

theorem X10Data.commute_left {R : GL (Fin d) K} {g : similarityPairs (oQ R)}
    {M : Subgroup (GL (Fin d) K)} {Q : ℕ} (h : X10Data R g M Q) (hσ : g.val.right = 1) :
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

end CFSG.ComponentClassification.GSThmB.X10Orth
