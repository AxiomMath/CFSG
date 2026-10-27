module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Comp
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGU
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameU

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one uMat)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal val_of_mem_scal
  mem_center_of_mem_scal)

variable {p f : ℕ}

section Split

variable {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem split_of_two_pComponents (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E V] (hn : finrank E V = 4) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M₁ M₂ : Subgroup (centralizer
      ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} : Set (sesqProjUnitary h B)))}
    (h₁ : IsPComponent 2 M₁) (h₂ : IsPComponent 2 M₂) (hne : M₁ ≠ M₂) :
    ∃ l : E, l ≠ 0 ∧ unitaryOp A * unitaryOp A = (l ^ 2) • 1 ∧ h.norm l = 1 ∧
      finrank E (eigenPlus l (unitaryOp A)) = 2 ∧ finrank E (eigenMinus l (unitaryOp A)) = 2 ∧
      IsCompl (eigenPlus l (unitaryOp A)) (eigenMinus l (unitaryOp A)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, hl0, hAA, hN, hP, hM, hcompl, hsplit, hpaired, -, hnormal, hindex, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hA
  rw [← range_centralizerImageHom] at hnormal hindex
  have := hnormal
  have := CatalogueRelativeB.quotient_solvable_of_index_le_two _ hindex
  obtain ⟨N₁, N₂, hN₁, hN₂, hNne⟩ := Sp4Rec.exists_pComponent_lifts (centralizerImageHom A)
    (ker_centralizerImageHom_le_center A) h₁ h₂ hne
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hP1 := Submodule.one_le_finrank_iff.mpr hP
  rcases hN with hN | hN
  · obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    have hM1 := Submodule.one_le_finrank_iff.mpr hM
    obtain ⟨⟨J, hJ⟩, ⟨J', hJ'⟩⟩ := Sp4Rec.exists_of_two_pComponents_prod
      (fun J₁ J₂ k₁ k₂ => (Sp4Rec.sesqUnitary_pComponent_eq h hp hP1 (hsymm _) hlP k₁ k₂).2)
      (fun J₁ J₂ k₁ k₂ => (Sp4Rec.sesqUnitary_pComponent_eq h hp hM1 (hsymm _) hlM k₁ k₂).2)
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₁)
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₂)
      (fun k => hNne (map_injective e.injective k))
    have d₁ := (Sp4Rec.sesqUnitary_pComponent_eq h hp hP1 (hsymm _) hlP hJ hJ).1
    have d₂ := (Sp4Rec.sesqUnitary_pComponent_eq h hp hM1 (hsymm _) hlM hJ' hJ').1
    exact ⟨l, hl0, hAA, hN, by omega, by omega, hcompl⟩
  · exfalso
    obtain ⟨-, -, -, -, -, -, e, -⟩ := hpaired hN
    obtain ⟨bP⟩ : Nonempty (Basis (Fin (finrank E (eigenPlus l (unitaryOp A)))) E
        (eigenPlus l (unitaryOp A))) := ⟨Module.finBasis E _⟩
    set e' := e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv) with he'
    obtain ⟨-, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ E hP1 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e' _ hN₁)
    obtain ⟨-, -, -, k₂, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ E hP1 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e' _ hN₂)
    exact hNne (map_injective e'.injective (k₁.trans k₂.symm))

end Split

variable {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uStar_smul {n : ℕ} (c : K) (M : Matrix (Fin n) (Fin n) K) :
    uStar h (c • M) = h.bar c • uStar h M := by
  ext i j
  simp [uStar, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply]

theorem unitaryOp_toSesqUnitary (g : unitarySU p f K 4) :
    unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 4 g) =
      Matrix.toLin' ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  LinearMap.ext fun x => (EscapingNotOddUnitary.toSesqUnitary_apply h 4 g x).trans
    (Matrix.toLin'_apply _ _).symm

theorem exists_frame_of_pairConfig [Finite K] (hp2 : p ≠ 2) {g : unitarySU p f K 4}
    {K₁ K₂ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hc : Sp4Rec.PairConfig (StatedProj (StatedSU 4 (p ^ f) K)) (QuotientGroup.mk g) K₁ K₂) :
    ∃ (l : K) (Q : GL (Fin 4) K), h.norm l = 1 ∧ l ^ 4 = 1 ∧
      uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) =
        (Q : Matrix (Fin 4) (Fin 4) K) * X1 l := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set ι := EscapingNotOddUnitary.projEmbed h 4 (by norm_num) with hιdef
  have hι : Function.Injective ι := EscapingNotOddUnitary.projEmbed_injective h 4 (by norm_num)
  have : ι.range.Normal := by
    rw [hιdef, EscapingNotOddUnitary.range_projEmbed]
    exact EscapingNotOddUnitary.toProj_range_normal h 4
  set A := EscapingNotOddUnitary.toSesqUnitary h 4 g with hAdef
  have hιg : ι (QuotientGroup.mk g) =
      (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) A := rfl
  obtain ⟨hK₁le, hK₁⟩ := Sp4Rec.isPComponent_map_of_normal ι hι hc.K_le hc.isPComponent_K
  obtain ⟨hK₂le, hK₂⟩ := Sp4Rec.isPComponent_map_of_normal ι hι hc.K'_le hc.isPComponent_K'
  have hne : (K₁.map ι).subgroupOf (centralizer ({ι (QuotientGroup.mk g)} : Set _)) ≠
      (K₂.map ι).subgroupOf (centralizer ({ι (QuotientGroup.mk g)} : Set _)) := by
    intro k
    apply hc.ne
    have h1 := subgroupOf_inj.mp k
    rw [inf_of_le_left hK₁le, inf_of_le_left hK₂le] at h1
    exact map_injective hι h1
  rw [hιg] at hK₁ hK₂ hne
  have hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h (stdHermForm h 4)) = 2 := by
    change orderOf ((QuotientGroup.mk' _) A) = 2
    rw [← hιg, orderOf_injective ι hι, hc.orderOf_x]
  obtain ⟨l, hl0, hAA, hN, hP, hM, hcompl⟩ := split_of_two_pComponents h hp2
    (Module.finrank_fin_fun K) (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) hA hK₁
    hK₂ hne
  set M := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hMdef
  have hop : unitaryOp A = Matrix.toLin' M := unitaryOp_toSesqUnitary h g
  set X : Matrix (Fin 4) (Fin 4) K := l⁻¹ • M with hX
  have hXop : Matrix.toLin' X = invSMulOp l (unitaryOp A) := by
    rw [hX, map_smul, hop]
    rfl
  have hTp : ∀ v ∈ eigenPlus l (unitaryOp A), Matrix.toLin' X v = (1 : K) • v := by
    intro v hv
    have hv' : (invSMulOp l (unitaryOp A) - 1) v = 0 := hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv'
    rw [hXop, hv', one_smul]
  have hTm : ∀ v ∈ eigenMinus l (unitaryOp A), Matrix.toLin' X v = (-1 : K) • v := by
    intro v hv
    have hv' : (invSMulOp l (unitaryOp A) + 1) v = 0 := hv
    rw [LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg] at hv'
    rw [hXop, hv', neg_one_smul]
  have hdetX : X.det = 1 := by
    have := CatFactsL4U4.det_eq_of_isCompl_smul hcompl hTp hTm
    rw [hP, hM, LinearMap.det_toLin'] at this
    rw [this]
    norm_num
  have hdetg : M.det = 1 := det_SU h g
  have hl4 : l ^ 4 = 1 := by
    have e := hdetX
    rw [hX, det_smul, hdetg, Fintype.card_fin, mul_one, inv_pow] at e
    exact inv_eq_one.mp e
  have hMM : M * M = (l ^ 2) • 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, ← hop, ← Module.End.mul_eq_comp, hAA, map_smul, Matrix.toLin'_one]
    rfl
  have hXX : X * X = 1 := by
    rw [hX, smul_mul_smul_comm, hMM, smul_smul, ← pow_two, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hl0), one_smul]
  have hbl : h.bar l * l = 1 := by
    have := hN
    rw [UnitaryFieldData.norm] at this
    rw [mul_comm]
    exact this
  have hXU : uStar h X * X = 1 := by
    have hgU := unitary_SU h g
    rw [hX, uStar_smul, smul_mul_smul_comm, hgU, map_inv₀, ← mul_inv, hbl, inv_one, one_smul]
  set Xs : unitarySU p f K 4 := toSU h X hdetX hXU with hXs
  have hXs' : ((Xs : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X := rfl
  have hne1 : X ≠ 1 := by
    intro h1
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp (by omega : 1 ≤ finrank K (eigenMinus l (unitaryOp A))))
    have e := hTm v hv
    rw [h1, Matrix.toLin'_one, LinearMap.id_apply, neg_one_smul] at e
    apply hv0
    have h2v : (2 : K) • v = 0 := by rw [two_smul]; nth_rewrite 1 [e]; exact neg_add_cancel v
    exact (smul_eq_zero.mp h2v).resolve_left h2K
  have hnem1 : X ≠ -1 := by
    intro h1
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp (by omega : 1 ≤ finrank K (eigenPlus l (unitaryOp A))))
    have e := hTp v hv
    rw [h1, map_neg, Matrix.toLin'_one, LinearMap.neg_apply, LinearMap.id_apply,
      one_smul] at e
    apply hv0
    have h2v : (2 : K) • v = 0 := by rw [two_smul]; nth_rewrite 2 [← e]; exact add_neg_cancel v
    exact (smul_eq_zero.mp h2v).resolve_left h2K
  obtain ⟨Qm, hQu, hXQ⟩ := CatFactsL4U4.StabU.exists_orthonormal_eigenframe h hp2 Xs
    (by rw [hXs']; exact hXX) (by rw [hXs']; exact hne1) (by rw [hXs']; exact hnem1)
  rw [hXs'] at hXQ
  have hQdet : Qm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hQu
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨l, GeneralLinearGroup.mkOfDetNeZero Qm hQdet, hN, hl4, hQu, ?_⟩
  change M * Qm = Qm * X1 l
  have hMX : M = l • X := by rw [hX, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  rw [hMX, smul_mul_assoc, hXQ, Catalog7L4.X1_eq_smul l, mul_smul_comm]

theorem conj_mem_SU {Q : GL (Fin 4) K}
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1)
    (g : unitarySU p f K 4) : Q⁻¹ * (g : GL (Fin 4) K) * Q ∈ unitarySU p f K 4 := by
  have hQ' : Q ∈ uMat h 4 := hQ
  have hQi : uStar h ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := inv_mem hQ'
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, det_SU h g, mul_one, ← det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  · rw [Units.val_mul, Units.val_mul]
    exact unitary_mul h (unitary_mul h hQi (unitary_SU h g)) hQ

theorem unitary_inv {Q : GL (Fin 4) K}
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1) :
    uStar h ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hQ' : Q ∈ uMat h 4 := hQ
  exact inv_mem hQ'

@[expose] def conjSU (Q : GL (Fin 4) K)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1) :
    unitarySU p f K 4 ≃* unitarySU p f K 4 where
  toFun g := ⟨Q⁻¹ * g * Q, conj_mem_SU h hQ g⟩
  invFun g := ⟨Q * g * Q⁻¹, by
    have := conj_mem_SU h (unitary_inv h hQ) g
    rwa [inv_inv] at this⟩
  left_inv g := Subtype.ext (by
    show Q * (Q⁻¹ * (g : GL (Fin 4) K) * Q) * Q⁻¹ = g
    group)
  right_inv g := Subtype.ext (by
    show Q⁻¹ * (Q * (g : GL (Fin 4) K) * Q⁻¹) * Q = g
    group)
  map_mul' g g' := Subtype.ext (by
    show Q⁻¹ * ((g : GL (Fin 4) K) * g') * Q = Q⁻¹ * g * Q * (Q⁻¹ * g' * Q)
    group)

theorem coe_conjSU (Q : GL (Fin 4) K)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1)
    (g : unitarySU p f K 4) :
    (((conjSU h Q hQ g : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) := by
  change ((Q⁻¹ * (g : GL (Fin 4) K) * Q : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
  rw [Units.val_mul, Units.val_mul]

theorem conjSU_of_mem_scal (Q : GL (Fin 4) K)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1)
    {z : unitarySU p f K 4} (hz : z ∈ scal p f K) : conjSU h Q hQ z = z := by
  obtain ⟨c, hc⟩ := val_of_mem_scal hz
  apply SU_ext
  rw [coe_conjSU, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one]

theorem map_conjSU_scal (Q : GL (Fin 4) K)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1) :
    (scal p f K).map (conjSU h Q hQ).toMonoidHom = scal p f K := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, conjSU_of_mem_scal h Q hQ hw]
    exact hw
  · intro hz
    exact ⟨z, hz, conjSU_of_mem_scal h Q hQ hz⟩

@[expose] def uconj (Q : GL (Fin 4) K)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1) :
    StatedProj (StatedSU 4 (p ^ f) K) ≃* StatedProj (StatedSU 4 (p ^ f) K) :=
  QuotientGroup.congr (scal p f K) (scal p f K) (conjSU h Q hQ) (map_conjSU_scal h Q hQ)

theorem uconj_mk (Q : GL (Fin 4) K)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = 1)
    (g : unitarySU p f K 4) :
    uconj h Q hQ (QuotientGroup.mk g) = QuotientGroup.mk (conjSU h Q hQ g) :=
  rfl

end Catalog7U4

end CFSG.ComponentClassification.GSThmB
