module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTModel
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTData
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLHalves
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem bglu_q_eq {Y : Type} [Group Y] {q r : ℕ} (h : IsPSUn 3 q Y) (h' : IsPSUn 3 r Y) :
    q = r := by
  obtain ⟨p, a, hp, ha, rfl, h1⟩ := l514c_card_psu h
  obtain ⟨ℓ, b, hℓ, hb, rfl, h2⟩ := l514c_card_psu h'
  refine order_psu3_inj hp hℓ ha hb ?_
  rw [← h1, ← h2]
  ring

variable {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)

theorem bglu_exists_H (hq : 2 < p ^ f) {σ : F ≃+* F} (hσ : orderOf σ = 3) (A : unitaryIsom3 hF)
    (hcomm : psuConj hF A * psuField hF σ = psuField hF σ * psuConj hF A)
    (h3 : psuConj hF A ^ 3 = 1) :
    ∃ H : unitaryIsom3 hF,
      psuConj hF A * psuField hF σ = psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹ := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hα3 : (psuConj hF A * psuField hF σ) ^ 3 = 1 := by
    rw [Commute.mul_pow hcomm 3, h3, ← map_pow, hσ3, map_one, one_mul]
  have hαD : psuConj hF A * psuField hF σ ∉ (psuConj hF).range := by
    rintro ⟨B, hB⟩
    have h1 : psuField hF σ ∈ (psuConj hF).range := ⟨A⁻¹ * B, by rw [map_mul, map_inv, hB]; group⟩
    have h2 := (psuField_mem_range_psuConj_iff (h := hF)).1 h1
    rw [h2, orderOf_one] at hσ
    omega
  obtain ⟨τ, -, H, hH⟩ := unitary_order_three_field_descent hq _ hα3 hαD
  have hfτ : psuField hF τ =
      (psuConj hF H)⁻¹ * (psuConj hF A * psuField hF σ) * psuConj hF H := by
    rw [hH]; group
  have h2 : psuField hF (τ * σ⁻¹) = psuConj hF
      (H⁻¹ * A * ⟨glAut σ (H : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ H.2⟩) := by
    rw [map_mul, map_inv, hfτ, map_mul (psuConj hF), map_mul (psuConj hF), map_inv (psuConj hF),
      ← psuField_mul_psuConj_mul_inv σ H]
    group
  have hτσ : τ * σ⁻¹ = 1 := (psuField_mem_range_psuConj_iff (h := hF)).1 ⟨_, h2.symm⟩
  rw [mul_inv_eq_one.1 hτσ] at hH
  exact ⟨H, hH⟩

theorem bglu_not_scalar_fixed {σ : F ≃+* F} (A H : unitaryIsom3 hF)
    (hh : psuConj hF A * psuField hF σ = psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹)
    (hA1 : psuConj hF A ≠ 1) :
    ¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      c * ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j := by
  rintro ⟨c, hc0, hc⟩
  apply hA1
  have hσc : σ c ≠ 0 := (map_ne_zero σ).2 hc0
  set d : Fˣ := Units.mk0 (c * (σ c)⁻¹) (mul_ne_zero hc0 (inv_ne_zero hσc)) with hd
  have hs : glAut σ (H : GL (Fin 3) F) =
      (H : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) d := by
    apply Units.ext
    rw [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    have := hc i j
    rw [map_mul] at this
    simp only [Matrix.mul_diagonal, Matrix.map_apply]
    change σ (((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j * (c * (σ c)⁻¹)
    field_simp
    linear_combination this
  have hscal : (H : GL (Fin 3) F) * glAut σ ((H : GL (Fin 3) F)⁻¹) =
      GeneralLinearGroup.scalar (Fin 3) d⁻¹ := by
    rw [map_inv, hs, (commute_scalar d (H : GL (Fin 3) F)).eq, _root_.mul_inv_rev, map_inv]
    group
  have hmem : GeneralLinearGroup.scalar (Fin 3) d⁻¹ ∈ unitaryIsom3 hF := by
    rw [← hscal]
    exact mul_mem H.2 (glAut_mem_unitaryIsom3 σ (inv_mem H.2))
  have e1 : psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹ =
      psuConj hF (H * ⟨glAut σ ((H⁻¹ : unitaryIsom3 hF) : GL (Fin 3) F),
        glAut_mem_unitaryIsom3 σ (H⁻¹).2⟩) * psuField hF σ := by
    rw [map_mul, ← psuField_mul_psuConj_mul_inv σ H⁻¹, map_inv]
    group
  have e2 : (H * ⟨glAut σ ((H⁻¹ : unitaryIsom3 hF) : GL (Fin 3) F),
      glAut_mem_unitaryIsom3 σ (H⁻¹).2⟩ : unitaryIsom3 hF) = ⟨_, hmem⟩ :=
    Subtype.ext hscal
  rw [e1, e2, psuConj_scalar, one_mul] at hh
  exact mul_right_cancel (hh.trans (one_mul _).symm)

theorem bglu_model_join (hcore : BGL.SU3SubfieldJoin) (hq3 : p ^ f % 3 ≠ 0) (hq8 : p ^ f ≠ 8)
    {σ : F ≃+* F} (hσ : orderOf σ = 3) (H : unitaryIsom3 hF)
    (hnot : ¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      c * ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) :
    bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom = ⊤ := by
  have := hF.finite
  have hHu : (((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (· ^ (p ^ f)))ᵀ *
      ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have h1 := H.2
    rw [mem_unitaryIsom3] at h1
    have hb : (⇑hF.bar : F → F) = (· ^ (p ^ f)) := funext fun c => hF.bar_apply c
    rw [← hb]
    exact h1
  have hc := hcore F (p ^ f) hF.card_eq_sq hq3 hq8 σ hσ H hHu hnot
  set W : Subgroup (unitarySU p f F 3) :=
    (bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom).comap (unitaryProj hF 3)
    with hW
  have h1 : StatedSU 3 (p ^ f) F ⊓ BGL.fixGL σ ≤ W.map (unitarySU p f F 3).subtype := by
    intro s hs
    refine ⟨⟨s, hs.1⟩, ?_, rfl⟩
    change unitaryProj hF 3 ⟨s, hs.1⟩ ∈
      bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom
    exact Subgroup.mem_sup_left
      (mem_bgluSub.2 ⟨⟨s, hs.1⟩, (bglu_mem_fixGL_iff σ s).1 hs.2, rfl⟩)
  have h2 : (StatedSU 3 (p ^ f) F ⊓ BGL.fixGL σ).map
      (MulAut.conj (H : GL (Fin 3) F)).toMonoidHom ≤ W.map (unitarySU p f F 3).subtype := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨suConj hF H ⟨s, hs.1⟩, ?_, rfl⟩
    change unitaryProj hF 3 (suConj hF H ⟨s, hs.1⟩) ∈
      bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom
    have hmem : unitaryProj hF 3 ⟨s, hs.1⟩ ∈ bgluSub hF σ :=
      mem_bgluSub.2 ⟨⟨s, hs.1⟩, (bglu_mem_fixGL_iff σ s).1 hs.2, rfl⟩
    exact Subgroup.mem_sup_right ⟨_, hmem, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := unitaryProj_surjective hF 3 x
  obtain ⟨g', hg', hgg'⟩ := sup_le h1 h2 (hc g.2)
  have hg : g' = g := Subtype.ext hgg'
  rw [← hg]
  exact hg'

theorem bglu_pair_generation (hcore : BGL.SU3SubfieldJoin) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (hU : ∃ (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Nat.card F = q ^ 2 ∧ q % 3 ≠ 0 ∧
      q ≠ 8 ∧ Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSU 3 q F)))
    {b x : MulAut K} (hb : IsFieldAutThree b) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hx : IsInnDiagThree x) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hbx : b * x = x * b) :
    (⊤ : Subgroup K) ≤
      GLAPLayer 3 (Lemma512Ns.fixedSub b) ⊔ GLAPLayer 3 (Lemma512Ns.fixedSub (b * x)) := by
  obtain ⟨F0, hF0, hfin0, q, hcard0, hq3, hq8, ⟨e0⟩⟩ := hU
  obtain ⟨p, f, F, hFf, hF, η, σ, A, hσ, hq, hηb, hηx⟩ :=
    bglu_data hK ⟨F0, hF0, hfin0, q, hcard0, ⟨e0⟩⟩ hb hb1 hb3 hx
  have hFfin := hF.finite
  have hqe : q = p ^ f := bglu_q_eq ⟨F0, hF0, hfin0, hcard0, ⟨e0⟩⟩
    ⟨F, hFf, hFfin, hF.card_eq_sq, ⟨η.trans (psuO hF)⟩⟩
  subst hqe
  have hcomm : psuConj hF A * psuField hF σ = psuField hF σ * psuConj hF A := by
    have := congrArg (fun z : MulAut K => MulAut.congr η (centerDescend K z)) hbx
    simp only [map_mul] at this
    rw [hηb, hηx] at this
    exact this.symm
  have h3 : psuConj hF A ^ 3 = 1 := by
    rw [← hηx, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hA1 : psuConj hF A ≠ 1 := by
    intro h1
    apply hx1
    refine eq_one_of_centerDescend_eq_one hK ?_
    apply (MulAut.congr η).injective
    rw [hηx, h1, map_one]
  obtain ⟨H, hh⟩ := bglu_exists_H hF hq hσ A hcomm h3
  have hnot := bglu_not_scalar_fixed hF A H hh hA1
  have hN₁ : BglNSP (psuField hF σ) (bgluSub hF σ) := bgluSub_nsp hF hσ hq8
  have hjoin := bglu_model_join hF hcore hq3 hq8 hσ H hnot
  have hβ₂ : MulAut.congr η (centerDescend K (b * x)) =
      psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹ := by
    rw [map_mul, map_mul, hηb, hηx, ← hcomm]
    exact hh
  have hN₂ : BglNSP (psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹)
      ((bgluSub hF σ).map (psuConj hF H).toMonoidHom) := by
    refine bglNSP_map ((psuConj hF H).symm) ?_ hN₁
    change (psuConj hF H)⁻¹ * (psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹) *
      (psuConj hF H)⁻¹⁻¹ = _
    group
  have hB₁ := bglNSP_map η hηb hN₁
  have hB₂ := bglNSP_map η hβ₂ hN₂
  have hQ : (bgluSub hF σ).map η.symm.toMonoidHom ⊔
      ((bgluSub hF σ).map (psuConj hF H).toMonoidHom).map η.symm.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, hjoin, Subgroup.map_top_of_surjective _ η.symm.surjective]
  have hK1 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    have := hK.1
    rwa [commutator_def] at this
  have key := glaPLayer_fixSubgroup_sup_eq_top_of_perfect (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.ker_mk' _).le (QuotientGroup.mk'_surjective _) hK1 b (b * x)
    (centerDescend K b) (centerDescend K (b * x)) (fun _ => rfl) (fun _ => rfl) Nat.prime_three
    (bglNSP_le_layer hB₁) (bglNSP_le_layer hB₂) hQ
  exact le_of_eq key.symm

theorem bglFieldPairGenerationU_of_core (hcore : BGL.SU3SubfieldJoin) :
    BGLFieldPairGenerationU := by
  intro K _ _ hK hU b x hb hb1 hb3 hx hx1 hx3 hbx
  exact bglu_pair_generation hcore hK hU hb hb1 hb3 hx hx1 hx3 hbx

end CFSG.HardMathSupport.Solomon.Coordinator
