module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def barE : K ≃+* K :=
  { h.bar with
    invFun := h.bar
    left_inv := h.bar_bar
    right_inv := h.bar_bar }

theorem barE_apply (c : K) : barE h c = h.bar c := rfl

theorem eq_one_or_barE {τ : K ≃+* K} (hτ : τ * τ = 1) : τ = 1 ∨ τ = barE h := by
  classical
  have := h.finite
  have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) DFunLike.coe_injective
  have : Fintype (RingAut K) := Fintype.ofFinite _
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2⟩ := hne
  have hb1 : barE h ≠ 1 := fun hb => by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (by rw [← barE_apply, hb]; rfl)
  have hbb : barE h * barE h = 1 := RingEquiv.ext fun c => h.bar_bar c
  have hsub : ({1, barE h, τ} : Finset (RingAut K)) ⊆
      Finset.univ.filter (fun a : RingAut K => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq, hbb]
    · rw [sq, hτ]
  have hcard := (Finset.card_le_card hsub).trans
    (IsCyclic.card_pow_eq_one_le (α := RingAut K) (by norm_num : 0 < 2))
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] at hcard
  · omega
  · simpa using fun e => h2 e.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hb1.symm, fun e => h1 e.symm⟩

theorem field_mul_self_eq_one {A B : unitaryIsom3 h} {τ : K ≃+* K}
    (hsq : (psuConj h A * psuField h τ) * (psuConj h A * psuField h τ) = psuConj h B) :
    τ * τ = 1 := by
  set A' : unitaryIsom3 h := ⟨glAut τ A, glAut_mem_unitaryIsom3 τ A.2⟩ with hA'
  have h1 : psuField h τ * psuConj h A = psuConj h A' * psuField h τ := by
    rw [hA', ← psuField_mul_psuConj_mul_inv]
    group
  have h2 : psuConj h (B⁻¹ * (A * A')) * psuField h (τ * τ) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, ← hsq]
    calc (psuConj h A * psuField h τ * (psuConj h A * psuField h τ))⁻¹ *
          (psuConj h A * psuConj h A') * (psuField h τ * psuField h τ)
        = (psuConj h A * (psuField h τ * psuConj h A) * psuField h τ)⁻¹ *
          (psuConj h A * psuConj h A') * (psuField h τ * psuField h τ) := by group
      _ = 1 := by rw [h1]; group
  exact (eq_one_of_psuConj_mul_psuField_eq_one _ _ h2).1

theorem exists_scalar_of_fix {A : unitaryIsom3 h} {τ : K ≃+* K} {g : unitarySU p f K 3}
    (hg : (psuConj h A * psuField h τ) (g : unitaryPSU h 3) = (g : unitaryPSU h 3)) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ 3 = 1 ∧
      (A : GL (Fin 3) K) * glAut τ (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c * g := by
  rw [MulAut.mul_apply, psuField_mk, psuConj_mk] at hg
  obtain ⟨c, hc1, hc3, hc⟩ := mem_unitaryScalars.mp ((QuotientGroup.eq_iff_div_mem).mp hg)
  refine ⟨c, hc1, hc3, ?_⟩
  rw [Subgroup.coe_div, coe_suConj, coe_suField, Subgroup.coe_inv] at hc
  exact div_eq_iff_eq_mul.mp hc

theorem scalar_mem_unitaryIsom3 {c : Kˣ} (hc : h.norm (c : K) = 1) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm hc

theorem psuConj_scalar {c : Kˣ} (hc : h.norm (c : K) = 1) :
    psuConj h ⟨GeneralLinearGroup.scalar (Fin 3) c, scalar_mem_unitaryIsom3 h hc⟩ = 1 :=
  CFSG.RankThree.PartTwo.KFacts.psuConj_eq_one_of_coe_eq_scalar rfl

theorem norm_det_of_mem {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) :
    h.norm ((GeneralLinearGroup.det A : Kˣ) : K) = 1 := by
  have h1 := congrArg Matrix.det (mem_unitaryIsom3.mp hA)
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one] at h1
  rw [UnitaryFieldData.norm, GeneralLinearGroup.val_det_apply, mul_comm]
  exact h1

theorem exists_eq_conj_of_sq {A : unitaryIsom3 h} {g : unitarySU p f K 3}
    (hsq : psuConj h A * psuConj h A = MulAut.conj (g : unitaryPSU h 3)) :
    ∃ g' : unitarySU p f K 3, psuConj h A = MulAut.conj (g' : unitaryPSU h 3) := by
  rw [conj_mk_eq_psuConj] at hsq
  set G : unitaryIsom3 h := ⟨(g : GL (Fin 3) K), unitarySU_le_unitaryIsom3 g.2⟩ with hG
  have h1 : psuConj h (G⁻¹ * (A * A)) * psuField h 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_mul, hsq, map_inv, inv_mul_cancel]
  obtain ⟨-, ω, hω, hωA⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul] at hωA
  have hAA : (A : GL (Fin 3) K) * A = (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ω := by
    rw [← hωA, show (G : GL (Fin 3) K) = g from rfl]
    group
  have hdetg : GeneralLinearGroup.det (g : GL (Fin 3) K) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact ((mem_unitarySU_iff h).mp g.2).1)
  set δ : Kˣ := GeneralLinearGroup.det (A : GL (Fin 3) K) with hδ
  have hδω : δ * δ = ω ^ 3 := by
    have := congrArg GeneralLinearGroup.det hAA
    rwa [map_mul, map_mul, hdetg, one_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at this
  have hnδ : h.norm (δ : K) = 1 := norm_det_of_mem h A.2
  set l : Kˣ := δ * ω⁻¹ with hl
  have hnl : h.norm (l : K) = 1 := by
    have hω' : h.norm ((ω⁻¹ : Kˣ) : K) = 1 := by
      rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv]
      rw [UnitaryFieldData.norm] at hω
      rw [hω, inv_one]
    rw [hl, Units.val_mul, UnitaryFieldData.norm, map_mul]
    rw [UnitaryFieldData.norm] at hnδ hω'
    linear_combination (h.bar (ω⁻¹ : Kˣ) * (ω⁻¹ : Kˣ)) * hnδ + hω'
  have hl3 : l ^ 3 = δ := by
    rw [hl, mul_pow, inv_pow, ← hδω]
    group
  set A' : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) l⁻¹ * A with hA'
  have hA'mem : A' ∈ unitarySU p f K 3 := by
    have hnl' : h.norm ((l⁻¹ : Kˣ) : K) = 1 := by
      rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv]
      rw [UnitaryFieldData.norm] at hnl
      rw [hnl, inv_one]
    have hu : A' ∈ unitaryIsom3 h := mul_mem (scalar_mem_unitaryIsom3 h hnl') A.2
    refine (mem_unitarySU_iff h).mpr ⟨?_, hu⟩
    rw [← GeneralLinearGroup.val_det_apply, hA', map_mul, GeneralLinearGroup.det_scalar,
      Fintype.card_fin, ← hδ, inv_pow, hl3, inv_mul_cancel, Units.val_one]
  refine ⟨⟨A', hA'mem⟩, ?_⟩
  rw [conj_mk_eq_psuConj]
  have hAeq : A = ⟨GeneralLinearGroup.scalar (Fin 3) l, scalar_mem_unitaryIsom3 h hnl⟩ *
      ⟨A', unitarySU_le_unitaryIsom3 hA'mem⟩ := by
    apply Subtype.ext
    show (A : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) l * (GeneralLinearGroup.scalar (Fin 3) l⁻¹ * A)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hAeq, map_mul, psuConj_scalar h hnl, one_mul]

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
