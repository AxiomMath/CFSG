module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModEbasis
public import Certificates.Certificate25142
public import CFSG.Sporadic.J4

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] noncomputable def liftS : J := wordProd xJ liftWordS * eta uJ 11 liftMaskS

@[expose] noncomputable def liftT : J := wordProd xJ liftWordT * eta uJ 11 liftMaskT

theorem liftWordS_letters : ∀ ℓ ∈ liftWordS, ℓ ∈ letters := by decide

theorem liftWordT_letters : ∀ ℓ ∈ liftWordT, ℓ ∈ letters := by decide

set_option maxRecDepth 100000 in
theorem liftWordS_act (i : Fin 11) : liftWordS.foldr act (2 ^ (i : ℕ)) = sRowMasks i := by
  revert i
  decide

set_option maxRecDepth 100000 in
theorem liftWordT_act (i : Fin 11) : liftWordT.foldr act (2 ^ (i : ℕ)) = tRowMasks i := by
  revert i
  decide

theorem Mx_liftElt (hM : MatFacts) (w : List ℤ) (c : ℕ) :
    Mx (wordProd xJ w * eta uJ 11 c) =
      rowsMatrix (liftRows (locMats ()) (locInvs ()) w c) := by
  rw [map_mul, Mx_wordProd hM, Mx_eta hM 11 le_rfl, ← rowsMatrix_mulRows]
  rfl

theorem lift_sq :
    liftS * liftS = 1 ∧ liftT * liftT = 1 ∧ (liftS * liftT) * (liftS * liftT) = 1 := by
  have hM := j4Facts.mat
  have h := Certificates.certificate25142
  unfold chkLift at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 h1)
    rw [rowsMatrix_mulRows, rowsMatrix_idRows, ← Mx_liftElt hM] at this
    rw [map_mul, map_one]
    exact this
  · apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 h2)
    rw [rowsMatrix_mulRows, rowsMatrix_idRows, ← Mx_liftElt hM] at this
    rw [map_mul, map_one]
    exact this
  · apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 h3)
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_idRows, ← Mx_liftElt hM,
      ← Mx_liftElt hM] at this
    rw [map_mul, map_mul, map_one]
    exact this

theorem liftS_mem : liftS ∈ Hj :=
  Hj.mul_mem (wordProd_mem_Hj liftWordS_letters)
    (Eg_le_Hj (eta_mem_Eg 11 le_rfl liftMaskS))

theorem liftT_mem : liftT ∈ Hj :=
  Hj.mul_mem (wordProd_mem_Hj liftWordT_letters)
    (Eg_le_Hj (eta_mem_Eg 11 le_rfl liftMaskT))

theorem conj_liftElt (hM : MatFacts) {w : List ℤ}
    (hw : ∀ ℓ ∈ w, ℓ ∈ letters) (c : ℕ) (i : Fin 11) :
    (wordProd xJ w * eta uJ 11 c) * uJ i * (wordProd xJ w * eta uJ 11 c)⁻¹ =
      eta uJ 11 (w.foldr act (2 ^ (i : ℕ))) := by
  have hcomm : eta uJ 11 c * uJ i = uJ i * eta uJ 11 c :=
    Eg_comm (elem_uJ hM) (eta_mem_Eg 11 le_rfl c) (u_mem_Eg i.2)
  have e : (wordProd xJ w * eta uJ 11 c) * uJ i * (wordProd xJ w * eta uJ 11 c)⁻¹ =
      wordProd xJ w * (eta uJ 11 c * uJ i * (eta uJ 11 c)⁻¹) * (wordProd xJ w)⁻¹ := by group
  rw [e, hcomm, mul_inv_cancel_right, ← eta_two_pow i.2 (u := uJ), wordProd_conj hM hw]

theorem maskMatrix_bits (m : Fin 11 → ℕ) (i j : Fin 11) :
    (m i).testBit j = decide (maskMatrix (ZMod 2) m i j = 1) := by
  simp only [maskMatrix, Matrix.of_apply]
  by_cases h : (m i).testBit j = true
  · simp [h]
  · have h' : (m i).testBit j = false := by simpa using h
    simp [h']

theorem liftData_J :
    LiftData (⊤ : Subgroup J) (Eg uJ 11) := by
  have hF := j4Facts
  have hM := hF.mat
  obtain ⟨hSS, hTT, hSTST⟩ := lift_sq
  refine ⟨fun i : Fin 11 => uJ i, liftS, liftT, fun i => u_mem_Eg i.2, ?_,
    (mem_Hloc_top hF).2 liftS_mem, (mem_Hloc_top hF).2 liftT_mem, hSS, hTT, hSTST, ?_, ?_⟩
  · intro c d hcd
    obtain ⟨m, hm, hmc⟩ := exists_mask 11 c
    obtain ⟨m', hm', hmd⟩ := exists_mask 11 d
    rw [ebasis_eq_eta uJ hmc, ebasis_eq_eta uJ hmd] at hcd
    have hmm : m = m' := eta_inj hM m hm m' hm' hcd
    subst hmm
    funext j
    have h3 : decide (c j = 1) = decide (d j = 1) := (hmc j).symm.trans (hmd j)
    rcases zmod_two_cases (c j) with hc | hc <;> rcases zmod_two_cases (d j) with hd | hd <;>
      rw [hc, hd] at h3 ⊢ <;> first | rfl | exact absurd h3 (by decide)
  · intro i
    rw [ebasis_eq_eta uJ (c := fun j => Smat i j) (m := sRowMasks i)
      (fun j => maskMatrix_bits sRowMasks i j)]
    show liftS * uJ i * liftS⁻¹ = _
    rw [liftS, conj_liftElt hM liftWordS_letters, liftWordS_act]
  · intro i
    rw [ebasis_eq_eta uJ (c := fun j => Tmat i j) (m := tRowMasks i)
      (fun j => maskMatrix_bits tRowMasks i j)]
    show liftT * uJ i * liftT⁻¹ = _
    rw [liftT, conj_liftElt hM liftWordT_letters, liftWordT_act]

end CFSG.EvenSporadicStandard.J4Std.DataMod

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem liftData_J4
    {G : Type} [Group G] (ι : J →* G)
    (hι : Function.Injective ι) : LiftData ι.range ((Eg uJ 11).map ι) :=
  DataMod.liftData_map ι hι _ DataMod.liftData_J

end CFSG.EvenSporadicStandard.J4Std
