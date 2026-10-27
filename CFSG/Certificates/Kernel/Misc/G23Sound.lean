module

public import Certificates.Data.Kernel.Misc.G23
public import CFSG.Certificates.Kernel.Misc.G24Sound
public import CFSG.LieType.Multipliers.G23Data
import CFSG.Certificates.Kernel.Misc.Spec.Cover23
import CFSG.Certificates.Kernel.Misc.Spec.Payload
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.G23

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.G23 CFSG.Sporadic.He.Native
open CFSG.KC.Misc.Spec

@[expose] def coverWordArrG (L : Fin 2 × Bool → Array (Array ℕ)) (w : List (Fin 2 × Bool)) :
    Array (Array ℕ) :=
  w.foldr (fun l M => mulM 2 54 (L l) M) (idM 54)

@[expose] def coverCheckG (sA sB : String) (L : Fin 2 × Bool → Array (Array ℕ))
    (R : List (List (Fin 2 × Bool)))
    (P : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))) : Bool :=
  (mulM 2 54 (blowUp (rowsOf 4 27 sA)) (blowUp (rowsOf 4 27 sA)) == idM 54) &&
    (mulM 2 54 (blowUp (rowsOf 4 27 sB))
      (mulM 2 54 (blowUp (rowsOf 4 27 sB)) (blowUp (rowsOf 4 27 sB))) == idM 54) &&
    (coverWords R fun i => commWords (P i)).all fun v => coverWordArrG L v == idM 54

@[expose] def relSixCheckG (L : Fin 2 × Bool → Array (Array ℕ)) (w : List (Fin 2 × Bool)) : Bool :=
  (mulM 2 54 (coverWordArrG L w) (mulM 2 54 (coverWordArrG L w) (coverWordArrG L w)) ==
      idM 54) && ((coverWordArrG L w)[0]!)[1]! == 1

theorem coverCheck_eq : coverCheck = coverCheckG atlasA atlasB coverLetter rels pairs := rfl

theorem relSixCheck_eq : relSixCheck = relSixCheckG coverLetter relSix := rfl

@[expose] def encW (w : List (Fin 2 × Bool)) : List ℕ :=
  w.map fun l => 2 * l.1.val + if l.2 then 1 else 0

private theorem testBit_one_of_bit {x : ℕ} (h : CFSG.KC.Misc.G24.bit x 1 = 1) :
    x.testBit 1 = true := by
  have h1 : (x >>> 1) &&& 1 = 1 := h
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at h1
  rw [Nat.testBit_succ, Nat.testBit_zero]
  simpa using h1

theorem g23_sound {sA sB : String} {L : Fin 2 × Bool → Array (Array ℕ)}
    {R : List (List (Fin 2 × Bool))}
    {P : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))} {w : List (Fin 2 × Bool)}
    {cA cB six : List ℕ} {Ab Bb : ℕ} {Rc : List (List ℕ)} {Pc : List (List (List ℕ × List ℕ))}
    (hA : sA = CFSG.KC.Misc.G24.strOf cA) (hB : sB = CFSG.KC.Misc.G24.strOf cB)
    (hL0 : ∀ b, L (0, b) = blowUp (rowsOf 4 27 sA)) (hL1 : L (1, true) = blowUp (rowsOf 4 27 sB))
    (hL2 : L (1, false) = mulM 2 54 (blowUp (rowsOf 4 27 sB)) (blowUp (rowsOf 4 27 sB)))
    (hR : R.map encW = Rc) (hP : ∀ i : Fin 2, (P i).map (fun p => (encW p.1, encW p.2)) =
      CFSG.KC.Misc.G24.nthP Pc i)
    (hw : encW w = six) (h : g23K cA cB Ab Bb Rc Pc six = true) :
    coverCheckG sA sB L R P = true ∧ relSixCheckG L w = true := by
  subst hA hB hR hw
  have h' := h
  unfold g23K at h'
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.letB_eq,
    CFSG.KS.PK.allLL_iff] at h'
  obtain ⟨hdA, hdB, hAA, hBB, hcov, hZ1, hZ2⟩ := h'
  set BA := toM (blowUp (rowsOf 4 27 (CFSG.KC.Misc.G24.strOf cA))) with hBA
  set BB := toM (blowUp (rowsOf 4 27 (CFSG.KC.Misc.G24.strOf cB))) with hBB'
  have hpA : pkMat 54 Ab = BA := by
    rw [← hdA, pkMat_decodeK]
    rfl
  have hpB : pkMat 54 Bb = BB := by
    rw [← hdB, pkMat_decodeK]
    rfl
  have hpBi : pkMat 54 (CFSG.KC.Misc.G24.mulF2 54 Bb Bb) = BB * BB := by
    rw [pkMat_mulF2, hpB]
  have hLM0 : ∀ b, toM (L (0, b)) = BA := fun b => by rw [hL0 b]
  have hLM1 : toM (L (1, true)) = BB := by rw [hL1]
  have hLM2 : toM (L (1, false)) = BB * BB := by rw [hL2, mulM_eq, toM_ofM]
  have hw8 : ∀ v : List (Fin 2 × Bool),
      pkMat 54 (wordM Ab Bb (CFSG.KC.Misc.G24.mulF2 54 Bb Bb) (encG v)) =
        wordProd (fun l => toM (L l)) v :=
    pkMat_wordM (fun b => by rw [hpA, hLM0 b]) (by rw [hpB, hLM1]) (by rw [hpBi, hLM2])
  have hAA' : BA * BA = 1 := by
    have h2 := congrArg (pkMat 54) hAA
    rwa [pkMat_mulF2, pkMat_oneF2, hpA] at h2
  have hBB'' : BB * (BB * BB) = 1 := by
    have h2 := congrArg (pkMat 54) hBB
    rwa [pkMat_mulF2, pkMat_mulF2, pkMat_oneF2, hpB] at h2
  have hc : coverW (List.map encW R) Pc = (coverWords R fun i => commWords (P i)).map encG :=
    coverW_eq R P Pc hP
  refine ⟨?_, ?_⟩
  · unfold coverCheckG
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [beq_iff_eq, mulM_eq, idM_eq]
      show ofM (BA * BA) = ofM 1
      rw [hAA']
    · rw [beq_iff_eq, mulM_eq, mulM_eq, toM_ofM, idM_eq]
      show ofM (BB * (BB * BB)) = ofM 1
      rw [hBB'']
    · rw [List.all_eq_true]
      intro v hv
      rw [beq_iff_eq]
      have hmem : encG v ∈ coverW (List.map encW R) Pc := by
        rw [hc]
        exact List.mem_map_of_mem hv
      have h2 := congrArg (pkMat 54) (hcov (encG v) hmem)
      rw [hw8, pkMat_oneF2] at h2
      show coverWordArrG L v = idM 54
      unfold coverWordArrG
      rw [foldr_mulM, idM_eq, h2]
  · unfold relSixCheckG
    rw [Bool.and_eq_true]
    have hz : pkMat 54 (wordM Ab Bb (CFSG.KC.Misc.G24.mulF2 54 Bb Bb) (encW w)) =
        wordProd (fun l => toM (L l)) w := hw8 w
    have hzarr : coverWordArrG L w = ofM (wordProd (fun l => toM (L l)) w) := by
      unfold coverWordArrG
      exact foldr_mulM L w
    refine ⟨?_, ?_⟩
    · rw [beq_iff_eq, hzarr, idM_eq]
      simp only [mulM_eq, toM_ofM]
      have h3 := congrArg (pkMat 54) hZ1
      rw [pkMat_mulF2, pkMat_mulF2, pkMat_oneF2, hz] at h3
      rw [h3]
    · rw [beq_iff_eq, hzarr, ofM_zero_one]
      have hb : (wordM Ab Bb (CFSG.KC.Misc.G24.mulF2 54 Bb Bb) (encW w)).testBit 1 = true :=
        testBit_one_of_bit hZ2
      have h5 : pkMat 54 (wordM Ab Bb (CFSG.KC.Misc.G24.mulF2 54 Bb Bb) (encW w)) 0 1 = 1 := by
        simp [pkMat, hb]
      rw [hz] at h5
      rw [h5]
      exact val_one_two

end CFSG.KC.Misc.G23

end
