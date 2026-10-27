module

public import Certificates.Data.Kernel.SporSch.Co1CtStar
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.SporSch.Co1MatSound
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.KS.Raw
  CFSG.Sporadic.Co1Block.Native CFSG.EvenSporadicStandard.TwoCo1.HypOne

theorem ctSixK_sound {GM GIM : Nat → Nat} {ng R M : Nat} (h : ctSixK GM GIM ng R M = true) :
    conjAtLeast (gensArr ng GM) (gensArr ng GIM) (unpack 24 24 R) 5 = true := by
  unfold ctSixK at h
  simp only [MatL.strictB_eq] at h
  exact conjAtLeast_of_K h

theorem beq_unpack24 (A B : Nat) : (unpack 24 24 A == unpack 24 24 B) = CFSG.KC.Co1B.eqK A B := by
  rw [← unpackR_eq_unpack, ← unpackR_eq_unpack]
  exact CFSG.KC.Co1B.beq_unpack A B

theorem fourConjK_sound {GM GIM : Nat → Nat} {ng X M : Nat} (h : fourConjK GM GIM ng X M = true) :
    (!fourRows (unpack 24 24 X) ||
      conjAtLeast (gensArr ng GM) (gensArr ng GIM) (unpack 24 24 X) 5) = true := by
  unfold fourConjK at h
  simp only [MatL.strictB_eq] at h
  unfold fourRows
  rw [mul_unpackW, mul_unpackW, ← MatL.unpack_idM, bne, beq_unpack24, beq_unpack24]
  cases h1 : CFSG.KC.Co1B.eqK (CFSG.KC.Co1B.mulWK X X) idM
  · cases h2 : CFSG.KC.Co1B.eqK (CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK X X)
        (CFSG.KC.Co1B.mulWK X X)) idM
    · simp
    · rw [h1, h2] at h
      simp [ctSixK_sound h]
  · simp

theorem dagIK_inv {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Int)}
    (h : dagIK M MI nb N ws = true) : ∀ k < N, invOKK (M k) (MI k) = true := by
  obtain ⟨-, h⟩ := bAnd_true h
  exact MatL.allN_iff.1 (bAnd_true h).1

theorem range_map_unpack (n : Nat) (M : Nat → Nat) :
    ((List.range n).map fun i => unpack 24 24 (M i)) = ((List.range n).map M).map (unpack 24 24) := by
  rw [List.map_map]
  rfl

theorem getD_range_unpack24 {M : Nat → Nat} {N j : Nat} (hj : j < N) :
    ((List.range N).map fun i => unpack 24 24 (M i)).getD j (one ()) = unpack 24 24 (M j) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem pickRows_unpack {M : Nat → Nat} {N : Nat} {D : List Rows × List Rows × Bool}
    (hD : D.1 = (List.range N).map fun i => unpack 24 24 (M i)) {idx : List Nat}
    (h : idx.all (fun j => decide (j < N)) = true) :
    pickRows D idx = (idx.map M).map (unpack 24 24) := by
  unfold pickRows
  rw [List.map_map, hD]
  apply List.map_congr_left
  intro j hj
  have hj' : j < N := by simpa using List.all_eq_true.1 h j hj
  rw [getD_range_unpack24 hj']
  rfl

theorem map_eq_range {α β : Type} (l : List α) (f : α → β) (d : α) :
    l.map f = (List.range l.length).map fun i => f (l.getD i d) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h₁)]

theorem range_map_congr {α : Type} {n : Nat} {f g : Nat → α} (h : ∀ i < n, f i = g i) :
    (List.range n).map f = (List.range n).map g :=
  List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

theorem perfectCheckOf_of_K {B : List Rows} {nb NP NU NF NQ : Nat}
    {BM PM PMI UM UMI FM FMI QM QMI : Nat → Nat}
    {dP dU dF dQ : List (List Int)} {pIdx fIdx qIdx : List Nat} {cIdx : List (Nat × Nat)}
    {Qr : List Rows}
    (hB : B = (List.range nb).map fun i => unpack 24 24 (BM i))
    (hPb' : ∀ i < nb, PM i = BM i)
    (hP : dagIK PM PMI nb NP dP = true)
    (hpi : pIdx.all (fun j => decide (j < NP)) = true)
    (hUb' : ∀ l < pIdx.length, UM l = PM (pIdx.getD l 0))
    (hU : dagIK UM UMI pIdx.length NU dU = true)
    (hci : cIdx.all (fun ij => decide (ij.1 < NU) && decide (ij.2 < NU)) = true)
    (hFb' : ∀ j < cIdx.length, FM j =
      CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK (UMI (cIdx.getD j (0, 0)).1) (UMI (cIdx.getD j (0, 0)).2))
        (CFSG.KC.Co1B.mulWK (UM (cIdx.getD j (0, 0)).1) (UM (cIdx.getD j (0, 0)).2)))
    (hF : dagIK FM FMI cIdx.length NF dF = true)
    (hfi : fIdx.all (fun j => decide (j < NF)) = true)
    (hfl : fIdx.length = pIdx.length)
    (hf' : ∀ l < pIdx.length, FM (fIdx.getD l 0) = PM (pIdx.getD l 0))
    (hQb' : ∀ l < pIdx.length, QM l = PM (pIdx.getD l 0))
    (hQ : dagIK QM QMI pIdx.length NQ dQ = true)
    (hqi : qIdx.all (fun j => decide (j < NQ)) = true)
    (hql : Qr.length = qIdx.length)
    (hq' : ∀ l < qIdx.length, Qr[l]?.getD #[] = unpack 24 24 (QM (qIdx.getD l 0))) :
    perfectCheckOf B dP pIdx dU cIdx dF fIdx dQ qIdx Qr = true := by
  have hPb : (List.range nb).map PM = (List.range nb).map BM := range_map_congr hPb'
  have hUb : (List.range pIdx.length).map UM = pIdx.map PM := by
    rw [map_eq_range pIdx PM 0]
    exact range_map_congr hUb'
  have hFb : (List.range cIdx.length).map FM = cIdx.map fun ij =>
      CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK (UMI ij.1) (UMI ij.2))
        (CFSG.KC.Co1B.mulWK (UM ij.1) (UM ij.2)) := by
    rw [map_eq_range cIdx _ (0, 0)]
    exact range_map_congr hFb'
  have hf : fIdx.map FM = pIdx.map PM := by
    rw [map_eq_range fIdx FM 0, map_eq_range pIdx PM 0, hfl]
    exact range_map_congr hf'
  have hQb : (List.range pIdx.length).map QM = pIdx.map PM := by
    rw [map_eq_range pIdx PM 0]
    exact range_map_congr hQb'
  have hq : Qr = (qIdx.map QM).map (unpack 24 24) := by
    apply List.ext_getElem (by simp [hql])
    intro l h₁ h₂
    have h := hq' l (by rwa [hql] at h₁)
    rw [List.getElem?_eq_getElem h₁, Option.getD_some] at h
    rw [h, List.getElem_map, List.getElem_map, List.getD_eq_getElem _ _ (by rwa [hql] at h₁)]
  have hB' : B = (List.range nb).map fun i => unpack 24 24 (PM i) := by
    rw [hB, range_map_unpack, range_map_unpack, hPb]
  have eP := dagIK_sound hB' hP
  have hPick : pickRows (dag B dP) pIdx =
      (List.range pIdx.length).map fun i => unpack 24 24 (UM i) := by
    rw [pickRows_unpack (by rw [eP]) hpi, range_map_unpack, hUb]
  have eU := dagIK_sound hPick hU
  have hinvU := dagIK_inv hU
  have hC : commRows (dag (pickRows (dag B dP) pIdx) dU) cIdx =
      (List.range cIdx.length).map fun i => unpack 24 24 (FM i) := by
    have e2 : ((List.range cIdx.length).map fun i => unpack 24 24 (FM i)) =
        (cIdx.map fun ij => CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK (UMI ij.1) (UMI ij.2))
          (CFSG.KC.Co1B.mulWK (UM ij.1) (UM ij.2))).map (unpack 24 24) := by
      rw [range_map_unpack, hFb]
    rw [eU, e2, List.map_map]
    unfold commRows
    apply List.map_congr_left
    intro ij hij
    have h := List.all_eq_true.1 hci ij hij
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    dsimp only
    rw [getD_range_unpack24 h.1, getD_range_unpack24 h.2, (invOKK_sound (hinvU _ h.1)).2,
      (invOKK_sound (hinvU _ h.2)).2, mul_unpackW, mul_unpackW, mul_unpackW]
    rfl
  have eF := dagIK_sound hC hF
  have hQbase : pickRows (dag B dP) pIdx =
      (List.range pIdx.length).map fun i => unpack 24 24 (QM i) := by
    rw [hPick, range_map_unpack, range_map_unpack, hUb, hQb]
  have eQ := dagIK_sound hQbase hQ
  have hFp : pickRows (dag (commRows (dag (pickRows (dag B dP) pIdx) dU) cIdx) dF) fIdx =
      pickRows (dag B dP) pIdx := by
    rw [pickRows_unpack (by rw [eF]) hfi, hf, hPick, range_map_unpack, hUb]
  have hQp : pickRows (dag (pickRows (dag B dP) pIdx) dQ) qIdx = Qr := by
    rw [pickRows_unpack (by rw [eQ]) hqi, hq]
  have hcAll : cIdx.all (fun ij =>
      mul ((dag (pickRows (dag B dP) pIdx) dU).1.getD ij.1 (one ()))
          (inv ((dag (pickRows (dag B dP) pIdx) dU).1.getD ij.1 (one ()))) == one () &&
        mul ((dag (pickRows (dag B dP) pIdx) dU).1.getD ij.2 (one ()))
          (inv ((dag (pickRows (dag B dP) pIdx) dU).1.getD ij.2 (one ()))) == one ()) = true := by
    rw [List.all_eq_true]
    intro ij hij
    have h := List.all_eq_true.1 hci ij hij
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [eU]
    dsimp only
    rw [getD_range_unpack24 h.1, getD_range_unpack24 h.2, (invOKK_sound (hinvU _ h.1)).2,
      (invOKK_sound (hinvU _ h.2)).2, (invOKK_sound (hinvU _ h.1)).1,
      (invOKK_sound (hinvU _ h.2)).1]
    rfl
  unfold perfectCheckOf
  simp only []
  rw [hFp, hQp, hcAll, eF, eQ, eU, eP]
  simp
