module

public import Certificates.Data.Kernel.Misc.YamakiNW
public import CFSG.Certificates.Kernel.Misc.YamakiCESound

public section

namespace CFSG.KC.YamakiNW

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiNA
  CFSG.KD.YamakiCE CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0
  CFSG.KC.YamakiA0 CFSG.KC.YamakiCE CFSG.KC.Misc.Spec Matrix
open CFSG.KD.Sp62 (MULF ONE)

@[expose] def colM (u : Fin 3 ⊕ Fin 3 → ZMod 2) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.of fun i j => if j = Sum.inl 0 then u i else 0

theorem mul_colM (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (u : Fin 3 ⊕ Fin 3 → ZMod 2) : A * colM u = colM (A *ᵥ u) := by
  ext i j
  simp only [colM, Matrix.mul_apply, Matrix.of_apply]
  split_ifs with h
  · simp [Matrix.mulVec, dotProduct]
  · simp

theorem colM_inj {u v : Fin 3 ⊕ Fin 3 → ZMod 2} (h : colM u = colM v) : u = v := by
  funext i
  have := congrFun (congrFun h i) (Sum.inl 0)
  simpa [colM] using this

theorem vnum_mat : ∀ w < 64, matN (vnum w) = colM (vecOf w) := by
  decide +kernel

theorem vnum_lt : ∀ w < 64, vnum w < 2 ^ 36 := by
  decide +kernel

theorem matN_inj {a b : ℕ} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : matN a = matN b) : a = b :=
  arrN_inj ha hb (by unfold arrN; rw [h])

theorem arrN_get_iff {x w c : ℕ} (hw : w < 64) (hc : c < 64) :
    (arrN x)[w]! = c ↔ MULF x (vnum w) = vnum c := by
  unfold arrN
  rw [matArr_get _ hw]
  constructor
  · intro h
    have hu : matN x *ᵥ vecOf w = vecOf c := by rw [← h, vecOf_codeOf]
    apply matN_inj (CFSG.KC.Sp62.MULF_lt _ _) (vnum_lt c hc)
    rw [matN_mul, vnum_mat w hw, mul_colM, hu, vnum_mat c hc]
  · intro h
    have e := congrArg matN h
    rw [matN_mul, vnum_mat w hw, mul_colM, vnum_mat c hc] at e
    rw [colM_inj e, codeOf_vecOf c hc]

theorem decide_get {x w c : ℕ} (hw : w < 64) (hc : c < 64) :
    decide ((arrN x)[w]! = c) = mapsTo x w c := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_eq, mapsTo, Nat.beq_eq]
  exact arrN_get_iff hw hc

theorem wCodes_lt : ∀ w ∈ wCodes, w < 64 := by decide

theorem contains_get {x w : ℕ} (hw : w < 64) :
    wCodes.contains (arrN x)[w]! = wCodes.any fun c => mapsTo x w c := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.any_eq_true]
  constructor
  · intro h
    exact ⟨_, h, by rw [← decide_get hw (wCodes_lt _ h), decide_eq_true_eq]⟩
  · rintro ⟨c, hc, h⟩
    rw [← decide_get hw (wCodes_lt _ hc), decide_eq_true_eq] at h
    rw [h]
    exact hc

variable {R : ℕ → ℕ}

theorem wCheck_of {PAA PBA : ℕ → ℕ}
    (hA : BInvE (fun t => arrN (recX R 12 t)) PAA PBA 64 (enumA0 ()))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hw : wK R = true) :
    wCheck () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hA
  unfold wK at hw
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hw
  obtain ⟨h1, h2⟩ := hw
  simp only [wCheck, Bool.and_eq_true, allLt_iff]
  refine ⟨fun i hi => ?_, fun v hv => ?_⟩
  · rw [e1] at hi
    rw [e4 i hi, List.all_eq_true]
    intro w hwc
    beta_reduce
    rw [decide_get (wCodes_lt w hwc) (wCodes_lt w hwc)]
    exact List.all_eq_true.1 (h1 i (List.mem_range.2 hi)) w hwc
  · have e := h2 v (List.mem_range.2 hv)
    have hfix : (allLt (gA0 ()).size fun j => decide (((gA0 ())[j]!)[v]! = v)) =
        (List.range 6).all fun j => mapsTo (R (Nat.add j 3)) v v := by
      apply Bool.eq_iff_iff.2
      rw [allLt_iff, size_gA0, List.all_eq_true]
      constructor
      · intro h j hj
        have hj' := List.mem_range.1 hj
        have f := h j hj'
        rw [gA0_eq hG hj', decide_get hv hv] at f
        exact f
      · intro h j hj
        rw [gA0_eq hG hj, decide_get hv hv]
        exact h j (List.mem_range.2 hj)
    rw [hfix]
    exact e

theorem stabWCheck_of {RX PA PB PAX PBX P : ℕ → ℕ} {o oX : ℕ}
    (hH : BInvE (fun t => arrN (recX R o t)) PA PB 23040 (enumH ()))
    (hX : BInvE (fun t => arrN (recX RX oX t)) PAX PBX 1536 (enumX ()))
    (hc : ∀ q < 45, stabChunk R o 23040 RX oX 1536 P 512 q = true) : stabWCheck () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hH
  simp only [stabWCheck, allLt_iff]
  intro i hi
  rw [e1] at hi
  have hq : i / 512 < 45 := by omega
  have hcq := hc _ hq
  unfold stabChunk at hcq
  have hlo : Nat.mul 512 (i / 512) ≤ i := Nat.mul_div_le i 512
  have hhi : i < Nat.mul 512 (i / 512) + 512 := by
    change i < 512 * (i / 512) + 512
    omega
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq i hlo hhi
  rw [Nat.blt_eq.mpr hi, cond_true, CFSG.KC.YamakiRepF.strictY_eq] at e
  rw [e4 i hi]
  beta_reduce
  have hall : (wCodes.all fun w => wCodes.contains (arrN (recX R o i))[w]!) =
      wCodes.all fun w => wCodes.any fun c => mapsTo (recX R o i) w c := by
    apply Bool.eq_iff_iff.2
    rw [List.all_eq_true, List.all_eq_true]
    constructor
    · intro h w hw
      rw [← contains_get (wCodes_lt w hw)]
      exact h w hw
    · intro h w hw
      rw [contains_get (wCodes_lt w hw)]
      exact h w hw
  rw [hall]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e ⊢
  rcases e with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (isSome_of_rec hX ⟨_, h1, h2⟩)

theorem rhoKerCheck_of {RA PA PB PAA PBA : ℕ → ℕ} {o : ℕ}
    (hN : BInvE (fun t => arrN (recX R o t)) PA PB 10752 (enumN ()))
    (hA : BInvE (fun t => arrN (recX RA 12 t)) PAA PBA 64 (enumA0 ()))
    (hc : ∀ q < 21, rhoChunk R o 10752 RA 512 q = true) : rhoKerCheck () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hN
  simp only [rhoKerCheck, allLt_iff]
  intro i hi
  rw [e1] at hi
  have hq : i / 512 < 21 := by omega
  have hcq := hc _ hq
  unfold rhoChunk at hcq
  have hlo : Nat.mul 512 (i / 512) ≤ i := Nat.mul_div_le i 512
  have hhi : i < Nat.mul 512 (i / 512) + 512 := by
    change i < 512 * (i / 512) + 512
    omega
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq i hlo hhi
  rw [Nat.blt_eq.mpr hi, cond_true, CFSG.KC.YamakiRepF.strictY_eq] at e
  rw [e4 i hi]
  beta_reduce
  have h3 : ([9, 20, 38].all fun w => decide ((arrN (recX R o i))[w]! = w)) =
      [9, 20, 38].all fun w => mapsTo (recX R o i) w w := by
    simp only [List.all_cons, List.all_nil]
    rw [decide_get (by norm_num : 9 < 64) (by norm_num : 9 < 64),
      decide_get (by norm_num : 20 < 64) (by norm_num : 20 < 64),
      decide_get (by norm_num : 38 < 64) (by norm_num : 38 < 64)]
  rw [h3]
  simp only [Bool.or_eq_true] at e ⊢
  rcases e with h | h
  · exact Or.inl h
  · exact Or.inr (isSome_of_rec hA (memK_sound h))

end CFSG.KC.YamakiNW

end
