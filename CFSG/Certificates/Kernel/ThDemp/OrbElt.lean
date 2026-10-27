
module

public import CFSG.Certificates.Kernel.ThDemp.OrbEltBase
import all CFSG.Certificates.Kernel.ThDemp.OrbEltBase

public import CFSG.Certificates.Kernel.ThDemp.OrbCent
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.NormNum.Prime
public import CFSG.Certificates.Kernel.ThDemp.OrbUnfold
public import CFSG.Certificates.Kernel.ThDemp.Sound

public section

namespace CFSG.Certificates.ThDemp.Elt

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Rows CFSG.Certificates.ThDemp.Stab
  CFSG.Certificates.ThDemp.USp CFSG.Certificates.ThDemp.Cent

set_option exponentiation.threshold 2000

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))


theorem inLayout_chainEl (hF : DempFacts D) (e : ℕ) : InLayout (chainEl D e) := by
  rw [chainEl_eq]
  exact inLayout_mulB hF.consts _ _

theorem ordChk_sound (hF : DempFacts D) {X p : ℕ} (h : ordChk D X p = true) (hp : p < 32)
    (hX : InLayout X) : pkMat X ^ p = 1 ∧ pkMat X ≠ 1 := by
  have hk := hF.consts
  obtain ⟨h1, h2⟩ := Unfold.andB_split h
  have e1 : pow5 D X p = D.ONE := Nat.eq_of_beq_eq_true h1
  have e2 := Unfold.notB_true h2
  refine ⟨?_, fun h1' => ?_⟩
  · rw [← pkMat_powB hk X p 5 (by norm_num; omega)]
    change pkMat (pow5 D X p) = 1
    rw [e1, pkMat_one hk]
  · have : X = D.ONE := pkMat_inj hX (inLayout_one hk) (by rw [h1', pkMat_one hk])
    rw [this, Nat.beq_refl] at e2
    exact absurd e2 (by decide)

namespace Ctx

variable (C : Ctx D O J) (hF : DempFacts D)

noncomputable def elt (e : ℕ) : J := chainProd C.t (coordsOf e)

theorem elt_mem (e : ℕ) : elt C e ∈ C.Dg := C.chainProd_mem _

include hF in
theorem mat_elt {e : ℕ} (h : codeChk D e = true) : 𝕄 (elt C e) = pkMat (chainEl D e) := by
  have hb := codeChk_sound h
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := C.osz
  have b0 : bitsN e 0 8 % 31 = bitsN e 0 8 := Nat.mod_eq_of_lt (by have := hb 0 (by omega); rwa [o0] at this)
  have b1 : bitsN e 8 8 % 30 = bitsN e 8 8 := Nat.mod_eq_of_lt (by have := hb 1 (by omega); rwa [o1] at this)
  have b2 : bitsN e 16 8 % 28 = bitsN e 16 8 :=
    Nat.mod_eq_of_lt (by have := hb 2 (by omega); rwa [o2] at this)
  have b3 : bitsN e 24 8 % 24 = bitsN e 24 8 :=
    Nat.mod_eq_of_lt (by have := hb 3 (by omega); rwa [o3] at this)
  have b4 : bitsN e 32 8 % 16 = bitsN e 32 8 :=
    Nat.mod_eq_of_lt (by have := hb 4 (by omega); rwa [o4] at this)
  have b5 : bitsN e 40 8 % 32 = bitsN e 40 8 :=
    Nat.mod_eq_of_lt (by have := hb 5 (by omega); rwa [o5] at this)
  unfold elt chainProd coordsOf
  simp only [mat_mul', b0, b1, b2, b3, b4, b5]
  rw [C.mat 5 (by omega) (bitsN e 40 8) (hb 5 (by omega)),
    C.mat 4 (by omega) (bitsN e 32 8) (hb 4 (by omega)),
    C.mat 3 (by omega) (bitsN e 24 8) (hb 3 (by omega)),
    C.mat 2 (by omega) (bitsN e 16 8) (hb 2 (by omega)),
    C.mat 1 (by omega) (bitsN e 8 8) (hb 1 (by omega)),
    C.mat 0 (by omega) (bitsN e 0 8) (hb 0 (by omega)), Unfold.pkMat_chainEl hF]

include hF in
theorem lil_U0 (h1 : Elt1Facts D O) : LIL (rowsOf (2 ^ 248 - 1) (U0 D)) := by
  have hnd := Unfold.nodupB_sound h1.nd
  rw [Cent.Ctx.hrm hF] at hnd
  exact lil_of_nodup _ (rowsOf_lt _) hnd

include hF in
theorem mapM_U0 (h1 : Elt1Facts D O) : ∀ d ∈ C.Dg, mapM (𝕄 d) (sp (U0 D)) = sp (U0 D) := by
  have hU := lil_U0 hF h1
  have hgen : ∀ (d : J) (g : ℕ) (G : ℕ), 𝕄 d = pkMat (gen D g) →
      combChk D.rm (mulB (cR 5) D.rm (U0 D) (gen D g)) (U0 D) G = true →
      mapM (𝕄 d) (sp (U0 D)) = sp (U0 D) := by
    intro d g G hd hc
    rw [Cent.Ctx.hrm hF, cR_eq] at hc
    have hl := lil_mulB (P := U0 D) (N := gen D g) (M' := 𝕄 d⁻¹) (by rw [← hd]; exact mat_mul_inv d) hU
    rw [hd, ← sp_mulB]
    exact sp_eq_of_combChk hc hl hU
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hgen _ 0 _ C.md₀ h1.g0
    · rw [Set.mem_singleton_iff.mp hx]
      exact hgen _ 1 _ C.md₁ h1.g1
  | one =>
    change mapM (((1 : GL (Fin 248) (ZMod 2))) : Matrix (Fin 248) (Fin 248) (ZMod 2)) _ = _
    rw [Units.val_one, mapM_one]
  | mul x y _ _ hx hy => rw [FwdRel.mat_mul, mapM_mul, hx, hy]
  | inv x _ hx =>
    conv_lhs => rw [← hx]
    rw [← mapM_mul, ← FwdRel.mat_mul, mul_inv_cancel]
    change mapM (((1 : GL (Fin 248) (ZMod 2))) : Matrix (Fin 248) (Fin 248) (ZMod 2)) _ = _
    rw [Units.val_one, mapM_one]

include hF in
theorem le_stabilizer (h1 : Elt1Facts D O) : C.Dg ≤ stabilizer J (sp (U0 D)) := by
  intro d hd
  rw [mem_stabilizer_iff, smul_eq_mapM]
  exact mapM_U0 C hF h1 _ (Subgroup.inv_mem _ hd)

end Ctx

private theorem qFits_U0 (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) : QFits (U0 D) := by
  have hF : ∀ k, (fun k => if k < 5 then D.bvL k else 0) k < 2 ^ 256 := fun k => by
    dsimp only
    split_ifs with h
    · exact Nat.lt_of_lt_of_le (hbv k h) (Nat.pow_le_pow_right (by omega) (by omega))
    · exact Nat.two_pow_pos _
  have e : U0 D = stackN 256 5 (fun k => if k < 5 then D.bvL k else 0) :=
    stackN_congr 256 5 (fun k hk => by simp [hk])
  intro p hp
  rw [e, testBit_stackN_s (by omega) hF, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨h1, h2⟩ := hp
  refine ⟨?_, h1⟩
  rw [if_pos h1] at h2
  by_contra h3
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hbv _ h1)
    (Nat.pow_le_pow_right (by omega) (by omega)))] at h2
  exact absurd h2 (by decide)

private theorem qPart_spec (hrm : D.rm = 2 ^ 248 - 1) (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) {Y : ℕ}
    (hY : pkMat Y ^ 31 = 1) (q k : ℕ) : ∀ n,
    QFits (qPart q k (powStack D Y (U0 D) 30) n) ∧ ∀ r < 5,
      pkVec (qRow (qPart q k (powStack D Y (U0 D) 30) n) r) = Matrix.vecMul (pkVec (D.bvL r))
        ((pkMat Y ^ k) ^ 5 + ∑ j ∈ Finset.range n, ((bitsN q j 1 : ℕ) : ZMod 2) • (pkMat Y ^ k) ^ j)
  | 0 => by
    have hU := qFits_U0 hbv
    have e : qPart q k (powStack D Y (U0 D) 30) 0 = qPow D Y (U0 D) (5 * k % 31) :=
      ptAt_powStack hrm Y hU (Nat.mod_lt _ (by omega))
    rw [e]
    refine ⟨qFits_qPow hrm Y hU _, fun r hr => ?_⟩
    rw [pkVec_qRow_qPow hrm hbv Y hr, pow_mod_31 hY, Finset.sum_range_zero, add_zero]
  | n + 1 => by
    obtain ⟨hF, hR⟩ := qPart_spec hrm hbv hY q k n
    have hU := qFits_U0 hbv
    have e : qPart q k (powStack D Y (U0 D) 30) (n + 1) = qPart q k (powStack D Y (U0 D) 30) n ^^^
        bitsN q n 1 * qPow D Y (U0 D) (n * k % 31) := by
      rw [← ptAt_powStack hrm Y hU (Nat.mod_lt _ (by omega))]
      rfl
    rw [e]
    refine ⟨hF.xor ((qFits_qPow hrm Y hU _).bit (bitsN_one_lt q n)), fun r hr => ?_⟩
    have e2 : Matrix.vecMul (pkVec (D.bvL r)) ((pkMat Y ^ k) ^ 5 + ∑ j ∈ Finset.range (n + 1),
        ((bitsN q j 1 : ℕ) : ZMod 2) • (pkMat Y ^ k) ^ j) =
        Matrix.vecMul (pkVec (D.bvL r)) ((pkMat Y ^ k) ^ 5 + ∑ j ∈ Finset.range n,
          ((bitsN q j 1 : ℕ) : ZMod 2) • (pkMat Y ^ k) ^ j) +
        ((bitsN q n 1 : ℕ) : ZMod 2) • Matrix.vecMul (pkVec (D.bvL r)) ((pkMat Y ^ k) ^ n) := by
      rw [Finset.sum_range_succ, ← add_assoc, Matrix.vecMul_add, Matrix.vecMul_smul]
    rw [e2, qRow_xor, qRow_bit (bitsN_one_lt q n), pkVec_xor, pkVec_bit (bitsN_one_lt q n),
      hR r hr, pkVec_qRow_qPow hrm hbv Y hr, pow_mod_31 hY]

private theorem qRows_eq_zero_iff (hrm : D.rm = 2 ^ 248 - 1) (hbv : ∀ l < 5, D.bvL l < 2 ^ 248)
    {Y : ℕ} (hY : pkMat Y ^ 31 = 1) (q k : ℕ) :
    qRows q k (powStack D Y (U0 D) 30) = 0 ↔ KillU D (Qm q (pkMat Y ^ k)) := by
  obtain ⟨hF, hR⟩ := qPart_spec hrm hbv hY q k 5
  rw [qRows_eq, killU_iff hbv]
  constructor
  · intro h0 r hr
    rw [Qm, ← hR r hr, h0, qRow_zero, pkVec_zero]
  · intro h
    refine hF.eq_zero fun r hr => pkVec_inj (land_rm_lt _) (Nat.two_pow_pos _) ?_
    rw [pkVec_zero, hR r hr]
    exact h r hr

private theorem ncard_killU_le (hrm : D.rm = 2 ^ 248 - 1) (hbv : ∀ l < 5, D.bvL l < 2 ^ 248)
    {Y : ℕ} (hY : pkMat Y ^ 31 = 1) (q : ℕ) (hc : qCount q (powStack D Y (U0 D) 30) ≤ 5) :
    {k | 0 < k ∧ k < 31 ∧ KillU D (Qm q (pkMat Y ^ k))}.ncard ≤ 5 := by
  unfold qCount at hc
  rw [Unfold.card_filter_of_sumBelow (m := 30) (hi := 1) (by norm_num)] at hc
  refine le_trans (Set.ncard_le_ncard (t := ↑(((Finset.range 30).filter fun i =>
    Nat.beq (qRows q (Nat.succ i) (powStack D Y (U0 D) 30)) 0 = true).image (· + 1))) ?_
    (Finset.finite_toSet _)) ?_
  · rintro k ⟨hk0, hk31, hk⟩
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k - 1, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩)
    have e : Nat.succ (k - 1) = k := by omega
    show Nat.beq (qRows q (Nat.succ (k - 1)) (powStack D Y (U0 D) 30)) 0 = true
    rw [e, (qRows_eq_zero_iff hrm hbv hY q k).mpr hk]
    rfl
  · rw [Set.ncard_coe_finset]
    exact le_trans Finset.card_image_le hc

theorem qChk_sound (h : qChk D O = true) (hrm : D.rm = 2 ^ 248 - 1)
    (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) (hX : pkMat (chainEl D O.x31) ^ 31 = 1)
    (hY : pkMat (chainEl D O.yb) ^ 31 = 1) :
    KillU D (Qm O.qm (pkMat (chainEl D O.x31))) ∧
    ¬ KillU D (Qm O.qm (pkMat (chainEl D O.x31) ^ 5)) ∧
    ¬ KillU D (Qm O.qm (pkMat (chainEl D O.x31) ^ 25)) ∧
    {k | 0 < k ∧ k < 31 ∧ KillU D (Qm O.qm (pkMat (chainEl D O.x31) ^ k))}.ncard ≤ 5 ∧
    {k | 0 < k ∧ k < 31 ∧ KillU D (Qm O.qm (pkMat (chainEl D O.yb) ^ k))}.ncard ≤ 5 := by
  unfold qChk at h
  obtain ⟨h1, h⟩ := Unfold.andB_split h
  obtain ⟨h5, h⟩ := Unfold.andB_split h
  obtain ⟨h25, h⟩ := Unfold.andB_split h
  obtain ⟨ha, hb⟩ := Unfold.andB_split h
  have iff := qRows_eq_zero_iff hrm hbv hX O.qm
  refine ⟨?_, fun hk => ?_, fun hk => ?_, ncard_killU_le hrm hbv hX O.qm (Nat.le_of_ble_eq_true ha),
    ncard_killU_le hrm hbv hY O.qm (Nat.le_of_ble_eq_true hb)⟩
  · have := (iff 1).mp (Nat.eq_of_beq_eq_true h1)
    rwa [pow_one] at this
  · have h5' := Unfold.notB_true h5
    rw [(iff 5).mpr hk] at h5'
    exact absurd h5' (by decide)
  · have h25' := Unfold.notB_true h25
    rw [(iff 25).mpr hk] at h25'
    exact absurd h25' (by decide)

end CFSG.Certificates.ThDemp.Elt

end
