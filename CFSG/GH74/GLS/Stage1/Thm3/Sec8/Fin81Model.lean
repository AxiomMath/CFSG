module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Dih
public import CFSG.GH74.GLS.Stage2.Final.ModelLUData

public section

open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

section Swap

variable {F : Type} [Field F]

@[expose] def sw2 (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

theorem coe_sw2 : ((sw2 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem sw2_mul_self : sw2 F * sw2 F = 1 := by
  apply Units.ext
  simp [coe_sw2, Matrix.one_fin_two]

theorem sw2_inv : (sw2 F)⁻¹ = sw2 F := inv_eq_of_mul_eq_one_right sw2_mul_self

theorem det_sw2 : ((sw2 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  simp [coe_sw2, Matrix.det_fin_two]

theorem sw2_mul_dgen_mul_sw2 (α β : Fˣ) : sw2 F * dgen α β * sw2 F = dgen β α := by
  apply Units.ext
  simp only [Units.val_mul, coe_sw2, coe_dgen, Matrix.diagonal_vec2, Matrix.mul_fin_two]
  simp

theorem dRefl_mul_dgen_mul_dRefl (α β : Fˣ) : dRefl F * dgen α β * dRefl F = dgen α β := by
  apply Units.ext
  simp only [Units.val_mul, coe_dRefl, coe_dgen, Matrix.diagonal_vec2, Matrix.mul_fin_two]
  simp

theorem sw2_mul_dRefl_sq : (sw2 F * dRefl F) * (sw2 F * dRefl F) = -1 := by
  apply Units.ext
  simp only [Units.val_mul, coe_sw2, coe_dRefl, Units.val_neg, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dRefl_mul_sw2_sq : (dRefl F * sw2 F) * (dRefl F * sw2 F) = -1 := by
  apply Units.ext
  simp only [Units.val_mul, coe_sw2, coe_dRefl, Units.val_neg, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dgen_one_one' : (dgen (1 : Fˣ) 1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  simp [coe_dgen, ← Matrix.diagonal_one]

theorem sc2_eq_dgen' (c : Fˣ) : (sc2 c : GL (Fin 2) F) = dgen c c := by
  apply Units.ext
  rw [coe_dgen]
  simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_fin_two]

end Swap

section Diag

variable {F : Type} [Field F]

@[expose] def ipow (i : Fˣ) (n : ZMod 4) : Fˣ := i ^ n.val

theorem ipow_zero (i : Fˣ) : ipow i 0 = 1 := by simp [ipow]

theorem ipow_add {i : Fˣ} (hi4 : i ^ 4 = 1) (a b : ZMod 4) :
    ipow i (a + b) = ipow i a * ipow i b := by
  unfold ipow
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hi4]

theorem ipow_two {i : Fˣ} (hii : i * i = -1) : ipow i 2 = -1 := by
  unfold ipow
  have h : (2 : ZMod 4).val = 2 := rfl
  rw [h, pow_two, hii]

@[expose] def ipDiag (i : Fˣ) (a b c d : ZMod 4) : GL (Fin 4) F :=
  diagGL (dgen (ipow i a) (ipow i b)) (dgen (ipow i c) (ipow i d))

theorem ipDiag_zero (i : Fˣ) : (ipDiag i 0 0 0 0 : GL (Fin 4) F) = 1 := by
  simp only [ipDiag, ipow_zero, dgen_one_one', diagGL_one]

theorem ipDiag_mul {i : Fˣ} (hi4 : i ^ 4 = 1) (a b c d a' b' c' d' : ZMod 4) :
    (ipDiag i a b c d : GL (Fin 4) F) * ipDiag i a' b' c' d' =
      ipDiag i (a + a') (b + b') (c + c') (d + d') := by
  simp only [ipDiag, diagGL_mul, dgen_mul, ipow_add hi4]

theorem ipDiag_inv {i : Fˣ} (hi4 : i ^ 4 = 1) (a b c d : ZMod 4) :
    (ipDiag i a b c d : GL (Fin 4) F)⁻¹ = ipDiag i (-a) (-b) (-c) (-d) := by
  apply inv_eq_of_mul_eq_one_right
  rw [ipDiag_mul hi4]
  simp only [add_neg_cancel]
  exact ipDiag_zero i

theorem ipDiag_scalar (i : Fˣ) (a : ZMod 4) :
    (ipDiag i a a a a : GL (Fin 4) F) = Matrix.GeneralLinearGroup.scalar (Fin 4) (ipow i a) := by
  rw [scalar4_eq, ipDiag, sc2_eq_dgen']

theorem ipDiag_mem_K4 {i : Fˣ} (hi4 : i ^ 4 = 1) (M : ModelData F)
    (hdg : ∀ a b : ℕ, (dgen (i ^ a) (i ^ b) : GL (Fin 2) F) ∈ M.U2) (a b c d : ZMod 4)
    (h : a + b + c + d = 0) : (ipDiag i a b c d : GL (Fin 4) F) ∈ M.K4 := by
  rw [ipDiag, M.diagGL_mem_K4_iff]
  refine ⟨hdg _ _, hdg _ _, ?_⟩
  rw [det_dgen, det_dgen]
  have h1 : ipow i a * ipow i b * (ipow i c * ipow i d) = 1 := by
    rw [← ipow_add hi4, ← ipow_add hi4, ← ipow_add hi4,
      show a + b + (c + d) = 0 by rw [← h]; ring, ipow_zero]
  have h2 := congrArg (fun u : Fˣ => (u : F)) h1
  simpa using h2

theorem yGL_eq_ipDiag {i : Fˣ} (hii : i * i = -1) :
    (yGL F : GL (Fin 4) F) = ipDiag i 2 2 0 0 := by
  rw [ipDiag, ipow_two hii, ipow_zero, dgen_one_one', ← sc2_eq_dgen', sc2_neg_one, yGL]

end Diag

section Generators

variable {F : Type} [Field F]

@[expose] def embTorusGL (i : Fˣ) (v : V4) : GL (Fin 4) F := ipDiag i 0 v.1 v.2 (-v.1 - v.2)

theorem embTorusGL_mem {i : Fˣ} (hi4 : i ^ 4 = 1) (M : ModelData F)
    (hdg : ∀ a b : ℕ, (dgen (i ^ a) (i ^ b) : GL (Fin 2) F) ∈ M.U2) (v : V4) :
    (embTorusGL i v : GL (Fin 4) F) ∈ M.K4 :=
  ipDiag_mem_K4 hi4 M hdg _ _ _ _ (by ring)

theorem embTorusGL_add {i : Fˣ} (hi4 : i ^ 4 = 1) (v w : V4) :
    (embTorusGL i (v + w) : GL (Fin 4) F) = embTorusGL i v * embTorusGL i w := by
  have h4 : -(v + w).1 - (v + w).2 = (-v.1 - v.2) + (-w.1 - w.2) := by
    simp only [Prod.fst_add, Prod.snd_add]; ring
  unfold embTorusGL
  rw [ipDiag_mul hi4, h4]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]

theorem embTorusGL_zero (i : Fˣ) : (embTorusGL i 0 : GL (Fin 4) F) = 1 := by
  simp only [embTorusGL, Prod.fst_zero, Prod.snd_zero, neg_zero, sub_zero]
  exact ipDiag_zero i

@[expose] def embTorus (M : ModelData F) {i : Fˣ} (hi4 : i ^ 4 = 1)
    (hdg : ∀ a b : ℕ, (dgen (i ^ a) (i ^ b) : GL (Fin 2) F) ∈ M.U2) :
    Multiplicative V4 →* PG M where
  toFun v := mkP M ⟨embTorusGL i (Multiplicative.toAdd v), embTorusGL_mem hi4 M hdg _⟩
  map_one' := by
    have h : (⟨embTorusGL i (Multiplicative.toAdd (1 : Multiplicative V4)),
        embTorusGL_mem hi4 M hdg _⟩ : ↥M.K4) = 1 :=
      Subtype.ext (embTorusGL_zero i)
    rw [h, map_one]
  map_mul' v w := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    exact embTorusGL_add hi4 _ _

@[expose] def embTau (F : Type) [Field F] : GL (Fin 4) F := diagGL (sw2 F) (dRefl F)

theorem embTau_mem (M : ModelData F) (hsw : sw2 F ∈ M.U2) (hR : dRefl F ∈ M.U2) :
    (embTau F : GL (Fin 4) F) ∈ M.K4 := by
  rw [embTau, M.diagGL_mem_K4_iff]
  refine ⟨hsw, hR, ?_⟩
  rw [det_sw2, det_dRefl]
  norm_num

theorem embTau_mul_ipDiag_mul_inv (i : Fˣ) (a b c d : ZMod 4) :
    embTau F * ipDiag i a b c d * (embTau F)⁻¹ = ipDiag i b a c d := by
  unfold embTau ipDiag
  rw [diagGL_conj, sw2_inv, dRefl_inv, sw2_mul_dgen_mul_sw2, dRefl_mul_dgen_mul_dRefl]

theorem swapGL_mul_ipDiag_mul_inv (i : Fˣ) (a b c d : ZMod 4) :
    swapGL F * ipDiag i a b c d * (swapGL F)⁻¹ = ipDiag i c d a b :=
  swapGL_mul_diagGL_mul_inv _ _

theorem embTau_mul_swapGL_pow_four : (embTau F * swapGL F) ^ 4 = xGL F := by
  have h1 : (embTau F * swapGL F) * (embTau F * swapGL F) =
      diagGL (sw2 F * dRefl F) (dRefl F * sw2 F) := by
    calc (embTau F * swapGL F) * (embTau F * swapGL F)
        = embTau F * (swapGL F * embTau F * swapGL F) := by simp only [mul_assoc]
      _ = embTau F * diagGL (dRefl F) (sw2 F) := by rw [embTau, swapGL_mul_diagGL_mul_swapGL]
      _ = diagGL (sw2 F * dRefl F) (dRefl F * sw2 F) := by rw [embTau, diagGL_mul]
  have h4 : (embTau F * swapGL F) ^ 4 =
      ((embTau F * swapGL F) * (embTau F * swapGL F)) *
        ((embTau F * swapGL F) * (embTau F * swapGL F)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4, h1, diagGL_mul, sw2_mul_dRefl_sq, dRefl_mul_sw2_sq]
  rfl

end Generators

section Relations

variable {F : Type} [Field F]

theorem emb_conj_eq_of_scalar (M : ModelData F) (g a b : ↥M.K4) (c : Fˣ)
    (h : ((g * a * g⁻¹ : ↥M.K4) : GL (Fin 4) F)⁻¹ * (b : GL (Fin 4) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) c) :
    mkP M g * mkP M a * (mkP M g)⁻¹ = mkP M b := by
  rw [← map_inv, ← map_mul, ← map_mul]
  exact mkP_eq_iff.2 ⟨c, h⟩

theorem emb_conj_tau (M : ModelData F) {i : Fˣ} (hi4 : i ^ 4 = 1)
    (hdg : ∀ a b : ℕ, (dgen (i ^ a) (i ^ b) : GL (Fin 2) F) ∈ M.U2)
    (hsw : sw2 F ∈ M.U2) (hR : dRefl F ∈ M.U2) (v : Multiplicative V4) :
    mkP M ⟨embTau F, embTau_mem M hsw hR⟩ * embTorus M hi4 hdg v *
        (mkP M ⟨embTau F, embTau_mem M hsw hR⟩)⁻¹ = embTorus M hi4 hdg (ψ aR v) := by
  obtain ⟨⟨x, y⟩, rfl⟩ : ∃ w : V4, v = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd v, rfl⟩
  rw [psi_apply, refAct_apply_ofAdd, actV_aR]
  refine emb_conj_eq_of_scalar M _ _ _ (ipow i (-x)) ?_
  show (embTau F * ipDiag i 0 x y (-x - y) * (embTau F)⁻¹)⁻¹ *
    ipDiag i 0 (-x) (y - x) (-(-x) - (y - x)) = _
  rw [embTau_mul_ipDiag_mul_inv, ipDiag_inv hi4, ipDiag_mul hi4, ← ipDiag_scalar]
  congr 1 <;> revert x y <;> decide

theorem emb_conj_omega (M : ModelData F) {i : Fˣ} (hi4 : i ^ 4 = 1)
    (hdg : ∀ a b : ℕ, (dgen (i ^ a) (i ^ b) : GL (Fin 2) F) ∈ M.U2) (v : Multiplicative V4) :
    mkP M M.wK * embTorus M hi4 hdg v * (mkP M M.wK)⁻¹ = embTorus M hi4 hdg (ψ wR v) := by
  obtain ⟨⟨x, y⟩, rfl⟩ : ∃ w : V4, v = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd v, rfl⟩
  rw [psi_apply, refAct_apply_ofAdd, actV_wR]
  refine emb_conj_eq_of_scalar M _ _ _ (ipow i (-y)) ?_
  show (swapGL F * ipDiag i 0 x y (-x - y) * (swapGL F)⁻¹)⁻¹ *
    ipDiag i 0 (-x - 2 * y) (-y) (-(-x - 2 * y) - (-y)) = _
  rw [swapGL_mul_ipDiag_mul_inv, ipDiag_inv hi4, ipDiag_mul hi4, ← ipDiag_scalar]
  congr 1 <;> revert x y <;> decide

end Relations

theorem exists_M128_embedding {F : Type} [Field F] [Finite F] (M : ModelData F)
    (h2 : (2 : F) ≠ 0) {i : Fˣ} (hii : i * i = -1)
    (hdg : ∀ a b : ℕ, (dgen (i ^ a) (i ^ b) : GL (Fin 2) F) ∈ M.U2) (hsw : sw2 F ∈ M.U2)
    (hR : dRefl F ∈ M.U2) :
    ∃ Φ : M128 →* PG M, Function.Injective Φ := by
  have hi4 : i ^ 4 = 1 := pow_four_of_sq hii
  have hτ : mkP M ⟨embTau F, embTau_mem M hsw hR⟩ * mkP M ⟨embTau F, embTau_mem M hsw hR⟩ = 1 := by
    rw [← map_mul]
    have h : (⟨embTau F, embTau_mem M hsw hR⟩ * ⟨embTau F, embTau_mem M hsw hR⟩ : ↥M.K4) = 1 := by
      apply Subtype.ext
      show embTau F * embTau F = 1
      rw [embTau, diagGL_mul, sw2_mul_self, dRefl_mul_self, diagGL_one]
    rw [h, map_one]
  have hω : mkP M M.wK * mkP M M.wK = 1 := by
    rw [← map_mul, wK_mul_self, map_one]
  have hτω : (mkP M ⟨embTau F, embTau_mem M hsw hR⟩ * mkP M M.wK) ^ 4 = 1 := by
    rw [← map_mul, ← map_pow]
    have h : (⟨embTau F, embTau_mem M hsw hR⟩ * M.wK : ↥M.K4) ^ 4 = M.xK := by
      apply Subtype.ext
      show (embTau F * swapGL F) ^ 4 = xGL F
      exact embTau_mul_swapGL_pow_four
    rw [h]
    exact (QuotientGroup.eq_one_iff _).2 (xK_mem_Zs M)
  obtain ⟨Φ, hΦα, -, -⟩ := exists_hom_M128 (embTorus M hi4 hdg)
    (mkP M ⟨embTau F, embTau_mem M hsw hR⟩) (mkP M M.wK) hτ hω hτω
    (emb_conj_tau M hi4 hdg hsw hR) (emb_conj_omega M hi4 hdg)
  refine ⟨Φ, injective_of_zeta Φ ?_⟩
  have hz : Φ zeta = yP M := by
    rw [show zeta = SemidirectProduct.inl (Multiplicative.ofAdd ((0 : ZMod 4), (2 : ZMod 4)))
      from rfl, hΦα]
    refine mkP_eq_iff.2 ⟨ipow i 2, ?_⟩
    show (ipDiag i 0 0 2 (-0 - 2))⁻¹ * (yGL F) = _
    rw [yGL_eq_ipDiag hii, ipDiag_inv hi4, ipDiag_mul hi4, ← ipDiag_scalar]
    congr 1
  rw [hz]
  exact yP_ne_one M h2

section Models

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F]

theorem dgen_mem_uni_gen [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) {a b : Fˣ} (ha : a ^ (p ^ f + 1) = 1)
    (hb : b ^ (p ^ f + 1) = 1) : (dgen a b : GL (Fin 2) F) ∈ (ModelData.uni hF).U2 := by
  show dgen a b ∈ uniGL (unitaryInvolution F p f) 2
  rw [mem_uniGL]
  have hσ : ∀ x, unitaryInvolution F p f x = x ^ (p ^ f) := unitaryInvolution_apply F p f
  have hmat : conjTr (unitaryInvolution F p f) ((dgen a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((dgen a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(a : F) ^ (p ^ f) * a, (b : F) ^ (p ^ f) * b] := by
    rw [coe_dgen, conjTr_diagonal', Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j <;> simp [hσ]
  rw [hmat, ← Matrix.diagonal_one]
  have h1 : (a : F) ^ (p ^ f) * a = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) ha
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rwa [pow_succ] at this
  have h2 : (b : F) ^ (p ^ f) * b = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hb
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rwa [pow_succ] at this
  congr 1
  funext j
  fin_cases j
  · simpa using h1
  · simpa using h2

theorem sw2_mem_uni {σ : F ≃+* F} : sw2 F ∈ uniGL σ 2 := by
  show conjTr σ ((sw2 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
    ((sw2 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
  have h := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F))
    (sw2_mul_self (F := F))
  simp only [Units.val_mul, Units.val_one] at h
  have hc : conjTr σ ((sw2 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((sw2 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [conjTr, coe_sw2]
  rw [hc]
  exact h

end Models

theorem exists_M128_embedding_lin {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (hq : Nat.card F % 4 = 1) :
    ∃ Φ : M128 →* PG (ModelData.lin F), Function.Injective Φ := by
  obtain ⟨i, hii⟩ := exists_i_of_card (F := F) (by omega)
  exact exists_M128_embedding (ModelData.lin F) h2 hii (fun _ _ => Subgroup.mem_top _)
    (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem exists_M128_embedding_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : p ^ f % 4 = 3) :
    ∃ Φ : M128 →* PG (ModelData.uni hF), Function.Injective Φ := by
  have hcardF : Nat.card F % 4 ≠ 3 := by
    rw [hF, Nat.pow_mod, show p ^ f % 4 = 3 by omega]
    norm_num
  obtain ⟨i, hii⟩ := exists_i_of_card hcardF
  have hi4 := pow_four_of_sq hii
  have hiq : i ^ (p ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 4 * m := ⟨(p ^ f + 1) / 4, by omega⟩
    rw [hm, pow_mul, hi4, _root_.one_pow]
  have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  have h2 : (2 : F) ≠ 0 :=
    CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow (Fact.out : p.Prime) hp2 hF'
  have hpow : ∀ a : ℕ, (i ^ a) ^ (p ^ f + 1) = 1 := fun a => by
    rw [← pow_mul, mul_comm, pow_mul, hiq, _root_.one_pow]
  exact exists_M128_embedding (ModelData.uni hF) h2 hii
    (fun a b => dgen_mem_uni_gen hF (hpow a) (hpow b)) sw2_mem_uni dRefl_mem_uni

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
