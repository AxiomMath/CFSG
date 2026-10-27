module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDCode
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JF4a

@[expose] public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

def s8dI : ZMod 2 →+ Sec12F4 where
  toFun c := if c = 0 then 0 else 1
  map_zero' := rfl
  map_add' := by decide

def s8dCo (j : Fin 4) : EvW →+ ZMod 2 where
  toFun a := a.1 4 + a.1 j.castSucc
  map_zero' := by simp
  map_add' a b := by
    simp only [Submodule.coe_add, Pi.add_apply]
    ring

def s8dQ : Fin 8 → Sec12M :=
  ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![1, 1; 1, 1], !![1, Sec12F4.w2; Sec12F4.w, 1],
    !![Sec12F4.w, 0; 0, 0], !![0, 0; 0, Sec12F4.w], !![Sec12F4.w, Sec12F4.w; Sec12F4.w, Sec12F4.w],
    !![Sec12F4.w, 1; Sec12F4.w2, Sec12F4.w]]

def s8dPomH : (EvW × EvW) →+ Sec12M where
  toFun p := ∑ j : Fin 4, (s8dI (s8dCo j p.1) • s8dQ ⟨j, by omega⟩ +
    s8dI (s8dCo j p.2) • s8dQ ⟨j + 4, by omega⟩)
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    abel

private theorem s8dPomH_dec_eq_zero : ∀ n < 256, s8dPomH (s8dDec n) = 0 → n = 0 := by
  decide +kernel

private theorem s8d_zmod2_add_self' (x : ZMod 2) : x + x = 0 := by
  revert x
  decide +kernel

private theorem s8d_vec_add_self (v : EvW × EvW) : v + v = 0 := by
  obtain ⟨a, b⟩ := v
  refine Prod.ext (Subtype.ext (funext fun i => ?_)) (Subtype.ext (funext fun i => ?_))
  · exact s8d_zmod2_add_self' (a.1 i)
  · exact s8d_zmod2_add_self' (b.1 i)

private theorem s8d_mat_add_self (M : Sec12M) : M + M = 0 := by
  have h : ∀ x : Sec12F4, x + x = 0 := by decide
  ext i j
  exact h (M i j)

theorem s8d_card_mat : Nat.card Sec12M = 256 := by
  show Nat.card (Fin 2 → Fin 2 → Sec12F4) = 256
  rw [Nat.card_fun, Nat.card_fun, sec12F4_card, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin]
  norm_num

theorem s8dPomH_bijective : Function.Bijective s8dPomH := by
  have hinj : Function.Injective s8dPomH := by
    intro p q hpq
    obtain ⟨n, hn, hpn⟩ := s8dDec_surj (p + q)
    have h0 : s8dPomH (s8dDec n) = 0 := by
      rw [hpn, map_add, hpq, s8d_mat_add_self]
    have hz : p + q = 0 := by rw [← hpn, s8dPomH_dec_eq_zero n hn h0, s8dDec_zero]
    calc p = p + (q + q) := by rw [s8d_vec_add_self, add_zero]
      _ = (p + q) + q := (add_assoc _ _ _).symm
      _ = q := by rw [hz, zero_add]
  refine hinj.bijective_of_nat_card_le ?_
  have h2 : 256 ≤ Nat.card (EvW × EvW) := by
    have h := Nat.card_le_card_of_injective (fun n : Fin 256 => s8dDec (n : ℕ))
      (fun a b hab => Fin.ext (s8dDec_inj a.2 b.2 hab))
    rwa [Nat.card_eq_fintype_card (α := Fin 256), Fintype.card_fin] at h
  rw [s8d_card_mat]
  exact h2

noncomputable def s8dPom : (EvW × EvW) ≃+ Sec12M := AddEquiv.ofBijective s8dPomH s8dPomH_bijective

theorem s8dPom_apply (p : EvW × EvW) : s8dPom p = s8dPomH p := rfl

theorem s8d_sl_coe_mul (A B : Sec12SL) :
    ((A * B : Sec12SL) : Sec12M) = (A : Sec12M) * (B : Sec12M) := rfl

theorem s8d_sl_coe_one : ((1 : Sec12SL) : Sec12M) = 1 := rfl

theorem s8d_sl_inv_mul (A : Sec12SL) : ((A⁻¹ : Sec12SL) : Sec12M) * (A : Sec12M) = 1 :=
  congrArg (fun X : Sec12SL => (X : Sec12M)) (inv_mul_cancel A)

theorem s8d_sl_mul_inv (A : Sec12SL) : (A : Sec12M) * ((A⁻¹ : Sec12SL) : Sec12M) = 1 :=
  congrArg (fun X : Sec12SL => (X : Sec12M)) (mul_inv_cancel A)

def s8dLmap (A B : Sec12SL) : Sec12M ≃+ Sec12M where
  toFun M := (A : Sec12M) * M * (B : Sec12M)ᵀ
  invFun M := ((A⁻¹ : Sec12SL) : Sec12M) * M * ((B⁻¹ : Sec12SL) : Sec12M)ᵀ
  left_inv M := by
    have hA := s8d_sl_inv_mul A
    have hB : (B : Sec12M)ᵀ * ((B⁻¹ : Sec12SL) : Sec12M)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, s8d_sl_inv_mul, Matrix.transpose_one]
    show ((A⁻¹ : Sec12SL) : Sec12M) * ((A : Sec12M) * M * (B : Sec12M)ᵀ) *
      ((B⁻¹ : Sec12SL) : Sec12M)ᵀ = M
    calc _ = (((A⁻¹ : Sec12SL) : Sec12M) * (A : Sec12M)) * M *
          ((B : Sec12M)ᵀ * ((B⁻¹ : Sec12SL) : Sec12M)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hA, hB, Matrix.one_mul, Matrix.mul_one]
  right_inv M := by
    have hA := s8d_sl_mul_inv A
    have hB : ((B⁻¹ : Sec12SL) : Sec12M)ᵀ * (B : Sec12M)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, s8d_sl_mul_inv, Matrix.transpose_one]
    show (A : Sec12M) * (((A⁻¹ : Sec12SL) : Sec12M) * M * ((B⁻¹ : Sec12SL) : Sec12M)ᵀ) *
      (B : Sec12M)ᵀ = M
    calc _ = ((A : Sec12M) * ((A⁻¹ : Sec12SL) : Sec12M)) * M *
          (((B⁻¹ : Sec12SL) : Sec12M)ᵀ * (B : Sec12M)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hA, hB, Matrix.one_mul, Matrix.mul_one]
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mul]

theorem s8dLmap_apply (A B : Sec12SL) (M : Sec12M) :
    s8dLmap A B M = (A : Sec12M) * M * (B : Sec12M)ᵀ := rfl

noncomputable def s8dOm : Sec12SL × Sec12SL →* S8A where
  toFun AB := s8dOfAdd ((s8dPom.trans (s8dLmap AB.1 AB.2)).trans s8dPom.symm)
  map_one' := s8d_ext fun p => by
    rw [s8dAp_ofAdd, s8dAp_one]
    simp only [AddEquiv.trans_apply, s8dLmap_apply, Prod.fst_one, Prod.snd_one,
      s8d_sl_coe_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
      AddEquiv.symm_apply_apply]
  map_mul' AB CD := s8d_ext fun p => by
    rw [s8dAp_mul, s8dAp_ofAdd, s8dAp_ofAdd, s8dAp_ofAdd]
    simp only [AddEquiv.trans_apply, s8dLmap_apply, AddEquiv.apply_symm_apply, Prod.fst_mul,
      Prod.snd_mul, s8d_sl_coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem s8dAp_om (A B : Sec12SL) (p : EvW × EvW) :
    s8dPom (s8dAp (s8dOm (A, B)) p) = (A : Sec12M) * s8dPom p * (B : Sec12M)ᵀ :=
  s8dPom.apply_symm_apply _

theorem s8dAg_det : (!![0, Sec12F4.w2; Sec12F4.w, Sec12F4.w2] : Sec12M).det = 1 := by
  rw [Matrix.det_fin_two_of]
  decide

theorem s8dAgF_det : (!![0, Sec12F4.w; Sec12F4.w2, Sec12F4.w] : Sec12M).det = 1 := by
  rw [Matrix.det_fin_two_of]
  decide

def s8dAg : Sec12SL := ⟨!![0, Sec12F4.w2; Sec12F4.w, Sec12F4.w2], s8dAg_det⟩

def s8dAgF : Sec12SL := ⟨!![0, Sec12F4.w; Sec12F4.w2, Sec12F4.w], s8dAgF_det⟩

noncomputable def s8dOm1 : S8A := s8dOm (s8dAg, 1)

noncomputable def s8dOm2 : S8A := s8dOm (1, s8dAgF)

end CFSG.OddStandard.SmallF3.Omega
