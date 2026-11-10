
module

public import Mathlib
public meta import Mathlib
public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs

@[expose] public section

namespace CFSG.GH74.GLS.Stage4.Q9

namespace F9

section Algebra

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[simp] theorem inv_re (a : F9) : (a⁻¹).re = a.re * (a.re * a.re + a.im * a.im) := rfl
@[simp] theorem inv_im (a : F9) : (a⁻¹).im = -(a.im * (a.re * a.re + a.im * a.im)) := rfl

end Algebra

end F9

theorem card_F9 : Fintype.card F9 = 9 := by decide

theorem nu_not_isSquare : ¬ IsSquare nu := by decide

theorem card_SL2 : Fintype.card SL2 = 720 := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_SL_field (𝔽 := F9) 2]
  simp [Fin.prod_univ_two, card_F9]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9
local notation "𝐀" => ((A0 : Matrix.GeneralLinearGroup (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)
local notation "𝐁" => ((A0⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)

theorem sigmaAut_apply_val (g : SL2) :
    ((sigmaAut g : SL2) : Matrix (Fin 2) (Fin 2) F9) =
      (A0 : Matrix (Fin 2) (Fin 2) F9) * (g : Matrix (Fin 2) (Fin 2) F9) *
        ((A0⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9) :=
  sigmaFun_val g

theorem sigmaAut_apply_entries (g : SL2) :
    ((sigmaAut g : SL2) : Matrix (Fin 2) (Fin 2) F9) =
      !![(g : Matrix (Fin 2) (Fin 2) F9) 1 1, nu * (g : Matrix (Fin 2) (Fin 2) F9) 1 0;
         nu⁻¹ * (g : Matrix (Fin 2) (Fin 2) F9) 0 1, (g : Matrix (Fin 2) (Fin 2) F9) 0 0] := rfl

theorem sigmaHom_ofAdd_one : sigmaHom (Multiplicative.ofAdd 1) = sigmaAut := by
  have h : (1 : ZMod 2).val = 1 := rfl
  show sigmaAut ^ (1 : ZMod 2).val = sigmaAut
  rw [h, pow_one]

theorem card_Lg : Nat.card Lg = 1440 := by
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card (α := SL2), card_SL2]
  simp

theorem innerL_apply (g : SL2) : innerL g = ⟨g, 1⟩ := rfl

theorem parityL_innerL (g : SL2) : parityL (innerL g) = 1 := SemidirectProduct.rightHom_inl g

theorem exists_innerL_of_parityL_eq_one {l : Lg} (h : parityL l = 1) : ∃ g, l = innerL g :=
  ⟨l.left, by
    rcases l with ⟨g, a⟩
    have : a = 1 := h
    subst this
    rfl⟩

theorem innerL_injective : Function.Injective innerL := SemidirectProduct.inl_injective

theorem minusOne_val : (minusOne : Matrix (Fin 2) (Fin 2) F9) = -1 := rfl

theorem sigmaAut_minusOne : sigmaAut minusOne = minusOne := by
  apply Subtype.ext
  rw [sigmaAut_apply_val]
  show 𝐀 * (-1 : 𝕄) * 𝐁 = -1
  rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Units.mul_inv A0]

theorem minusOne_mul_comm (g : SL2) : minusOne * g = g * minusOne := by
  apply Subtype.ext
  show (-1 : 𝕄) * (g : 𝕄) = (g : 𝕄) * (-1 : 𝕄)
  rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]

theorem sigmaHom_minusOne (a : Multiplicative (ZMod 2)) : sigmaHom a minusOne = minusOne := by
  obtain ⟨a, rfl⟩ : ∃ a', a = Multiplicative.ofAdd a' := ⟨a.toAdd, rfl⟩
  fin_cases a
  · show sigmaHom (1 : Multiplicative (ZMod 2)) minusOne = minusOne
    rw [map_one]; rfl
  · show sigmaHom (Multiplicative.ofAdd 1) minusOne = minusOne
    rw [sigmaHom_ofAdd_one, sigmaAut_minusOne]

theorem innerL_minusOne_mem_center : innerL minusOne ∈ Subgroup.center Lg := by
  rw [Subgroup.mem_center_iff]
  intro l
  rcases l with ⟨g, a⟩
  show (⟨g, a⟩ : Lg) * (⟨minusOne, 1⟩ : Lg) = (⟨minusOne, 1⟩ : Lg) * ⟨g, a⟩
  simp only [SemidirectProduct.mul_def]
  rw [map_one]
  refine SemidirectProduct.ext ?_ ?_
  · show g * sigmaHom a minusOne = minusOne * (1 : MulAut SL2) g
    rw [sigmaHom_minusOne, minusOne_mul_comm]; rfl
  · simp

theorem minusOne_sq : minusOne ^ 2 = 1 := by
  apply Subtype.ext
  show (-1 : 𝕄) ^ 2 = 1
  decide

theorem minusOne_ne_one : minusOne ≠ 1 := by
  intro h
  have := congrArg (fun x : SL2 => (x : 𝕄) 0 0) h
  revert this
  decide

theorem orderOf_minusOne : orderOf minusOne = 2 :=
  orderOf_eq_prime minusOne_sq minusOne_ne_one

theorem normSL_eq (g : SL2) : normSL g = g :=
  Subtype.ext (Matrix.eta_fin_two _).symm

theorem normL_eq (x : Lg) : normL x = x := by
  rcases x with ⟨g, a⟩
  simp [normL, normSL_eq]

theorem ordLAux_spec (l : Lg) (k : ℕ) : ∀ (n : ℕ) (p : Lg), p = l ^ n → 1 ≤ n →
    (∀ j, 1 ≤ j → j < n → l ^ j ≠ 1) → ordLAux l k p n ≠ 0 → orderOf l = ordLAux l k p n := by
  induction k with
  | zero => intro n p _ _ _ h; simp [ordLAux] at h
  | succ k ih =>
    intro n p hp hn hlt h
    simp only [ordLAux] at h ⊢
    split_ifs at h ⊢ with hp1
    · have hln : l ^ n = 1 := hp ▸ hp1
      exact (orderOf_eq_iff (by omega)).mpr ⟨hln, fun m hm hm0 => hlt m hm0 hm⟩
    · refine ih (n + 1) _ ?_ (by omega) ?_ h
      · rw [normL_eq, hp, pow_succ]
      · intro j hj1 hjn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with h' | rfl
        · exact hlt j hj1 h'
        · rw [← hp]; exact hp1

def tauL : Lg := ⟨1, Multiplicative.ofAdd 1⟩

theorem parityL_tauL : parityL tauL ≠ 1 := by
  show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1
  decide

theorem tauL_conj_innerL (M : SL2) : tauL * innerL M * tauL⁻¹ = innerL (sigmaAut M) := by
  have h := SemidirectProduct.inl_aut (φ := sigmaHom) (Multiplicative.ofAdd (1 : ZMod 2)) M
  rw [sigmaHom_ofAdd_one] at h
  have e : tauL = SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) := rfl
  rw [e, ← map_inv]
  exact h.symm

def Chat : Subgroup (Lg × Lg) :=
  MonoidHom.eqLocus (parityL.comp (MonoidHom.fst Lg Lg)) (parityL.comp (MonoidHom.snd Lg Lg))

theorem mem_Chat_iff {p : Lg × Lg} : p ∈ Chat ↔ parityL p.1 = parityL p.2 := Iff.rfl

instance : DecidablePred (· ∈ Chat) := fun _ => decidable_of_iff _ mem_Chat_iff.symm

instance : Fintype Chat := Subtype.fintype (· ∈ Chat)

def kappa0 : Lg × Lg := (innerL minusOne, innerL minusOne)

theorem kappa0_mem : kappa0 ∈ Chat :=
  mem_Chat_iff.mpr rfl

def tauHat : Lg × Lg := (tauL, tauL)

theorem tauHat_mem : tauHat ∈ Chat :=
  mem_Chat_iff.mpr rfl

theorem Chat_inner_pair (M N : SL2) : ((innerL M, innerL N) : Lg × Lg) ∈ Chat :=
  mem_Chat_iff.mpr (by rw [parityL_innerL, parityL_innerL])

theorem card_Chat : Nat.card Chat = 1036800 := by
  let φ : Lg × Lg →* Multiplicative (ZMod 2) :=
    (parityL.comp (MonoidHom.fst Lg Lg)) * (parityL.comp (MonoidHom.snd Lg Lg))
  have hpar : ∀ a b : Multiplicative (ZMod 2), a * b = 1 ↔ a = b := by decide
  have hker : φ.ker = Chat := by
    ext p
    simp only [MonoidHom.mem_ker, mem_Chat_iff, φ, MonoidHom.mul_apply, MonoidHom.comp_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd]
    exact hpar _ _
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y = 1 ∨ y = Multiplicative.ofAdd 1 := by revert y; decide
    rcases hy with rfl | rfl
    · exact ⟨1, map_one φ⟩
    · refine ⟨(tauL, 1), ?_⟩
      show parityL tauL * parityL 1 = Multiplicative.ofAdd 1
      rw [map_one, mul_one]
      rfl
  have hindex : Chat.index = 2 := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hsurj,
      Subgroup.card_top]
    simp
  have h := Subgroup.card_mul_index Chat
  rw [hindex, Nat.card_prod, card_Lg] at h
  omega

end CFSG.GH74.GLS.Stage4.Q9
