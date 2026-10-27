module

public import CFSG.ClassicalInvolution.Phan.PhanS19Gf
public import CFSG.ClassicalInvolution.Phan.PhanS18Core

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

theorem card_gf49 : Nat.card GF49 = 7 ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod 7) 0), Nat.card_prod, Nat.card_zmod]
  norm_num

theorem star_eq_pow_seven (x : GF49) : star x = x ^ 7 := by
  obtain ⟨a, b⟩ := x
  revert a b
  decide

@[expose] def m0 : Model GF49 where
  q := 7
  τ := starRingEnd GF49
  κ := -2
  card_K := card_gf49
  tau_pow x := star_eq_pow_seven x
  tau_tau x := star_star x
  κ_ne := by decide
  tau_κ := by decide
  two_ne := by decide

@[expose] def toVec (x : V7) : Vec GF49 :=
  Sum.elim ![x.x0, x.x1, x.x2] (Sum.elim ![x.x3, x.x4, x.x5] (fun _ => x.x6))

@[expose] def ofVec (v : Vec GF49) : V7 :=
  ⟨v (.inl 0), v (.inl 1), v (.inl 2), v (.inr (.inl 0)), v (.inr (.inl 1)), v (.inr (.inl 2)),
    v (.inr (.inr ()))⟩

theorem ofVec_toVec (x : V7) : ofVec (toVec x) = x := by
  rfl

theorem toVec_ofVec (v : Vec GF49) : toVec (ofVec v) = v := by
  funext i
  rcases i with i | i | i
  · fin_cases i <;> rfl
  · rcases i with i
    fin_cases i <;> rfl
  · rfl

theorem toVec_injective : Function.Injective toVec := fun x y h => by
  rw [← ofVec_toVec x, ← ofVec_toVec y, h]

theorem bf_toVec (x y : V7) : bf m0 (toVec x) (toVec y) = bfC x y := by
  simp only [bf, toVec, bfC, Fin.sum_univ_three, Sum.elim_inl, Sum.elim_inr]
  simp [m0]

theorem tauV_toVec (x : V7) : tauV m0 (toVec x) = toVec (tauC x) := by
  funext i
  rcases i with i | i | i
  · fin_cases i <;> rfl
  · rcases i with i
    fin_cases i <;> rfl
  · rfl

theorem her_toVec (x y : V7) : her m0 (toVec x) (toVec y) = herC x y := by
  rw [her, tauV_toVec, bf_toVec, herC]

theorem gram_toVec (x y : V7) : gram m0 (toVec x) (toVec y) = gramC x y := by
  rw [gram, her_toVec, her_toVec, her_toVec, her_toVec, gramC]

theorem isFF_toVec (x : V7) : IsFF m0 (toVec x) ↔ isFFC x = true := by
  simp [IsFF, isFFC, bf_toVec, her_toVec]

theorem col_toVec (x y : V7) : Col m0 (toVec x) (toVec y) ↔ colC x y = true := by
  simp [Col, colC, bf_toVec, gram_toVec]

theorem toVec_smulC (c : GF49) (x : V7) : toVec (smulC c x) = c • toVec x := by
  funext i
  rcases i with i | i | i
  · fin_cases i <;> rfl
  · rcases i with i
    fin_cases i <;> rfl
  · rfl

theorem toVec_tauC (x : V7) : toVec (tauC x) = tauV m0 (toVec x) := (tauV_toVec x).symm

noncomputable def ptC (x : V7) (h : isFFC x = true) : FFPt m0 :=
  FFPt.mk m0 ((isFF_toVec x).2 h)

@[expose] def SigmaWitt : Prop :=
  ∀ v w : Fin 2 → Vec GF49,
    (∀ i j, bf m0 (v i) (v j) = bf m0 (w i) (w j)) →
    (∀ i j, her m0 (v i) (v j) = her m0 (w i) (w j)) →
    (∀ c d : Fin 2 → GF49, ∑ i, c i • v i + ∑ i, d i • tauV m0 (v i) = 0 ↔
      ∑ i, c i • w i + ∑ i, d i • tauV m0 (w i) = 0) →
    ∃ g : SigmaIso m0, ∀ i, g.toLinearEquiv (v i) = w i

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
