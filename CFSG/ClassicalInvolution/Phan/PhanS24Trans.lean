module

public import CFSG.ClassicalInvolution.Phan.PhanS20Model

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

section GF49

theorem gf49_star_fixed_im_zero :
    ∀ a b : ZMod 7, star (⟨a, b⟩ : GF49) = ⟨a, b⟩ → b = 0 := by
  decide

theorem gf49_norm_exists : ∀ k : ZMod 7, k ≠ 0 →
    ∃ x y : ZMod 7, (⟨x, y⟩ : GF49) * star (⟨x, y⟩ : GF49) = ⟨k, 0⟩ := by
  decide

theorem gf49_exists_norm_eq {n : GF49} (hn : n ≠ 0) (hs : star n = n) :
    ∃ ν : GF49, ν * star ν = n := by
  obtain ⟨a, b⟩ := n
  have hb : b = 0 := gf49_star_fixed_im_zero a b hs
  subst hb
  have ha : a ≠ 0 := fun h => hn (by rw [h]; rfl)
  obtain ⟨x, y, h⟩ := gf49_norm_exists a ha
  exact ⟨⟨x, y⟩, h⟩

end GF49

theorem exists_ringEquiv_gf49 {K : Type} [Field K] [Finite K] (M : Model K) (hq : M.q = 7) :
    Nonempty (K ≃+* GF49) := by
  have hK : Nat.card K = Nat.card GF49 := by rw [M.card_K, hq, card_gf49]
  have : Finite GF49 := Nat.finite_of_card_ne_zero (by rw [card_gf49]; norm_num)
  let _ := Fintype.ofFinite K
  let _ := Fintype.ofFinite GF49
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact hK

section Scaling

variable {K : Type} [Field K]

@[expose] def scaleWts (ν : GF49) : Fin 3 ⊕ Fin 3 ⊕ Unit → GF49 :=
  Sum.elim (fun _ => ν) (Sum.elim (fun _ => star ν) (fun _ => 1))

theorem scaleWts_ne {ν : GF49} (hν : ν ≠ 0) (s : Fin 3 ⊕ Fin 3 ⊕ Unit) : scaleWts ν s ≠ 0 := by
  rcases s with i | i | i
  · simpa [scaleWts] using hν
  · simpa [scaleWts] using hν
  · simp [scaleWts]

@[expose] def scaleEquiv (φ : K ≃+* GF49) (w : Fin 3 ⊕ Fin 3 ⊕ Unit → GF49) (hw : ∀ s, w s ≠ 0) :
    Vec K ≃ Vec GF49 where
  toFun x := fun s => w s * φ (x s)
  invFun y := fun s => φ.symm ((w s)⁻¹ * y s)
  left_inv x := by
    funext s
    simp [hw s]
  right_inv y := by
    funext s
    simp [hw s]

theorem scaleEquiv_apply (φ : K ≃+* GF49) (w : Fin 3 ⊕ Fin 3 ⊕ Unit → GF49) (hw : ∀ s, w s ≠ 0)
    (x : Vec K) (s : Fin 3 ⊕ Fin 3 ⊕ Unit) : scaleEquiv φ w hw x s = w s * φ (x s) := rfl

def similGF49OfData (M : Model K) (φ : K ≃+* GF49) (ν n : GF49) (hν : ν ≠ 0) (hn : n ≠ 0)
    (hτ : ∀ x, φ (M.τ x) = star (φ x)) (hνn : ν * star ν = n) (hκ : n * φ M.κ = -2) :
    Simil M m0 where
  φ := φ
  T := scaleEquiv φ (scaleWts ν) (scaleWts_ne hν)
  n := n
  n_ne := hn
  smul c x := by
    funext s
    simp only [scaleEquiv_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  bf_eq x y := by
    simp only [bf, scaleEquiv_apply, scaleWts, Sum.elim_inl, Sum.elim_inr, map_add, map_mul,
      map_sum]
    have hκ' : m0.κ = n * φ M.κ := by rw [hκ]; rfl
    rw [hκ', mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hνn]
      ring
    · ring
  comm x := by
    funext s
    rcases s with i | i | i
    · simp [scaleEquiv_apply, scaleWts, tauV, hτ, m0, starRingEnd_apply]
    · simp [scaleEquiv_apply, scaleWts, tauV, hτ, m0, starRingEnd_apply]
    · simp [scaleEquiv_apply, scaleWts, tauV, hτ, m0, starRingEnd_apply]

theorem nonempty_simil_m0 [Finite K] (M : Model K) (hq : M.q = 7) : Nonempty (Simil M m0) := by
  obtain ⟨φ⟩ := exists_ringEquiv_gf49 M hq
  have hτ : ∀ x, φ (M.τ x) = star (φ x) := fun x => by
    rw [M.tau_pow, hq, map_pow, star_eq_pow_seven]
  have hκ0 : φ M.κ ≠ 0 := by simpa using M.κ_ne
  have hκs : star (φ M.κ) = φ M.κ := by rw [← hτ, M.tau_κ]
  have hn0 : (-2 : GF49) / φ M.κ ≠ 0 := div_ne_zero (by decide) hκ0
  have hns : star ((-2 : GF49) / φ M.κ) = (-2 : GF49) / φ M.κ := by
    rw [star_div₀, hκs, star_neg, star_ofNat]
  obtain ⟨ν, hνn⟩ := gf49_exists_norm_eq hn0 hns
  have hν : ν ≠ 0 := fun h => hn0 (by rw [← hνn, h, zero_mul])
  exact ⟨similGF49OfData M φ ν _ hν hn0 hτ hνn (div_mul_cancel₀ _ hκ0)⟩

end Scaling

theorem muConnected_of_m0 (h : Std.Q.MuConnected m0) {K : Type} [Field K] [Finite K]
    (M : Model K) (hq : M.q = 7) : Std.Q.MuConnected M := by
  obtain ⟨S⟩ := nonempty_simil_m0 M hq
  intro A C hAC B D hAB hCB hAD hCD
  exact S.muConnectedAt_of_simil (h _ _ ((S.bf_ptMap_ne_iff A C).2 hAC)) B D hAB hCB hAD hCD

theorem q7Residual_of_muConnected_m0 (h : Std.Q.MuConnected m0) : PhanB3.S.Q7Residual :=
  PhanB3.S.q7Residual_of_muConnected fun _ _ _ M hq => muConnected_of_m0 h M hq

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
