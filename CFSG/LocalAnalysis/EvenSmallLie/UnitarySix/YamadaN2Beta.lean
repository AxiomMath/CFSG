module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Hyp

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def dProd (d : ℕ → Γ) (ν : ℕ) : Γ := ((bitList ν).map d).prod

@[expose] def betaG (e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)) (π : Γ →* (W →ₗ[ZMod 2] W))
    (x : Γ) : Mat8 := blk1M (matOfN e (π x))

@[expose] def deltaM (X : Mat8) : Mat8 := tM2 * X * tM2 + X

theorem deltaM_add (X Y : Mat8) : deltaM (X + Y) = deltaM X + deltaM Y := by
  simp only [deltaM, mul_add, add_mul]; abel

theorem blk1M_conj_one_add {V φ : Mat18} (hV : ∀ r c : Fin 18, clsN c < clsN r → V r c = 0)
    (hVV : V * V = 1) (hφ : FlagM φ) :
    blk1M (V * (1 + φ) * V) = sub0M V * blk1M (1 + φ) * sub1M V := by
  rw [mul_add, mul_one, add_mul, hVV, blk1M_add, blk1M_one, zero_add, blk1M_tri_conj hV hφ,
    blk1M_add, blk1M_one, zero_add]

theorem one_add_sub_one (M : Mat18) : 1 + (M - 1) = M := by abel

theorem msum8_eq_sum_bitList (μ : ℕ) (f : ℕ → Mat8) :
    ((bitList μ).map f).sum = msum8 4 μ f := by
  have key : ∀ l : List ℕ, ((l.filter fun n => μ.testBit n).map f).sum =
      (l.map fun n => bz (μ.testBit n) • f n).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons n l ih =>
      by_cases h : μ.testBit n
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
          List.map_cons, List.sum_cons, h, bz_true, one_smul]
      · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons,
          Bool.eq_false_iff.mpr h, bz_false, zero_smul, zero_add]
  rw [bitList, key, msum8]
  have hr : ∀ n : ℕ, ((List.range n).map fun m => bz (μ.testBit m) • f m).sum =
      ∑ m ∈ Finset.range n, bz (μ.testBit m) • f m := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.sum_range_succ, ih, Finset.sum_range_succ]
  exact hr 4

theorem aIndep {μ : ℕ} (hμ : μ < 16)
    (h0 : msum8 4 μ aM2 = 0) : μ = 0 := by
  have h := aIndepCheck_eq_true
  simp only [aIndepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  rcases h μ hμ with h1 | ⟨r, hr, c, hc, hb⟩
  · exact h1
  · exfalso
    have h1 := congrFun (congrFun h0 ⟨r, hr⟩) ⟨c, hc⟩
    have h2 : msum8 4 μ aM2 = toMat 8 8 (msum2 4 μ aBits2) := (toMat_msum2 4 μ aBits2).symm
    rw [h2, toMat_apply, Matrix.zero_apply] at h1
    change bz (((msum2 4 μ aBits2).getD r 0).testBit c) = 0 at h1
    rw [hb, bz_true] at h1
    exact one_ne_zero h1

section Beta

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem R3bHyp.beta_mul (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {x y : Γ} (hx : x ∈ D) (hy : y ∈ D) :
    betaG e π (x * y) = betaG e π x + betaG e π y := by
  unfold betaG
  have := blk1M_mul_flag (h.flagM hK hx) (h.flagM hK hy)
  rwa [one_add_sub_one, one_add_sub_one, ← mx_mul] at this

theorem betaG_one : betaG e π (1 : Γ) = 0 := by
  rw [betaG, map_one, matOfN_one, blk1M_one]

theorem R3bHyp.beta_list (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) (l : List Γ) (hl : ∀ x ∈ l, x ∈ D) :
    betaG e π l.prod = (l.map (betaG e π)).sum := by
  induction l with
  | nil => exact betaG_one
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      h.beta_mul hK (hl x (by simp)) (Subgroup.list_prod_mem _ fun y hy => hl y (by simp [hy])),
      ih fun y hy => hl y (by simp [hy])]

theorem R3bHyp.beta_conj (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {V' : Mat18}
    (hV : ∀ r c : Fin 18, clsN c < clsN r → V' r c = 0) (hVV : V' * V' = 1) {x : Γ}
    (hx : x ∈ D) : blk1M (V' * matOfN e (π x) * V') = sub0M V' * betaG e π x * sub1M V' := by
  have := blk1M_conj_one_add hV hVV (h.flagM hK hx)
  rwa [one_add_sub_one] at this

theorem R3bHyp.beta_τ (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {x : Γ} (hx : x ∈ D) :
    betaG e π (τ x) = tM2 * betaG e π x * tM2 := by
  rw [betaG, h.mx_τ he, h.beta_conj hK tauM_tri tauM_mul_self hx, sub0M_tauM, sub1M_tauM]

theorem R3bHyp.beta_ν (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {j : ℕ} (hj : j < 4) {x : Γ} (hx : x ∈ D) :
    betaG e π (θ (gen3 (nuS j)) * x * (θ (gen3 (nuS j)))⁻¹) =
      n0M2 j * betaG e π x * n1M2 j := by
  rw [betaG, ← map_inv, gen3_inv, mx_mul, mx_mul, mx_V hK,
    h.beta_conj hK (vM_tri hj) (vM_mul_self hj) hx, sub0M_vM hj, sub1M_vM hj]

theorem beta_E (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {m : ℕ} (hm : m < 4) :
    betaG e π (θ (gen3 (Fin.ofNat 12 m))) = aM2 m := by
  rw [betaG, mx_E hK, blk1M_eM hm]

theorem R3bHyp.beta_eProdG (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) (μ : ℕ) :
    betaG e π (eProdG θ μ) = msum8 4 μ aM2 := by
  rw [eProdG, h.beta_list hK _ (fun x hx => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact h.E_le n (bitList_lt hn)), List.map_map,
    ← msum8_eq_sum_bitList]
  congr 1
  exact List.map_congr_left fun n hn => beta_E hK (bitList_lt hn)

theorem R3bHyp.beta_dProd (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ} (hd : ∀ n < 4, d n ∈ D)
    (ν : ℕ) : betaG e π (dProd d ν) = msum8 4 ν fun n => betaG e π (d n) := by
  rw [dProd, h.beta_list hK _ (fun x hx => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hd n (bitList_lt hn)), List.map_map,
    ← msum8_eq_sum_bitList]
  rfl

theorem R3bHyp.dProd_mem (_h : R3bHyp π θ τW ι D W₀ V τ) {d : ℕ → Γ} (hd : ∀ n < 4, d n ∈ D)
    (ν : ℕ) : dProd d ν ∈ D :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hd n (bitList_lt hn)

theorem eProdG_zero : eProdG θ 0 = 1 := rfl

theorem R3bHyp.τ_fixed (h : R3bHyp π θ τW ι D W₀ V τ) {x : Γ} (hx : x ∈ D) :
    τ (x * τ x) = x * τ x := by
  rw [map_mul, h.ττ, h.D_comm _ (h.τD x hx) x hx]

theorem R3bHyp.beta_inj (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {x : Γ} (hx : x ∈ D)
    (h0 : betaG e π x = 0) : x = 1 := by
  have hw := h.τ_fixed hx
  obtain ⟨μ, hμ, hwμ⟩ := h.τfix _ (mul_mem hx (h.τD x hx)) hw
  have hβw : betaG e π (x * τ x) = 0 := by
    rw [h.beta_mul hK hx (h.τD x hx), h.beta_τ he hK hx, h0]; simp
  rw [hwμ, h.beta_eProdG hK] at hβw
  have hμ0 := aIndep hμ hβw
  rw [hμ0, eProdG_zero] at hwμ
  have hτx : τ x = x := by
    have : x⁻¹ = τ x := (eq_inv_of_mul_eq_one_right hwμ).symm
    rw [← this, h.inv_eq hx]
  obtain ⟨μ', hμ', hxμ'⟩ := h.τfix x hx hτx
  rw [hxμ', h.beta_eProdG hK] at h0
  rw [hxμ', aIndep hμ' h0, eProdG_zero]

end Beta

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
