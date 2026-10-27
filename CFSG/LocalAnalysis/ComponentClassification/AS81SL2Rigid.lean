module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Walter.Defs

public section
namespace CFSG.ComponentClassification.AS81

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section SL2

variable {F : Type*} [Field F]

theorem sl2Upper_one_mul_weyl_pow_three :
    (sl2Upper F 1 * sl2Weyl F 1) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Diag_inv (t : Fˣ) : (sl2Diag F t)⁻¹ = sl2Diag F t⁻¹ := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Weyl_mul_diag (t : Fˣ) :
    sl2Weyl F 1 * sl2Diag F t = (sl2Diag F t)⁻¹ * sl2Weyl F 1 := by
  rw [sl2Diag_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Lower_eq_weyl_conj (c : F) :
    sl2Lower F c = sl2Weyl F 1 * sl2Upper F (-c) * (sl2Weyl F 1)⁻¹ := by
  rw [sl2Weyl_mul_upper, mul_inv_cancel_right]
  congr 1
  simp

def sl2UpperSubgroup (F : Type*) [Field F] : Subgroup SL(2, F) where
  carrier := Set.range (sl2Upper F)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, sl2Upper_add a b⟩
  one_mem' := ⟨0, sl2Upper_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, sl2Upper_neg a⟩

theorem sl2Upper_mem_sl2UpperSubgroup (c : F) : sl2Upper F c ∈ sl2UpperSubgroup F :=
  ⟨c, rfl⟩

theorem sl2Upper_injective : Function.Injective (sl2Upper F) := fun a b h => by
  have := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa using this

theorem card_sl2UpperSubgroup [Finite F] : Nat.card (sl2UpperSubgroup F) = Nat.card F :=
  Nat.card_range_of_injective sl2Upper_injective

variable [CharP F 2]

theorem exists_eq_sl2Upper_of_commute {M : SL(2, F)}
    (h : M * sl2Upper F 1 = sl2Upper F 1 * M) : ∃ s, M = sl2Upper F s := by
  have h00 := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h01 := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, Matrix.mul_apply,
    Fin.sum_univ_two] at h00 h01
  simp at h00 h01
  have hc : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h00
  have hd : (M : Matrix (Fin 2) (Fin 2) F) 1 1 = (M : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -h01
  have hdet := M.2
  rw [det_fin_two, hc, hd, mul_zero, sub_zero] at hdet
  have ha : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    CharTwo.sq_injective (show _ ^ 2 = (1 : F) ^ 2 by rw [sq, hdet, one_pow])
  refine ⟨(M : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]

theorem sl2_aut_eq_one_of_fix_upper {α : MulAut SL(2, F)} (hα : Odd (orderOf α)) (t : Fˣ)
    (ht : (t : F) ≠ 1) (hfix : ∀ c, α (sl2Upper F c) = sl2Upper F c) : α = 1 := by
  set h₀ := sl2Diag F t with hh₀
  have hconj : ∀ c, h₀ * sl2Upper F c * h₀⁻¹ = sl2Upper F ((t : F) ^ 2 * c) := fun c => by
    rw [hh₀, sl2Diag_mul_upper, mul_inv_cancel_right]
  have h1 : α h₀ * sl2Upper F 1 * (α h₀)⁻¹ = h₀ * sl2Upper F 1 * h₀⁻¹ := by
    calc α h₀ * sl2Upper F 1 * (α h₀)⁻¹ = α (h₀ * sl2Upper F 1 * h₀⁻¹) := by
          rw [map_mul, map_mul, map_inv, hfix]
      _ = h₀ * sl2Upper F 1 * h₀⁻¹ := by rw [hconj, hfix]
  have hM : h₀⁻¹ * α h₀ * sl2Upper F 1 = sl2Upper F 1 * (h₀⁻¹ * α h₀) := by
    calc h₀⁻¹ * α h₀ * sl2Upper F 1
        = h₀⁻¹ * (α h₀ * sl2Upper F 1 * (α h₀)⁻¹) * α h₀ := by group
      _ = h₀⁻¹ * (h₀ * sl2Upper F 1 * h₀⁻¹) * α h₀ := by rw [h1]
      _ = sl2Upper F 1 * (h₀⁻¹ * α h₀) := by group
  obtain ⟨s, hs⟩ := exists_eq_sl2Upper_of_commute hM
  have hαh : α h₀ = h₀ * sl2Upper F s := by
    rw [← hs]
    group
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  have htt : (t : F) - (t : F)⁻¹ ≠ 0 := by
    intro h
    apply ht
    have h' : (t : F) * (t : F) = 1 := by
      have : (t : F) = (t : F)⁻¹ := sub_eq_zero.mp h
      calc (t : F) * t = t * (t : F)⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel₀ ht0
    exact CharTwo.sq_injective (show (t : F) ^ 2 = 1 ^ 2 by rw [sq, h', one_pow])
  have ht2 : (t : F) ^ 2 - 1 ≠ 0 := by
    intro h
    apply htt
    field_simp
    linear_combination h
  set e : F := (t : F) ^ 2 * s / ((t : F) ^ 2 - 1) with he
  have key : (t : F) * e = (t : F) * s + e * (t : F)⁻¹ := by
    rw [he]
    field_simp
    ring
  set v := sl2Upper F e with hv
  have hhv : h₀ * v = v * (h₀ * sl2Upper F s) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hv, hh₀]
    linear_combination key
  have hvh : v⁻¹ * h₀ * v = h₀ * sl2Upper F s := by
    calc v⁻¹ * h₀ * v = v⁻¹ * (h₀ * v) := by group
      _ = h₀ * sl2Upper F s := by rw [hhv]; group
  set α' := MulAut.conj v * α with hα'
  have hα'apply : ∀ y, α' y = v * α y * v⁻¹ := fun y => rfl
  have hα'h : α' h₀ = h₀ := by
    rw [hα'apply, hαh, ← hvh]
    group
  have hα'u : ∀ c, α' (sl2Upper F c) = sl2Upper F c := fun c => by
    rw [hα'apply, hfix, hv, ← sl2Upper_add, add_comm, sl2Upper_add, mul_inv_cancel_right]
  set w := sl2Weyl F 1 with hw
  have hwh : w * h₀ = h₀⁻¹ * w := sl2Weyl_mul_diag t
  set D := w⁻¹ * α' w with hD
  have hDh : D * h₀ = h₀ * D := by
    have h2 : α' w * h₀ = h₀⁻¹ * α' w := by
      have := congrArg α' hwh
      rwa [map_mul, map_mul, map_inv, hα'h] at this
    have h3 : w⁻¹ * h₀⁻¹ = h₀ * w⁻¹ := by
      calc w⁻¹ * h₀⁻¹ = w⁻¹ * (h₀⁻¹ * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * h₀) * w⁻¹ := by rw [hwh]
        _ = h₀ * w⁻¹ := by group
    calc D * h₀ = w⁻¹ * (α' w * h₀) := by rw [hD]; group
      _ = (w⁻¹ * h₀⁻¹) * α' w := by rw [h2]; group
      _ = h₀ * D := by rw [h3, hD]; group
  have hD01 : (D : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F) 0 1) hDh
    simp [hh₀, Matrix.mul_apply, Fin.sum_univ_two] at h
    have : (D : Matrix (Fin 2) (Fin 2) F) 0 1 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination -h
    exact (mul_eq_zero.mp this).resolve_right htt
  have hD10 : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F) 1 0) hDh
    simp [hh₀, Matrix.mul_apply, Fin.sum_univ_two] at h
    have : (D : Matrix (Fin 2) (Fin 2) F) 1 0 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp this).resolve_right htt
  have hα'wD : α' w = w * D := by
    rw [hD]
    group
  have hN : (sl2Upper F 1 * (w * D)) ^ 3 = 1 := by
    have := congrArg α' (sl2Upper_one_mul_weyl_pow_three (F := F))
    rwa [map_pow, map_mul, hα'u, map_one, hα'wD] at this
  have hdetD : (D : Matrix (Fin 2) (Fin 2) F) 0 0 * (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := D.2
    rw [det_fin_two, hD01, hD10, mul_zero, sub_zero] at this
    exact this
  set m := (D : Matrix (Fin 2) (Fin 2) F) 0 0 with hm_def
  set d := (D : Matrix (Fin 2) (Fin 2) F) 1 1 with hd_def
  have hm0 : m ≠ 0 := left_ne_zero_of_mul_eq_one hdetD
  have hdm : d = m⁻¹ := (inv_eq_of_mul_eq_one_right hdetD).symm
  set μ : Fˣ := Units.mk0 m hm0 with hμ
  have hDeq : D = sl2Diag F μ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD01, hD10, hμ, m, d, ← hdm]
  have hNm : ((sl2Upper F 1 * (w * D) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![-m, m⁻¹; -m, 0] := by
    rw [hDeq, hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hμ]
  have h11 := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F) 1 1) hN
  simp only [Matrix.SpecialLinearGroup.coe_pow, hNm, Matrix.SpecialLinearGroup.coe_one] at h11
  simp [pow_succ] at h11
  have hm : m = 1 := by
    field_simp at h11
    linear_combination h11
  have hD1 : D = 1 := by
    rw [hDeq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hμ, hm]
  have hα'w : α' w = w := by rw [hα'wD, hD1, mul_one]
  have hα'l : ∀ c, α' (sl2Lower F c) = sl2Lower F c := fun c => by
    rw [sl2Lower_eq_weyl_conj, map_mul, map_mul, map_inv, hα'u, ← hw, hα'w]
  have hα'1 : α' = 1 := by
    have heq : α'.toMonoidHom = MonoidHom.id SL(2, F) := by
      refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := F)) ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hα'u c
      · exact hα'l c
    exact MulEquiv.ext fun y => DFunLike.congr_fun heq y
  have hαv : α = (MulAut.conj v)⁻¹ := eq_inv_of_mul_eq_one_right hα'1
  have hv2 : v ^ 2 = 1 := by
    rw [sq, hv, ← sl2Upper_add, CharTwo.add_self_eq_zero, sl2Upper_zero]
  have hα2 : α ^ 2 = 1 := by
    rw [hαv, inv_pow, ← map_pow, hv2, map_one, inv_one]
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hα2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hα
    exact absurd hα (by decide)

end SL2

section PSL2

open CFSG.Walter

theorem psl2_aut_eq_one_of_fix {n : ℕ} (hn : 2 ≤ n) {U : Subgroup PSL(2, GaloisField 2 n)}
    (hU : Nat.card U = 2 ^ n) {α : MulAut PSL(2, GaloisField 2 n)} (hα : Odd (orderOf α))
    (hfix : ∀ u ∈ U, α u = u) : α = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  set e := psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n) with he
  set β := MulAut.congr e α with hβdef
  have hβ : ∀ y, β y = e (α (e.symm y)) := fun y => rfl
  have hβodd : Odd (orderOf β) := by
    rw [hβdef, MulEquiv.orderOf_eq]
    exact hα
  have hcard : Nat.card SL(2, GaloisField 2 n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv]
    exact psl2_even_card hn0
  have hodd : Odd ((2 ^ n) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn0⟩, two_ne_zero⟩) odd_one
  have hfac : (Nat.card SL(2, GaloisField 2 n)).factorization 2 = n := by
    have hne : (2 ^ n) ^ 2 - 1 ≠ 0 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
    rw [hcard, Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat]
    simp
  set U' := U.map e.toMonoidHom with hU'def
  have hU' : Nat.card U' = 2 ^ (Nat.card SL(2, GaloisField 2 n)).factorization 2 := by
    rw [hfac, hU'def, Subgroup.card_map_of_injective e.injective, hU]
  have hU₀ : Nat.card (sl2UpperSubgroup (GaloisField 2 n)) =
      2 ^ (Nat.card SL(2, GaloisField 2 n)).factorization 2 := by
    rw [hfac, card_sl2UpperSubgroup, hF]
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq SL(2, GaloisField 2 n)
    (Sylow.ofCard _ hU₀) (Sylow.ofCard _ hU')
  have hxU : ∀ c, x * sl2Upper (GaloisField 2 n) c * x⁻¹ ∈ U' := by
    intro c
    have h1 : sl2Upper (GaloisField 2 n) c ∈
        ((Sylow.ofCard _ hU₀ : Sylow 2 SL(2, GaloisField 2 n)) : Subgroup _) :=
      sl2Upper_mem_sl2UpperSubgroup c
    have h2 : MulAut.conj x • sl2Upper (GaloisField 2 n) c ∈
        ((x • Sylow.ofCard _ hU₀ : Sylow 2 SL(2, GaloisField 2 n)) : Subgroup _) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hx, Sylow.coe_ofCard] at h2
    simpa [MulAut.smul_def, MulAut.conj_apply] using h2
  set γ := (MulAut.conj x)⁻¹ * β * MulAut.conj x with hγdef
  have hγ : ∀ y, γ y = x⁻¹ * β (x * y * x⁻¹) * x := fun y => rfl
  have hγodd : Odd (orderOf γ) := by
    have : γ = MulAut.conj (MulAut.conj x)⁻¹ β := by
      rw [hγdef, MulAut.conj_apply, inv_inv]
    rw [this, MulEquiv.orderOf_eq]
    exact hβodd
  have hγfix : ∀ c, γ (sl2Upper (GaloisField 2 n) c) = sl2Upper (GaloisField 2 n) c := by
    intro c
    obtain ⟨u, hu, hue⟩ := hxU c
    have hue' : e u = x * sl2Upper (GaloisField 2 n) c * x⁻¹ := hue
    rw [hγ, ← hue', hβ, MulEquiv.symm_apply_apply, hfix u hu, hue']
    group
  obtain ⟨t, ht⟩ : ∃ t : (GaloisField 2 n)ˣ, (t : GaloisField 2 n) ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set (GaloisField 2 n)) ⊆ {0, 1} := by
      intro a _
      by_cases ha : a = 0
      · exact Or.inl ha
      · exact Or.inr (h (Units.mk0 a ha))
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, hF] at h1
    have h2 := Set.ncard_insert_le (0 : GaloisField 2 n) {1}
    rw [Set.ncard_singleton] at h2
    have h3 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hγ1 := sl2_aut_eq_one_of_fix_upper hγodd t ht hγfix
  have hβ1 : β = 1 := by
    have : β = MulAut.conj x * γ * (MulAut.conj x)⁻¹ := by
      rw [hγdef]
      group
    rw [this, hγ1, mul_one, mul_inv_cancel]
  apply (MulAut.congr e).injective
  rw [← hβdef, hβ1, map_one]

end PSL2

end CFSG.ComponentClassification.AS81
