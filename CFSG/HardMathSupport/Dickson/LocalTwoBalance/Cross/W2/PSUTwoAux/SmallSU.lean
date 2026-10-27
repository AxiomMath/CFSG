module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeLayer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.RankThree.PartOne.K133H.SylowTorus

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartOne

section Irreducible

variable {f : ℕ} {E : Type} [Field E]

theorem eq_top_of_invariant_gramSU (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 2) {m : ℕ}
    (hm : 2 ≤ m) (F : Submodule E (Fin m → E))
    (hF : ∀ A ∈ gramSU hE (1 : Matrix (Fin m) (Fin m) E), ∀ v ∈ F,
      (A : Matrix (Fin m) (Fin m) E) *ᵥ v ∈ F)
    {v : Fin m → E} (hv : v ∈ F) (hv0 : v ≠ 0) : F = ⊤ := by
  classical
  have h2 : (2 : E) = 0 := by
    have := hE.charP
    exact CharP.cast_eq_zero E 2
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨j, hji⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases h0 : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h => by rw [h0] at h; exact absurd (congrArg Fin.val h) (by simp)⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
  have hij : i ≠ j := hji.symm
  obtain ⟨c, hc, hc2⟩ := KCUnitary.exists_norm_one_sq_ne_one hE (by rw [hf])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact zero_ne_one hc
  have hci : hE.bar c⁻¹ * c⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hc, inv_one]
  obtain ⟨A₁, hA₁, hA₁g⟩ := unitLambdaDiag_mem hE hc hij
  obtain ⟨A₂, hA₂, hA₂g⟩ := unitLambdaDiag_mem hE hci hij
  have hw₁ := F.sub_mem (hF A₁ hA₁g v hv) hv
  have hw₂ := F.sub_mem (hF A₂ hA₂g v hv) hv
  rw [hA₁] at hw₁
  rw [hA₂] at hw₂
  set κ : E := (c - 1) * (c - 1) - (c⁻¹ - 1) * (c⁻¹ - 1) with hκ
  have hκ0 : κ ≠ 0 := by
    intro h0
    have h3 : (c - c⁻¹) * (c + c⁻¹) = 0 := by
      have : (c - c⁻¹) * (c + c⁻¹ - 2) = κ := by rw [hκ]; ring
      rw [h2, sub_zero] at this
      rw [this, h0]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · apply hc2
      have : c = c⁻¹ := sub_eq_zero.1 h4
      calc c ^ 2 = c * c := sq c
        _ = c * c⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel₀ hc0
    · apply hc2
      have h5 : c * (c + c⁻¹) = 0 := by rw [h4, mul_zero]
      have h6 : c ^ 2 + 1 = 0 := by
        have : c * (c + c⁻¹) = c ^ 2 + 1 := by field_simp
        rw [← this, h5]
      have h7 : (1 : E) + 1 = 0 := by
        have : (2 : E) = 1 + 1 := by norm_num
        rw [← this, h2]
      calc c ^ 2 = c ^ 2 + 1 - 1 := by ring
        _ = -1 := by rw [h6]; ring
        _ = 1 := by
          have := eq_neg_of_add_eq_zero_left h7
          exact this.symm
  have hu : (c - 1) • ((diagonal (unitLambdaDiag c i j)) *ᵥ v - v) -
      (c⁻¹ - 1) • ((diagonal (unitLambdaDiag c⁻¹ i j)) *ᵥ v - v) =
        (κ * v i) • Pi.single i (1 : E) := by
    funext r
    simp only [Pi.sub_apply, Pi.smul_apply, mulVec_diagonal, smul_eq_mul, unitLambdaDiag]
    by_cases hri : r = i
    · subst hri
      simp [hκ]
      ring
    · by_cases hrj : r = j
      · subst hrj
        simp [hri]
        ring
      · simp [hri, hrj]
  have hmem : (κ * v i) • (Pi.single i (1 : E) : Fin m → E) ∈ F := by
    rw [← hu]
    exact F.sub_mem (F.smul_mem _ hw₁) (F.smul_mem _ hw₂)
  have hei : (Pi.single i (1 : E) : Fin m → E) ∈ F := by
    have := F.smul_mem (κ * v i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hκ0 hi), one_smul] at this
  have hek : ∀ k : Fin m, (Pi.single k (1 : E) : Fin m → E) ∈ F := by
    intro k
    by_cases hk : k = i
    · rw [hk]; exact hei
    · obtain ⟨M, hM, hMg⟩ := unitSignedSwapMatrix_mem hE (Ne.symm hk)
      have := hF M hMg _ hei
      rw [hM, unitSignedSwapMatrix_mulVec] at this
      convert this using 1
      funext r
      simp only [unitSignedSwap]
      by_cases hrk : r = k
      · subst hrk
        simp [hk]
      · have : Equiv.swap i k r ≠ i := by
          intro h
          apply hrk
          have := (Equiv.swap_apply_eq_iff.1 h)
          simpa [Equiv.swap_apply_left] using this
        simp [hrk, Pi.single_apply, this]
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine F.sum_mem fun k _ => ?_
  have : (Pi.single k (w k) : Fin m → E) = w k • Pi.single k (1 : E) := by
    funext r
    simp [Pi.single_apply]
  rw [this]
  exact F.smul_mem _ (hek k)

theorem noNormalPPrime_three_gramSU (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 2) {m : ℕ}
    (hm : 2 ≤ m)
    (hord : Nat.card (gramSU hE (1 : Matrix (Fin m) (Fin m) E)) ∣ 2 ^ 3 * 3 ^ 3) :
    NoNormalPPrime 3 (gramSU hE (1 : Matrix (Fin m) (Fin m) E)) := by
  classical
  intro N hNS hNn hNc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card N ∣ 2 ^ 3 * 3 ^ 3 := (Subgroup.card_dvd_of_le hNS).trans hord
  have hN2 : Nat.card N ∣ 2 ^ 3 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 3 hNc.symm) hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hN2
  have hpg : IsPGroup 2 N := IsPGroup.of_card hj
  letI : MulAction N (Fin m → E) := MulAction.compHom (Fin m → E)
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin m) E ≃* _).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (n : N) (v : Fin m → E),
      n • v = ((n : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v := fun n v => rfl
  have : Finite E := hE.finite
  have hcardE : Nat.card E = 4 := by
    rw [hE.card, pow_mul', hf]
    norm_num
  have hpα : 2 ∣ Nat.card (Fin m → E) := by
    rw [Nat.card_pi]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    rw [hcardE]
    exact dvd_pow (by norm_num : 2 ∣ 4) (by omega)
  have h0 : (0 : Fin m → E) ∈ MulAction.fixedPoints N (Fin m → E) := fun n =>
    (hsmul n 0).trans (mulVec_zero _)
  obtain ⟨b, hb, hb0⟩ := hpg.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin m → E) hpα h0
  let F : Submodule E (Fin m → E) :=
    { carrier := {v | ∀ n : N, ((n : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v = v}
      add_mem' := fun {a b} ha hb n => by rw [mulVec_add, ha n, hb n]
      zero_mem' := fun n => by simp
      smul_mem' := fun c v hv n => by rw [mulVec_smul, hv n] }
  have hbF : b ∈ F := fun n => by rw [← hsmul]; exact hb n
  have hFtop : F = ⊤ := by
    refine eq_top_of_invariant_gramSU hE hf hm F ?_ hbF (Ne.symm hb0)
    intro A hA v hv n
    obtain ⟨n, hn⟩ := n
    have hn' : (A⁻¹ * n * A⁻¹⁻¹ : GL (Fin m) E) ∈ N :=
      hNn A⁻¹ ((gramSU hE (1 : Matrix (Fin m) (Fin m) E)).inv_mem hA) n hn
    have h1 : (n : Matrix (Fin m) (Fin m) E) * (A : Matrix (Fin m) (Fin m) E) =
        (A : Matrix (Fin m) (Fin m) E) *
          ((A⁻¹ * n * A⁻¹⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    show (n : Matrix (Fin m) (Fin m) E) *ᵥ ((A : Matrix (Fin m) (Fin m) E) *ᵥ v) =
      (A : Matrix (Fin m) (Fin m) E) *ᵥ v
    rw [mulVec_mulVec, h1, ← mulVec_mulVec]
    have := hv ⟨_, hn'⟩
    simp only at this
    rw [this]
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
  have hall : ∀ v : Fin m → E, ((n : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v = v := by
    intro v
    have : v ∈ F := by rw [hFtop]; trivial
    exact this ⟨n, hn⟩
  apply Units.ext
  ext r s
  have := congrFun (hall (Pi.single s 1)) r
  simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

end Irreducible

section Order

variable {f : ℕ} {E : Type} [Field E]

theorem card_gramSU_one_dvd (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 2) {m : ℕ}
    (hm : m = 2 ∨ m = 3) :
    Nat.card (gramSU hE (1 : Matrix (Fin m) (Fin m) E)) ∣ 2 ^ 3 * 3 ^ 3 := by
  have hfin : Finite E := hE.finite
  have hB : (gramForm hE (1 : Matrix (Fin m) (Fin m) E)).IsSymm :=
    gramForm_isSymm hE (by simp)
  have hBl : (gramForm hE (1 : Matrix (Fin m) (Fin m) E)).SeparatingLeft :=
    gramForm_separatingLeft hE (by simp)
  have hord := (CFSG.LinearGroups.unitary_full_group_order hE hB hBl
    (Module.finrank_fin_fun E) (by omega : 1 ≤ m)).2.1
  rw [card_gramSU]
  rw [hf] at hord
  rcases hm with rfl | rfl
  · have h6 : Nat.card (sesqSpecialUnitaryGroup (gramForm hE (1 : Matrix (Fin 2) (Fin 2) E))) = 6 := by
      have : (Nat.card (sesqSpecialUnitaryGroup (gramForm hE (1 : Matrix (Fin 2) (Fin 2) E))) : ℤ)
          = 6 := by
        rw [hord]; decide
      exact_mod_cast this
    rw [h6]; norm_num
  · have h216 : Nat.card (sesqSpecialUnitaryGroup (gramForm hE (1 : Matrix (Fin 3) (Fin 3) E))) =
        216 := by
      have : (Nat.card (sesqSpecialUnitaryGroup (gramForm hE (1 : Matrix (Fin 3) (Fin 3) E))) : ℤ)
          = 216 := by
        rw [hord]; decide
      exact_mod_cast this
    rw [h216]; norm_num

theorem noNormalPPrime_three_gramSU_of_mem (hE : UnitaryFieldData 2 f E) (hf : 2 ^ f = 2)
    {m : ℕ} (hm : m = 2 ∨ m = 3) :
    NoNormalPPrime 3 (gramSU hE (1 : Matrix (Fin m) (Fin m) E)) :=
  noNormalPPrime_three_gramSU hE hf (by omega) (card_gramSU_one_dvd hE hf hm)

end Order

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
