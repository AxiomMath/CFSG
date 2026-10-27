module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphAut
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem scalar_of_commute_transvection {T : Matrix (Fin 3) (Fin 3) F}
    (hT : ∀ i j : Fin 3, i ≠ j → T * transvection i j 1 = transvection i j 1 * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h : T ∈ Set.range (Matrix.scalar (Fin 3)) := by
    refine mem_range_scalar_of_commute_single fun i j hij => ?_
    have h1 := hT i j hij
    simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    exact (add_left_cancel h1).symm
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [← hc, smul_one_eq_diagonal, scalar_apply]⟩

theorem semilinear_fix_reduce [Finite F] {Ω : Subgroup SL(3, F)} (hperf : Group.IsPerfect Ω)
    {R : Set SL(3, F)} (hRΩ : R ⊆ Ω)
    (hRfix : ∀ ρ : F ≃+* F, ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F).map ρ = g)
    (hRcomm : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ R, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
        ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    {A : GL (Fin 3) F} {τ : F ≃+* F}
    (hfix : ∀ g ∈ Ω,
      (conjAut 3 F A * fieldAut 3 F τ) (LinearFlag.proj 3 F g) = LinearFlag.proj 3 F g) :
    conjAut 3 F A = 1 ∧ ∀ g ∈ Ω, (g : Matrix (Fin 3) (Fin 3) F).map τ = g := by
  have hinv : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
      = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hf1 := Odd87.semiSL_fix_of_perfect A τ hperf fun g hg => by
    rw [← Odd87.beta_proj]; exact hfix g hg
  have hAcomm : ∀ g ∈ R, (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * A := by
    intro g hg
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (hf1 g (hRΩ hg))
    simp only [Odd87.coe_semiSL] at h1
    rw [hRfix τ g hg] at h1
    calc (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)
        = (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
            ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * A := by
          rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F), hinv, Matrix.mul_one]
      _ = (g : Matrix (Fin 3) (Fin 3) F) * A := by rw [h1]
  obtain ⟨c, hc⟩ := hRcomm _ hAcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) A.mul_inv
    simp [hc] at this
  have hA : conjAut 3 F A = 1 := by
    have hA' : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) = A := by
      apply Units.ext
      rw [hc, smul_one_eq_diagonal]
      rfl
    rw [← hA', conjAut_scalar]
  refine ⟨hA, fun g hg => ?_⟩
  have hf2 := Odd87.semiSL_fix_of_perfect 1 τ hperf fun g hg => by
    rw [← Odd87.beta_proj, map_one, one_mul]
    have h := hfix g hg
    rwa [hA, one_mul] at h
  have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (hf2 g hg)
  simpa [Odd87.coe_semiSL] using h1

theorem card_fix_zpowers [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (τ : F ≃+* F) : orderOf τ ∣ f ∧
      ∃ S : Subfield F, (S : Set F) = {a | τ a = a} ∧ Nat.card S = p ^ (f / orderOf τ) := by
  obtain ⟨-, -, -, -, -, hA⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hcard
  obtain ⟨hdvd, S, hS, hcS⟩ := hA (zpowers τ)
  rw [Nat.card_zpowers] at hdvd hcS
  refine ⟨hdvd, S, ?_, hcS⟩
  rw [hS]
  ext a
  refine ⟨fun h => h τ (mem_zpowers τ), fun h ρ hρ => ?_⟩
  have hst : τ ∈ MulAction.stabilizer (F ≃+* F) a := MulAction.mem_stabilizer_iff.2 h
  exact MulAction.mem_stabilizer_iff.1 ((zpowers_le.2 hst) hρ)

theorem ringEquiv_eq_one_of_fix_fixed [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) {σ τ : F ≃+* F} (hσ : σ ≠ 1) (hσσ : σ * σ = 1) {m : ℕ}
    (hm : Odd m) (hτ : τ ^ m = 1) (hfix : ∀ x, σ x = x → τ x = x) : τ = 1 := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ
  obtain ⟨hd1, S₁, hS₁, hc₁⟩ := card_fix_zpowers hp hf hcard σ
  obtain ⟨hd2, S₂, hS₂, hc₂⟩ := card_fix_zpowers hp hf hcard τ
  rw [hσ2] at hd1 hc₁
  have hr : Odd (orderOf τ) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hτ)
  have hle : Nat.card S₁ ≤ Nat.card S₂ := by
    have hsub : (S₁ : Set F) ⊆ (S₂ : Set F) := by
      rw [hS₁, hS₂]
      exact fun x hx => hfix x hx
    exact Nat.card_mono (Set.toFinite _) hsub
  rw [hc₁, hc₂] at hle
  have hle' : f / 2 ≤ f / orderOf τ := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have hr0 : 0 < orderOf τ := Nat.pos_of_dvd_of_pos hd2 (by omega)
  refine orderOf_eq_one_iff.1 ?_
  by_contra hne
  have h3 : 3 ≤ orderOf τ := by
    obtain ⟨k, hk⟩ := hr
    omega
  have h4 : f / orderOf τ ≤ f / 3 := Nat.div_le_div_left h3 (by norm_num)
  obtain ⟨k, hk⟩ := hd1
  omega

theorem ringEquiv_eq_one_of_fix_normOne [Finite F] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hcard : Nat.card F = (p ^ e) ^ 2) (τ : F ≃+* F)
    (hfix : ∀ x : F, x ^ (p ^ e + 1) = 1 → τ x = x) : τ = 1 := by
  have hq2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hf : Nat.card F = p ^ (2 * e) := by rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hog : orderOf g = (p ^ e) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have hfac : (p ^ e) ^ 2 - 1 = (p ^ e - 1) * (p ^ e + 1) := by
    rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
  have hdvd : p ^ e - 1 ∣ orderOf g := by rw [hog, hfac]; exact Dvd.intro _ rfl
  have hox : orderOf (g ^ (p ^ e - 1)) = p ^ e + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hog, hfac, Nat.mul_div_cancel_left _ (by omega)]
  have hx1 : ((g ^ (p ^ e - 1) : Fˣ) : F) ^ (p ^ e + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hox, pow_orderOf_eq_one, Units.val_one]
  obtain ⟨hd2, S, hS, hcS⟩ := card_fix_zpowers hp (by omega) hf τ
  have hxS : ((g ^ (p ^ e - 1) : Fˣ) : F) ∈ S := by
    rw [← SetLike.mem_coe, hS]
    exact hfix _ hx1
  let y : Sˣ := Units.mk0 ⟨_, hxS⟩ fun h => (g ^ (p ^ e - 1)).ne_zero (congrArg Subtype.val h)
  have hoy : orderOf y = p ^ e + 1 := by
    rw [← hox, ← orderOf_injective (Units.map S.subtype.toMonoidHom)
      (Units.map_injective Subtype.val_injective) y]
    exact congrArg orderOf (Units.ext rfl)
  have hdy : p ^ e + 1 ∣ Nat.card S - 1 := by
    rw [← hoy, ← Nat.card_units]
    exact orderOf_dvd_natCard y
  rw [hcS] at hdy
  have hr0 : 0 < orderOf τ := Nat.pos_of_dvd_of_pos hd2 (by omega)
  refine orderOf_eq_one_iff.1 ?_
  by_contra hne
  have hr2 : 2 ≤ orderOf τ := by omega
  have hdiv : 2 * e / orderOf τ ≤ e := by
    calc 2 * e / orderOf τ ≤ 2 * e / 2 := Nat.div_le_div_left hr2 (by norm_num)
      _ = e := by omega
  have hpos : 1 ≤ 2 * e / orderOf τ := (Nat.one_le_div_iff hr0).2 (Nat.le_of_dvd (by omega) hd2)
  have hle1 : p ^ (2 * e / orderOf τ) ≤ p ^ e := Nat.pow_le_pow_right hp.pos hdiv
  have hge : 2 ≤ p ^ (2 * e / orderOf τ) :=
    le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have := Nat.le_of_dvd (by omega) hdy
  omega

end CFSG.GH74.Generic.BProg.B3.S3T5L3
