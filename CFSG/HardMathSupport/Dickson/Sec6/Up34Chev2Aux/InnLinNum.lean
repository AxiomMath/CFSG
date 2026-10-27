module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.ComponentClassification.CatLeaf

namespace Up34Chev2

theorem factorization_twenty_thousand_two : (20160 : ℕ).factorization 2 = 6 := by
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem isLThreeFour_cases_psl_two (hO : LieOrderFormulasInput) {X : Type} [Group X] {m e : ℕ}
    (hm : CFSG.Blueprint.LieModel X .PSL m 2 e) (hL : IsLThreeFour X) :
    (m = 3 ∧ e = 2) ∨ (m = 4 ∧ e = 1) := by
  have hadm := hm.admissible
  obtain ⟨-, hnum, hfac⟩ := hO X .PSL m 2 e hadm hm
  have hc : Nat.card X = 20160 := card_eq_of_isLThreeFour hL
  rw [hc] at hnum hfac
  simp only [lieSylowExponent] at hfac
  rw [factorization_twenty_thousand_two] at hfac
  have hm2 : 2 ≤ m := hadm.2.2.1
  have he : 1 ≤ e := hadm.2.1
  have hm4 : m ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have h10 : 10 ≤ m * (m - 1) / 2 := by
      have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul hcon (by omega)
      omega
    nlinarith
  interval_cases m
  · have he6 : e = 6 := by omega
    subst he6
    have h1 : lieOrderNumerator .PSL 2 (2 ^ 6) = 262080 := by decide +kernel
    have h2 : lieOrderDivisor .PSL 2 (2 ^ 6) = 1 := by decide
    rw [h1, h2] at hnum
    omega
  · left
    exact ⟨rfl, by omega⟩
  · right
    exact ⟨rfl, by omega⟩

theorem not_isLThreeFour_psu_two (hO : LieOrderFormulasInput) {X : Type} [Group X] {m e : ℕ}
    (hm : CFSG.Blueprint.LieModel X .PSU m 2 e) : ¬ IsLThreeFour X := by
  intro hL
  have hadm := hm.admissible
  obtain ⟨-, hnum, hfac⟩ := hO X .PSU m 2 e hadm hm
  have hc : Nat.card X = 20160 := card_eq_of_isLThreeFour hL
  rw [hc] at hnum hfac
  simp only [lieSylowExponent] at hfac
  rw [factorization_twenty_thousand_two] at hfac
  have hm3 : 3 ≤ m := hadm.2.2.1
  have he : 1 ≤ e := hadm.2.1
  have hm4 : m ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have h10 : 10 ≤ m * (m - 1) / 2 := by
      have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul hcon (by omega)
      omega
    nlinarith
  interval_cases m
  · have he2 : e = 2 := by omega
    subst he2
    have h1 : lieOrderNumerator .PSU 3 (2 ^ 2) = 62400 := by decide +kernel
    have h2 : lieOrderDivisor .PSU 3 (2 ^ 2) = 1 := by decide
    rw [h1, h2] at hnum
    omega
  · have he1 : e = 1 := by omega
    subst he1
    have h1 : lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 := by decide +kernel
    have h2 : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide
    rw [h1, h2] at hnum
    omega

section Four

def sl4T : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

def sl4G : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 1, 0; 0, 0, 0, 1], by decide⟩

def sl4U : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1], by decide⟩

def sl4V : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

theorem sl4_comm : sl4T * sl4G = sl4G * sl4T := by decide
theorem sl4T_sq : sl4T * sl4T = 1 := by decide
theorem sl4G_cube : sl4G * sl4G * sl4G = 1 := by decide
theorem sl4T_not_comm : sl4T * sl4U ≠ sl4U * sl4T := by decide
theorem sl4G_not_comm : sl4G * sl4V ≠ sl4V * sl4G := by decide

end Four

theorem not_isLThreeFour_sl_four_two {F : Type} [Group F]
    {E : Type} [Field E] (hE : Nat.card E = 2)
    (e : F ≃* Matrix.SpecialLinearGroup (Fin 4) E) :
    ¬ IsLThreeFour (F ⧸ Subgroup.center F) := by
  intro hL
  have hX := statedClassicalModel_of_lieModel_psl (isL34Type_of_isLThreeFour hL)
  obtain ⟨-, hcent, -⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated.{0} _ hX
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hE]; norm_num)
  let φ : ZMod 2 →+* E := ZMod.castHom (dvd_refl 2) E
  let Φ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin 4) E :=
    Matrix.SpecialLinearGroup.map φ
  have hΦ : Function.Injective Φ := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 4) E => (x : Matrix (Fin 4) (Fin 4) E))
      hab
    exact Matrix.map_injective φ.injective (by simpa [Φ] using this)
  let ι : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* F ⧸ Subgroup.center F :=
    (QuotientGroup.mk' (Subgroup.center F)).comp (e.symm.toMonoidHom.comp Φ)
  have hcen : ∀ a : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), ι a = 1 →
      ∀ b : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), a * b = b * a := by
    intro a ha b
    have hmem : e.symm (Φ a) ∈ Subgroup.center F := (QuotientGroup.eq_one_iff _).1 ha
    have h1 := Subgroup.mem_center_iff.1 hmem (e.symm (Φ b))
    apply hΦ
    apply e.symm.injective
    rw [map_mul, map_mul, map_mul, map_mul]
    exact h1.symm
  have ht1 : ι sl4T ≠ 1 := fun h => sl4T_not_comm (hcen _ h _)
  have hg1 : ι sl4G ≠ 1 := fun h => sl4G_not_comm (hcen _ h _)
  have ht2 : orderOf (ι sl4T) = 2 := by
    refine orderOf_eq_prime ?_ ht1
    rw [← map_pow, pow_two, sl4T_sq, map_one]
  have hg3 : orderOf (ι sl4G) = 3 := by
    refine orderOf_eq_prime ?_ hg1
    rw [← map_pow, show sl4G ^ 3 = 1 from by rw [pow_succ, pow_two, sl4G_cube], map_one]
  have hmem : ι sl4G ∈ Subgroup.centralizer ({ι sl4T} : Set (F ⧸ Subgroup.center F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, sl4_comm]
  have hdvd := orderOf_dvd_natCard (⟨ι sl4G, hmem⟩ :
    ↥(Subgroup.centralizer ({ι sl4T} : Set (F ⧸ Subgroup.center F))))
  rw [Subgroup.orderOf_mk, hg3, hcent _ ht2] at hdvd
  omega

theorem exists_central_three_sl_three_four {F : Type} [Group F] {E : Type} [Field E]
    (hE : Nat.card E = 4) (e : F ≃* Matrix.SpecialLinearGroup (Fin 3) E) :
    ∃ z : F, z ∈ Subgroup.center F ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hcube : ∀ a : E, a ≠ 0 → a ^ 3 = 1 := by
    intro a ha
    have h4 : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card, hE]
    have : a ^ 4 = a := by simpa [h4] using FiniteField.pow_card a
    have h : a * (a ^ 3 - 1) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 ha
    · exact sub_eq_zero.1 h1
  obtain ⟨ζ, hζ0, hζ1⟩ : ∃ ζ : E, ζ ≠ 0 ∧ ζ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Fintype.card E ≤ 2 := by
      calc Fintype.card E = (Finset.univ : Finset E).card := Finset.card_univ.symm
        _ ≤ ({0, 1} : Finset E).card := Finset.card_le_card (fun a _ => by
            by_cases ha : a = 0
            · simp [ha]
            · simp [hcon a ha])
        _ ≤ 2 := Finset.card_le_two
    rw [← Nat.card_eq_fintype_card, hE] at hle
    omega
  have hζ3 : ζ ^ 3 = 1 := hcube ζ hζ0
  let z0 : Matrix.SpecialLinearGroup (Fin 3) E :=
    ⟨ζ • (1 : Matrix (Fin 3) (Fin 3) E), by
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      simpa using hζ3⟩
  have hz0c : z0 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) E) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Matrix (Fin 3) (Fin 3) E) * (ζ • (1 : Matrix (Fin 3) (Fin 3) E)) =
      (ζ • (1 : Matrix (Fin 3) (Fin 3) E)) * (g : Matrix (Fin 3) (Fin 3) E)
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  refine ⟨e.symm z0, ?_, ?_, ?_⟩
  · have := Subgroup.map_center_eq e.symm
    rw [← this]
    exact Subgroup.mem_map_of_mem _ hz0c
  · rw [← map_pow]
    have : z0 ^ 3 = 1 := by
      apply Subtype.ext
      change (ζ • (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3 = 1
      rw [smul_pow, hζ3, one_pow, one_smul]
    rw [this, map_one]
  · intro h1
    have : z0 = 1 := e.symm.injective (h1.trans (map_one _).symm)
    have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) E =>
      (x : Matrix (Fin 3) (Fin 3) E) 0 0) this
    simp [z0] at h2
    exact hζ1 h2

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
