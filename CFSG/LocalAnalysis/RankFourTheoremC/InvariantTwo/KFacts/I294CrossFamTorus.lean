module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamOrder
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryO.GL3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open

instance instFiniteUnitsEnd (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] : Finite (Module.End K V)ˣ :=
  Finite.of_equiv (GL (Fin (Module.finrank K V)) K)
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toMulEquiv).symm.toEquiv

section Torus

variable (K : Type) [Field K] [Finite K] (ch : ℕ) [Fact ch.Prime] [CharP K ch] (e : ℕ) [NeZero e]

noncomputable abbrev TorusAlg (a b : ℕ) : Type :=
  (Fin a → FiniteField.Extension K ch e) × (Fin b → K)

theorem finrank_torusAlg (a b : ℕ) : Module.finrank K (TorusAlg K ch e a b) = a * e + b := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp [FiniteField.finrank_extension]

theorem card_units_torusAlg (a b : ℕ) :
    Nat.card (TorusAlg K ch e a b)ˣ = (Nat.card K ^ e - 1) ^ a * (Nat.card K - 1) ^ b := by
  rw [Nat.card_congr MulEquiv.prodUnits.toEquiv, Nat.card_prod,
    Nat.card_congr MulEquiv.piUnits.toEquiv, Nat.card_congr MulEquiv.piUnits.toEquiv, Nat.card_pi,
    Nat.card_pi, Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin, Nat.card_units, Nat.card_units,
    FiniteField.natCard_extension]

variable {K} {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]

noncomputable def torusHom {a b : ℕ} (φ : TorusAlg K ch e a b ≃ₗ[K] V) :
    (TorusAlg K ch e a b)ˣ →* (Module.End K V)ˣ :=
  Units.map ((LinearEquiv.conjAlgEquiv K φ).toAlgHom.comp
    (Algebra.lmul K (TorusAlg K ch e a b))).toMonoidHom

theorem torusHom_injective {a b : ℕ} (φ : TorusAlg K ch e a b ≃ₗ[K] V) :
    Function.Injective (torusHom ch e φ) :=
  Units.map_injective ((LinearEquiv.conjAlgEquiv K φ).injective.comp
    (Algebra.lmul_injective (R := K) (A := TorusAlg K ch e a b)))

end Torus

section Sylow

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [Module.Finite K V] {p : ℕ} [hp : Fact p.Prime]

theorem isMulCommutative_of_isPGroup_GL (hp2 : Odd p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (hne : Module.finrank K V / e < p) {P : Subgroup (Module.End K V)ˣ} (hP : IsPGroup p P) :
    IsMulCommutative P := by
  obtain ⟨ch, hch⟩ := CharP.exists K
  haveI : Fact ch.Prime := ⟨CharP.char_is_prime K ch⟩
  haveI : NeZero e := ⟨he.ne'⟩
  set n := Module.finrank K V with hn
  set a := n / e with ha
  set b := n % e with hb
  have hab : a * e + b = n := by rw [mul_comm, ha, hb]; exact Nat.div_add_mod n e
  let φ : TorusAlg K ch e a b ≃ₗ[K] V :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_torusAlg, hab])
  let T := (torusHom ch e φ).range
  have hcardT : Nat.card T = (Nat.card K ^ e - 1) ^ a * (Nat.card K - 1) ^ b := by
    rw [← card_units_torusAlg K ch e a b]
    exact (Nat.card_congr (MonoidHom.ofInjective (torusHom_injective ch e φ)).toEquiv).symm
  have hcardG : Nat.card (Module.End K V)ˣ = Nat.card (GL (Fin n) K) :=
    Nat.card_congr (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Module.finBasis K V)).toMulEquiv).toEquiv
  have hvG : padicValNat p (Nat.card (Module.End K V)ˣ) =
      a * padicValNat p (Nat.card K ^ e - 1) := by
    rw [hcardG]
    exact padicValNat_card_GL hp2 hpK he hpe hne
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hqe : 1 < Nat.card K ^ e := Nat.one_lt_pow he.ne' hq1
  have hvT : padicValNat p (Nat.card T) = a * padicValNat p (Nat.card K ^ e - 1) := by
    rw [hcardT, padicValNat.mul (pow_ne_zero _ (Nat.sub_ne_zero_of_lt hqe))
      (pow_ne_zero _ (Nat.sub_ne_zero_of_lt hq1)), padicValNat.pow, padicValNat.pow]
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · simp [hb0]
    · have hbe : b < e := Nat.mod_lt n he
      have he1 : ¬ e ∣ 1 := fun h => by
        have := Nat.le_of_dvd one_pos h
        omega
      have : padicValNat p (Nat.card K - 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro h
        apply he1
        exact (hpe 1).1 (by simpa using h)
      simp [this]
  have hidx : ¬ p ∣ T.index := by
    have hmul : Nat.card T * T.index = Nat.card (Module.End K V)ˣ := T.card_mul_index
    have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
    have hI0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have := congrArg (padicValNat p) hmul
    rw [padicValNat.mul hT0 hI0, hvG, hvT] at this
    intro hd
    have h1 := (dvd_iff_padicValNat_ne_zero hI0).1 hd
    omega
  exact CFSG.SignalizerFunctorTheorem.McBride.UnitaryO.isMulCommutative_of_isPGroup_of_not_dvd_index
    T hidx hP

theorem le_pRank_GL (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) {r : ℕ} (hr : r * e ≤ Module.finrank K V) :
    r ≤ CFSG.Open.pRank p (⊤ : Subgroup (Module.End K V)ˣ) := by
  obtain ⟨ch, hch⟩ := CharP.exists K
  haveI : Fact ch.Prime := ⟨CharP.char_is_prime K ch⟩
  haveI : NeZero e := ⟨he.ne'⟩
  set b := Module.finrank K V - r * e with hb
  have hrb : r * e + b = Module.finrank K V := by omega
  let φ : TorusAlg K ch e r b ≃ₗ[K] V :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_torusAlg, hrb])
  have hdvd : p ∣ Nat.card (FiniteField.Extension K ch e)ˣ := by
    rw [Nat.card_units, FiniteField.natCard_extension]
    exact (hpe e).2 dvd_rfl
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let S := Subgroup.zpowers z
  have hSp : ∀ s : S, s ^ p = 1 := by
    rintro ⟨s, k, rfl⟩
    refine Subtype.ext ?_
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz, pow_orderOf_eq_one,
      one_zpow]
  have hSc : ∀ s t : S, s * t = t * s := by
    rintro ⟨s, k, rfl⟩ ⟨t, l, rfl⟩
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← zpow_add, ← zpow_add, add_comm]
  let φ1 : (Fin r → S) →* (Fin r → (FiniteField.Extension K ch e)ˣ) :=
    Pi.monoidHom fun i => S.subtype.comp (Pi.evalMonoidHom (fun _ => S) i)
  let φ2 : (Fin r → (FiniteField.Extension K ch e)ˣ) →* (TorusAlg K ch e r b)ˣ :=
    (Units.map (MonoidHom.inl (Fin r → FiniteField.Extension K ch e) (Fin b → K))).comp
      (MulEquiv.piUnits (M := fun _ : Fin r => FiniteField.Extension K ch e)).symm.toMonoidHom
  have hφ1 : Function.Injective φ1 := fun s t h =>
    funext fun i => Subtype.ext (congrFun h i)
  have hinl : Function.Injective
      (MonoidHom.inl (Fin r → FiniteField.Extension K ch e) (Fin b → K)) :=
    fun x y h => congrArg Prod.fst h
  have hφ2 : Function.Injective φ2 := (Units.map_injective hinl).comp (MulEquiv.injective _)
  let f : (Fin r → S) →* (Module.End K V)ˣ := (torusHom ch e φ).comp (φ2.comp φ1)
  have hf : Function.Injective f := (torusHom_injective ch e φ).comp (hφ2.comp hφ1)
  have hcard : Nat.card (Fin r → S) = p ^ r := by
    rw [Nat.card_fun, Nat.card_zpowers, hz, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt
    (fun s t => funext fun i => hSc _ _) (fun s => funext fun i => hSp _) hcard f hf le_top

end Sylow

end CFSG.LocalAnalysis.RankFourTheoremC
