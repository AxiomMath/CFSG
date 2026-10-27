module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421ZNeSupp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBorel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Gen

variable {G : Type} [Group G] [Finite G]

theorem twoPart_mul_of_card {X Y Z : Subgroup G} (h : Nat.card Z = Nat.card X * Nat.card Y) :
    twoPart Z = twoPart X * twoPart Y := by
  unfold twoPart
  rw [h, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp [pow_add]

theorem isSylowTwoOf_sup {X Y PX PY : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hinf : X ⊓ Y = ⊥) (hPXY : PX ≤ Subgroup.normalizer (PY : Set G)) (hPX : IsSylowTwoOf PX X)
    (hPY : IsSylowTwoOf PY Y) : IsSylowTwoOf (PX ⊔ PY) (X ⊔ Y) := by
  have h1 := card_sup_mul_card_inf hXY
  rw [hinf, Subgroup.card_bot, mul_one] at h1
  have hPinf : PX ⊓ PY = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf hPX.le hPY.le
  have h2 := card_sup_mul_card_inf hPXY
  rw [hPinf, Subgroup.card_bot, mul_one] at h2
  have hp : IsPGroup 2 ↥(PX ⊔ PY) := isPGroup_sup_of_le_normalizer hPXY hPX.isPGroup hPY.isPGroup
  refine isSylowTwoOf_of_card_eq (sup_le_sup hPX.le hPY.le) hp ?_
  rw [h2, hPX.card_eq, hPY.card_eq]
  exact (twoPart_mul_of_card h1).symm

theorem isSylowTwoOf_conjR {A X : Subgroup G} (h : IsSylowTwoOf A X) (g : G) :
    IsSylowTwoOf (conjR A g) (conjR X g) := by
  refine ⟨conjR_mono h.1 g, (isPGroup_conjR_iff 2).2 h.2.1, ?_⟩
  have := relIndex_conjR h.1 g
  have h3 := h.2.2
  unfold Subgroup.relIndex at this
  rw [this]
  exact h3

theorem hall_sylow_decomp' {K P D : Subgroup G} (hP : IsSylowTwoOf P K) (hD : IsHallTwoPrimeOf D K)
    (hDN : D ≤ Subgroup.normalizer (P : Set G)) :
    D ⊓ P = ⊥ ∧ P ⊔ D = K ∧ ∀ k ∈ K, ∃ p ∈ P, ∃ d ∈ D, k = p * d := by
  have hN : K ≤ Subgroup.normalizer (P : Set G) := by
    obtain ⟨hDK, hodd, e, he⟩ := hD
    have h2 : ¬ 2 ∣ Nat.card D := hodd.not_two_dvd_nat
    have hKcard : Nat.card K = 2 ^ e * Nat.card D := by
      have := Subgroup.relIndex_mul_card (H := D) (K := K)
      rw [inf_eq_left.mpr hDK, he] at this
      exact this.symm
    have hPcard : Nat.card P = 2 ^ e := by
      rw [hP.card_eq]
      unfold twoPart
      rw [hKcard, Nat.factorization_mul (by positivity) Nat.card_pos.ne']
      simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd h2,
        Nat.Prime.factorization_self Nat.prime_two]
    have hDP : D ⊓ P = ⊥ := by
      have h1 : Nat.card (D ⊓ P : Subgroup G) ∣ Nat.card D :=
        Subgroup.card_dvd_of_le inf_le_left
      have h3 : Nat.card (D ⊓ P : Subgroup G) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_right
      have hcop : Nat.Coprime (Nat.card D) (Nat.card P) := by
        rw [hPcard]
        exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)).symm
      have h4 : Nat.card (D ⊓ P : Subgroup G) ∣ Nat.gcd (Nat.card D) (Nat.card P) :=
        Nat.dvd_gcd h1 h3
      rw [Nat.Coprime.gcd_eq_one hcop] at h4
      exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_one h4)
    have hcardsup := card_sup_mul_card_inf hDN
    rw [hDP, Subgroup.card_bot, mul_one] at hcardsup
    have hsupK : P ⊔ D = K := by
      have hle : P ⊔ D ≤ K := sup_le hP.le hDK
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [sup_comm, hcardsup, hKcard, hPcard]
      exact le_of_eq (mul_comm _ _)
    rw [← hsupK]
    exact sup_le Subgroup.le_normalizer hDN
  exact hall_sylow_decomp hP hN hD

omit [Finite G] in
theorem sup_inf_left_of_commute {X Y X' Y' : Subgroup G} (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hbot : X ⊓ Y = ⊥) (hX' : X' ≤ X) (hY' : Y' ≤ Y) : (X' ⊔ Y') ⊓ X = X' := by
  apply le_antisymm
  · rintro x ⟨hx, hxX⟩
    have hN : Y' ≤ Subgroup.normalizer (X' : Set G) :=
      le_normalizer_of_commute fun a ha b hb => hXY a (hX' ha) b (hY' hb)
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hx
    have hbX : b ∈ X := by
      have := X.mul_mem (X.inv_mem (hX' ha)) hxX
      simpa using this
    have : b ∈ X ⊓ Y := ⟨hbX, hY' hb⟩
    rw [hbot, Subgroup.mem_bot] at this
    rw [this, mul_one]
    exact ha
  · exact le_inf le_sup_left hX'

omit [Finite G] in
theorem sup_inf_right_of_commute {X Y X' Y' : Subgroup G} (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hbot : X ⊓ Y = ⊥) (hX' : X' ≤ X) (hY' : Y' ≤ Y) : (X' ⊔ Y') ⊓ Y = Y' := by
  rw [sup_comm]
  exact sup_inf_left_of_commute (X := Y) (Y := X) (fun a ha b hb => (hXY b hb a ha).symm)
    (by rw [inf_comm]; exact hbot) hY' hX'

end Gen

end CFSG.QuasithinUnique.Lin2
