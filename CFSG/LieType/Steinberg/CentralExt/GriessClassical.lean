module

public import CFSG.LieType.Steinberg.CentralExt.PSLAlternating
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalTwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.UnitaryTwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusFour
public import CFSG.LieType.Steinberg.CentralExt.SUThreeField
public import CFSG.LieType.Steinberg.CentralExt.SpThree

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open scoped MatrixGroups

namespace CFSG.LieType.Steinberg.CentralExt.GriessClassical

theorem of_mulEquiv {X Y T : Type} [Group X] [Group Y] [Group T] (e : X ≃* Y)
    (h : commutator Y = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier Y ≃* T)) :
    commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃* T) := by
  obtain ⟨hY, ⟨eY⟩⟩ := h
  have : Group.IsPerfect Y := ⟨hY⟩
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨Group.IsPerfect.commutator_eq_top, ⟨(griessHopfMultiplierCongr e).trans eY⟩⟩

theorem of_mulEquiv_target {X T T' : Type} [Group X] [Group T] [Group T'] (e : T ≃* T')
    (h : commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃* T)) :
    commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃* T') :=
  ⟨h.1, h.2.map fun e' => e'.trans e⟩

noncomputable def toGenEx {t : StatedLieTag} {n p f a₁ a₂ b₁ b₂ : ℕ}
    (hg : genericOrders t n p f = (a₁, a₂)) (he : exceptionalOrders t n p f = (b₁, b₂)) :
    (Multiplicative (ZMod a₁) × Multiplicative (ZMod a₂)) ×
        (Multiplicative (ZMod b₁) × Multiplicative (ZMod b₂)) ≃*
      generic t n p f × exceptional t n p f :=
  MulEquiv.prodCongr
    (MulEquiv.prodCongr
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr (by rw [hg])).toAddEquiv)
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr (by rw [hg])).toAddEquiv))
    (MulEquiv.prodCongr
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr (by rw [he])).toAddEquiv)
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr (by rw [he])).toAddEquiv))

noncomputable def padOne (a : ℕ) :
    Multiplicative (ZMod a) ≃*
      (Multiplicative (ZMod a) × Multiplicative (ZMod 1)) ×
        (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) :=
  let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
  MulEquiv.prodUnique.symm.trans MulEquiv.prodUnique.symm

theorem exceptionalOrders_PSL {n p f : ℕ} (hp : p.Prime) (hf : 0 < f) :
    exceptionalOrders .PSL n p f = CFSG.Open.griessPSLExceptional n (p ^ f) := by
  have key : ∀ {r k : ℕ}, r.Prime → 0 < k → (p ^ f = r ^ k ↔ p = r ∧ f = k) := by
    intro r k hr hk
    constructor
    · intro h
      obtain ⟨f', rfl⟩ := Nat.exists_eq_add_of_lt hf
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_lt hk
      obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hp hr (by simpa using h)
      exact ⟨h1, by omega⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have h4 : p ^ f = 4 ↔ p = 2 ∧ f = 2 := by
    simpa using key (r := 2) (k := 2) Nat.prime_two (by norm_num)
  have h2 : p ^ f = 2 ↔ p = 2 ∧ f = 1 := by
    simpa using key (r := 2) (k := 1) Nat.prime_two (by norm_num)
  have h9 : p ^ f = 9 ↔ p = 3 ∧ f = 2 := by
    simpa using key (r := 3) (k := 2) Nat.prime_three (by norm_num)
  by_cases hA : n = 2 ∧ p = 2 ∧ f = 2
  · obtain ⟨rfl, rfl, rfl⟩ := hA
    decide
  by_cases hB : n = 3 ∧ p = 2 ∧ f = 1
  · obtain ⟨rfl, rfl, rfl⟩ := hB
    decide
  by_cases hC : n = 4 ∧ p = 2 ∧ f = 1
  · obtain ⟨rfl, rfl, rfl⟩ := hC
    decide
  by_cases hD : n = 2 ∧ p = 3 ∧ f = 2
  · obtain ⟨rfl, rfl, rfl⟩ := hD
    decide
  by_cases hE : n = 3 ∧ p = 2 ∧ f = 2
  · obtain ⟨rfl, rfl, rfl⟩ := hE
    decide
  have hd : exceptionalOrders .PSL n p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  rw [hd]
  unfold CFSG.Open.griessPSLExceptional
  rw [ite_eq_right (by rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp_all),
    ite_eq_right (by rintro ⟨rfl, h⟩; simp_all), ite_eq_right (by rintro ⟨rfl, h⟩; simp_all)]

namespace GriessExceptionalPow

theorem eq_two_two_of_pow_eq_four {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 4) :
    p = 2 ∧ f = 2 := by
  have hdvd : p ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h]
    exact dvd_pow_self p hf.ne'
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num))⟩

theorem eq_two_one_of_pow_eq_two {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 2) :
    p = 2 ∧ f = 1 := by
  have hdvd : p ∣ 2 := by
    rw [← h]
    exact dvd_pow_self p hf.ne'
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num))⟩

theorem eq_three_one_of_pow_eq_three {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 3) :
    p = 3 ∧ f = 1 := by
  have hdvd : p ∣ 3 := by
    rw [← h]
    exact dvd_pow_self p hf.ne'
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) (h.trans (by norm_num))⟩

end GriessExceptionalPow

variable {X : Type} [Group X] {n p f : ℕ}

theorem psl_row
    (h : StatedClassicalModel X .PSL n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSL n p f × exceptional .PSL n p f) := by
  obtain ⟨⟨hp, hf, hn, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK, GaloisField.card p f (by omega)]
  let φ : K ≃+* GaloisField p f := FiniteField.ringEquivOfCardEq hcardK
  let e' : X ≃* PSL(n, GaloisField p f) :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin n))
  have hsmall : n = 2 → 4 ≤ p ^ f := by
    rintro rfl
    have h1 : p ^ f ≠ 2 := fun h => h22 (by rw [h])
    have h2 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
    have h0 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    omega
  refine of_mulEquiv e' (of_mulEquiv_target ?_ (SLClosed.griess_psl p f n (by omega) hn hsmall))
  set g := Nat.gcd n (p ^ f - 1)
  set E := CFSG.Open.griessPSLExceptional n (p ^ f)
  let _ : Unique (Multiplicative (ZMod 1)) := inferInstance
  exact (MulEquiv.prodMultiplicative _ _).trans ((MulEquiv.prodCongr (MulEquiv.refl _)
    (MulEquiv.prodMultiplicative _ _)).trans ((MulEquiv.prodCongr MulEquiv.prodUnique.symm
      (MulEquiv.refl _)).trans (toGenEx (t := .PSL) (n := n) (p := p) (f := f) (a₁ := g) (a₂ := 1)
        (b₁ := E.1) (b₂ := E.2) (by simp [genericOrders, g])
        ((exceptionalOrders_PSL hp (by omega)).trans (Prod.mk.eta).symm))))

theorem psu_row
    (h : StatedClassicalModel X .PSU n p f) (he : Even n)
    (hq : 4 ≤ p ^ f ∨ (p ^ f = 2 ∧ 8 ≤ n) ∨ (p ^ f = 3 ∧ 6 ≤ n)) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSU n p f × exceptional .PSU n p f) := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
  have hn4 : 4 ≤ n := by
    obtain ⟨r, hr⟩ := he
    omega
  have hM : commutator (StatedProj (StatedSU n (p ^ f) K)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSU n (p ^ f) K)) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f + 1)))) := by
    rcases hq with h4 | ⟨h2, hn8⟩ | ⟨h3, hn6⟩
    · exact SUClosed.psu_hopfMultiplier hK he hn4 h4
    · obtain ⟨rfl, rfl⟩ := GriessExceptionalPow.eq_two_one_of_pow_eq_two hp (by omega) h2
      obtain ⟨r, rfl⟩ := he
      rw [← two_mul]
      exact SUClosed.psu_two_hopfMultiplier hK (by omega)
    · obtain ⟨rfl, rfl⟩ := GriessExceptionalPow.eq_three_one_of_pow_eq_three hp (by omega) h3
      exact SUClosed.psu_three_hopfMultiplier hK he hn6
  refine of_mulEquiv e (of_mulEquiv_target ?_ hM)
  refine (padOne _).trans (toGenEx (t := .PSU) (n := n) (p := p) (f := f)
    (a₁ := Nat.gcd n (p ^ f + 1)) (a₂ := 1) (b₁ := 1) (b₂ := 1) (by simp [genericOrders]) ?_)
  have h1 : ¬(n = 4 ∧ p = 2 ∧ f = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    rcases hq with h | ⟨-, h⟩ | ⟨-, h⟩ <;> norm_num at h
  have h2 : ¬(n = 6 ∧ p = 2 ∧ f = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    rcases hq with h | ⟨-, h⟩ | ⟨h, -⟩ <;> norm_num at h
  have h3 : ¬(n = 4 ∧ p = 3 ∧ f = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    rcases hq with h | ⟨h, -⟩ | ⟨-, h⟩ <;> norm_num at h
  unfold exceptionalOrders
  split <;> simp_all

theorem psp_row
    (h : StatedClassicalModel X .PSp n p f)
    (hq : 5 ≤ p ^ f ∨ p ^ f = 4 ∨ (p ^ f = 2 ∧ 4 ≤ n) ∨ (p ^ f = 3 ∧ 3 ≤ n)) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSp n p f × exceptional .PSp n p f) := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hM : commutator (StatedProj (StatedSp n K)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp n K)) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
    rcases hq with h5 | h4 | ⟨h2, hn4⟩ | ⟨h3, hn3⟩
    · exact SpClosed.psp_hopfMultiplier hn (by omega)
    · obtain ⟨rfl, rfl⟩ := GriessExceptionalPow.eq_two_two_of_pow_eq_four hp (by omega) h4
      have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (by norm_num) hK
      exact SpClosed.psp_even_hopfMultiplier hK hf hn (fun _ => le_rfl)
    · obtain ⟨rfl, rfl⟩ := GriessExceptionalPow.eq_two_one_of_pow_eq_two hp (by omega) h2
      have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (by norm_num) hK
      exact SpClosed.psp_even_hopfMultiplier hK hf hn (fun h3 => by omega)
    · exact SpThree.psp_three_hopfMultiplier hn3 (hK.trans h3)
  refine of_mulEquiv e (of_mulEquiv_target ?_ hM)
  refine (padOne _).trans (toGenEx (t := .PSp) (n := n) (p := p) (f := f)
    (a₁ := Nat.gcd 2 (Nat.card K - 1)) (a₂ := 1) (b₁ := 1) (b₂ := 1)
    (by rw [hK]; simp [genericOrders]) ?_)
  have h31 : ¬(n = 3 ∧ p = 2 ∧ f = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    rcases hq with h | h | ⟨-, h⟩ | ⟨h, -⟩ <;> norm_num at h
  unfold exceptionalOrders
  split <;> simp_all

theorem pomegaOdd_row (h : StatedClassicalModel X .POmegaOdd n p f)
    (hq : 5 ≤ p ^ f ∨ (p ^ f = 3 ∧ 4 ≤ n)) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .POmegaOdd n p f × exceptional .POmegaOdd n p f) := by
  obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have h2 : (2 : K) ≠ 0 := fun h0 => by
    have hev := (SpinTorus.two_eq_zero_iff_even_card).1 h0
    rw [hK] at hev
    exact Nat.not_even_iff_odd.2 (Odd.pow (hp.odd_of_ne_two hp2)) hev
  have hM : commutator (StatedProj (StatedOmega (StatedQuadOdd n K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadOdd n K))) ≃*
        Multiplicative (ZMod 2)) := by
    rcases hq with h5 | ⟨h3, hn4⟩
    · exact SpinOddClosed.pomegaOdd_hopfMultiplier h2 hn (by omega)
    · exact SpinOddClosed.pomegaOdd_three_hopfMultiplier (hK.trans h3) hn4
  refine of_mulEquiv e (of_mulEquiv_target ?_ hM)
  refine (padOne _).trans (toGenEx (t := .POmegaOdd) (n := n) (p := p) (f := f)
    (a₁ := 2) (a₂ := 1) (b₁ := 1) (b₂ := 1) (by simp [genericOrders]) ?_)
  have h31 : ¬(n = 3 ∧ p = 3 ∧ f = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    rcases hq with h | ⟨-, h⟩ <;> norm_num at h
  unfold exceptionalOrders
  split <;> simp_all

theorem pomegaPlus_row
    (h : StatedClassicalModel X .POmegaPlus n p f)
    (hq : 3 ≤ p ^ f ∨ (p ^ f = 2 ∧ 5 ≤ n)) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .POmegaPlus n p f × exceptional .POmegaPlus n p f) := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hM : commutator (StatedProj (StatedOmega (StatedQuadPlus n K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadPlus n K))) ≃*
        generic .POmegaPlus n p f) := by
    rcases hq with h3 | ⟨h2, hn5⟩
    · rcases eq_or_lt_of_le h3 with h3 | h4
      · exact SpinPlusClosed.pomegaPlus_three_hopfMultiplier hn hK (hK.trans h3.symm)
      · exact SpinPlusClosed.pomegaPlus_hopfMultiplier (by omega) hK (by omega)
    · exact OrthogonalTwo.pomegaPlus_two_hopfMultiplier hn5 hK (hK.trans h2)
  refine of_mulEquiv e (of_mulEquiv_target ?_ hM)
  have h41 : ¬(n = 4 ∧ p = 2 ∧ f = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    rcases hq with h | ⟨-, h⟩ <;> norm_num at h
  have he : exceptionalOrders .POmegaPlus n p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
  exact MulEquiv.prodUnique.symm.trans (toGenEx (t := .POmegaPlus) (n := n) (p := p) (f := f)
    (a₁ := (genericOrders .POmegaPlus n p f).1) (a₂ := (genericOrders .POmegaPlus n p f).2)
    (b₁ := 1) (b₂ := 1) (Prod.mk.eta).symm he)

theorem pomegaMinus_row
    (h : StatedClassicalModel X .POmegaMinus n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .POmegaMinus n p f × exceptional .POmegaMinus n p f) := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  have hM : commutator (StatedProj (StatedOmega (StatedQuadMinus n K b c))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃*
          Multiplicative (ZMod (Nat.gcd 4 ((p ^ f) ^ n + 1)))) := by
    have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    rcases (show 4 ≤ p ^ f ∨ p ^ f = 2 ∨ p ^ f = 3 by omega) with h4 | h2 | h3
    · exact SpinMinusClosed.pomegaMinus_hopfMultiplier hn hirr hK (by omega)
    · exact OrthogonalTwo.pomegaMinus_two_hopfMultiplier hn hirr hK (hK.trans h2)
    · exact SpinMinusClosed.pomegaMinus_three_hopfMultiplier' hn hirr hK (hK.trans h3)
  refine of_mulEquiv e (of_mulEquiv_target ?_ hM)
  refine (padOne _).trans (toGenEx (t := .POmegaMinus) (n := n) (p := p) (f := f)
    (a₁ := Nat.gcd 4 ((p ^ f) ^ n + 1)) (a₂ := 1) (b₁ := 1) (b₂ := 1)
    (by simp [genericOrders]) ?_)
  unfold exceptionalOrders
  split <;> simp_all

theorem griess_classical_of_large
    (t : StatedLieTag)
    (hmodel : CFSG.Models.LieModel X t n p f)
    (ht : t = .PSL ∨
      (t = .PSU ∧ Even n ∧ (4 ≤ p ^ f ∨ (p ^ f = 2 ∧ 8 ≤ n) ∨ (p ^ f = 3 ∧ 6 ≤ n))) ∨
      (t = .PSp ∧ (5 ≤ p ^ f ∨ p ^ f = 4 ∨ (p ^ f = 2 ∧ 4 ≤ n) ∨ (p ^ f = 3 ∧ 3 ≤ n))) ∨
      (t = .POmegaOdd ∧ (5 ≤ p ^ f ∨ (p ^ f = 3 ∧ 4 ≤ n))) ∨
      (t = .POmegaPlus ∧ (3 ≤ p ^ f ∨ (p ^ f = 2 ∧ 5 ≤ n))) ∨
      t = .POmegaMinus) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f) := by
  obtain ⟨-, hcl | ⟨-, d, hd, -⟩⟩ := hmodel
  · rcases ht with rfl | ⟨rfl, he, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | rfl
    · exact psl_row hcl
    · exact psu_row hcl he hq
    · exact psp_row hcl hq
    · exact pomegaOdd_row hcl hq
    · exact pomegaPlus_row hcl hq
    · exact pomegaMinus_row hcl
  · exfalso
    rcases ht with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | rfl <;>
      cases h : d.1 <;> rw [h] at hd <;> simp [CFSG.Models.NamesTag] at hd

end CFSG.LieType.Steinberg.CentralExt.GriessClassical
