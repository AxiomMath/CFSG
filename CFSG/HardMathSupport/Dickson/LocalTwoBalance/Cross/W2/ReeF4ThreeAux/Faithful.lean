module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux.SU3
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux.Centralizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

section Arith

theorem odd_ree_cofactor (b : ℕ) :
    Odd ((2 ^ (2 * b + 1) - 1) ^ 2 * (2 ^ (2 * b + 1) + 1) ^ 2 *
      ((2 ^ (2 * b + 1)) ^ 2 + 1) ^ 2 * ((2 ^ (2 * b + 1)) ^ 2 - 2 ^ (2 * b + 1) + 1) *
      ((2 ^ (2 * b + 1)) ^ 4 - (2 ^ (2 * b + 1)) ^ 2 + 1)) := by
  have hQe : Even (2 ^ (2 * b + 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hQ2 : 2 ≤ 2 ^ (2 * b + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * b + 1) = Q at hQe hQ2 ⊢
  have hQ2e : Even (Q ^ 2) := Nat.even_pow.2 ⟨hQe, by norm_num⟩
  have hQ4e : Even (Q ^ 4) := Nat.even_pow.2 ⟨hQe, by norm_num⟩
  have h1 : Q ≤ Q ^ 2 := by nlinarith
  have h2 : Q ^ 2 ≤ Q ^ 4 := by nlinarith
  refine Odd.mul (Odd.mul (Odd.mul (Odd.mul ?_ ?_) ?_) ?_) ?_
  · exact Odd.pow (Nat.Even.sub_odd (by omega) hQe odd_one)
  · exact Odd.pow hQe.add_one
  · exact Odd.pow hQ2e.add_one
  · exact ((Nat.even_sub h1).2 (iff_of_true hQ2e hQe)).add_one
  · exact ((Nat.even_sub h2).2 (iff_of_true hQ4e hQ2e)).add_one

theorem le_of_two_pow_dvd_card_reeGamma
    {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) {n : ℕ}
    (h : 2 ^ n ∣ Nat.card (ReeTag.F4.reeGamma k b)) : n ≤ 12 * (2 * b + 1) := by
  rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion b k
    hk).1] at h
  simp only [mul_assoc] at h
  have hcop : Nat.Coprime (2 ^ n) ((2 ^ (2 * b + 1) - 1) ^ 2 * ((2 ^ (2 * b + 1) + 1) ^ 2 *
      (((2 ^ (2 * b + 1)) ^ 2 + 1) ^ 2 * (((2 ^ (2 * b + 1)) ^ 2 - 2 ^ (2 * b + 1) + 1) *
        ((2 ^ (2 * b + 1)) ^ 4 - (2 ^ (2 * b + 1)) ^ 2 + 1))))) := by
    refine Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 ?_)
    simpa only [mul_assoc] using odd_ree_cofactor b
  have h2 : 2 ^ n ∣ ((2 ^ (2 * b + 1)) ^ 12) := hcop.dvd_of_dvd_mul_right h
  rw [← pow_mul] at h2
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2 |>.trans (by omega)

end Arith

section Faithful


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem card_galoisField_su3 (a : ℕ) :
    Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
  rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]

theorem pow_three_eq_one_of_conj_fixes (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ReeTag.F4.reeGamma K a} (hy : orderOf y = 3) {x : ReeTag.F4.reeGamma K a}
    (hx : ∀ t ∈ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)), x * t * x⁻¹ = t) :
    x ^ 3 = 1 := by
  have hcomm : ∀ t ∈ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)),
      t * x = x * t := fun t ht => by
    have h := hx t ht
    calc t * x = x * t * x⁻¹ * x := by rw [h]
      _ = x * t := by group
  have hxC : x ∈ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) :=
    Subgroup.mem_centralizer_singleton_iff.2
      (hcomm y (Subgroup.mem_centralizer_singleton_iff.2 rfl)).symm
  have hξ : (⟨x, hxC⟩ : Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) ∈
      Subgroup.center (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hcomm s s.2)
  obtain ⟨e⟩ := reeGamma_centralizer_su3 hK hy
  have h3 := pow_three_eq_one_of_mem_center_su3 (f := 2 * a + 1)
    (K := GaloisField 2 (2 * (2 * a + 1))) (by omega) (card_galoisField_su3 a)
    ((MulEquivClass.apply_mem_center_iff e).2 hξ)
  have h4 : (⟨x, hxC⟩ : Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, h3, map_one]
  exact congrArg Subtype.val h4

theorem false_of_outer_prime_fix (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ReeTag.F4.reeGamma K a} (hy : orderOf y = 3) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    {h : MulAut (ReeTag.F4.reeGamma K a)} (hhr : h ^ r = 1)
    (hho : h ∉ innerAut (ReeTag.F4.reeGamma K a))
    (hfix : ∀ t ∈ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)), h t = t) :
    False := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hNFex, hNFuniq⟩ := reeGamma_normalForm ha hK
  obtain ⟨-, hone, hpow, -⟩ := reeGammaFieldAut_hom_facts (K := K) (a := a)
  obtain ⟨u, β, rfl⟩ := hNFex h
  have hβr : β ^ r = 1 := by
    obtain ⟨z, hz⟩ : ∃ z, (MulAut.conj u * F4.reeGammaFieldAut K a β) ^ r =
        MulAut.conj z * F4.reeGammaFieldAut K a β ^ r :=
      ⟨_, CFSG.RankThree.PartOne.KE.conj_mul_pow_aut u (F4.reeGammaFieldAut K a β) r⟩
    have h' : MulAut.conj 1 * F4.reeGammaFieldAut K a 1 =
        MulAut.conj z * F4.reeGammaFieldAut K a (β ^ r) := by
      rw [map_one, hone, one_mul, hpow, ← hz, hhr]
    exact (hNFuniq _ _ _ _ h').2.symm
  have hβ1 : β ≠ 1 := by
    rintro rfl
    exact hho ⟨u, by rw [hone, mul_one]⟩
  have hβ : orderOf β = r := orderOf_eq_prime hβr hβ1
  obtain ⟨σ₁, -, -, -, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) Nat.prime_two (by omega) hK
  have hrf : r ∣ 2 * a + 1 := by
    rw [← hβ, ← hcardAut]
    exact orderOf_dvd_natCard β
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have hr5 : 5 ≤ r := by
    have h2 := hr.two_le
    by_contra hlt
    have : r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases this with h | h | h
    · exact hr2 h
    · exact hr3 h
    · rw [h] at hr
      norm_num at hr
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hr β hβ _ hhr
    ⟨u, rfl⟩
  obtain ⟨b, hk, ψ, hbr, hψinj, hψfix, -⟩ := exists_reeGamma_fixSubfield_hom hK hr hr2 β hβ
  have hle : (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))).map
      ((MulAut.conj g)⁻¹).toMonoidHom ≤ ψ.range := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hfix t ht
    rw [hg] at h1
    have h2 : F4.reeGammaFieldAut K a β ((MulAut.conj g)⁻¹ t) = (MulAut.conj g)⁻¹ t := by
      apply (MulAut.conj g).injective
      have h1' : (MulAut.conj g) (F4.reeGammaFieldAut K a β ((MulAut.conj g)⁻¹ t)) = t := h1
      rw [h1', MulAut.apply_inv_self]
    exact (hψfix _).1 h2
  have hTcard : Nat.card (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) ∣
      Nat.card ψ.range := by
    have h1 : Nat.card ((Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))).map
        ((MulAut.conj g)⁻¹).toMonoidHom) =
        Nat.card (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) :=
      Subgroup.card_map_of_injective ((MulAut.conj g)⁻¹).injective
    rw [← h1]
    exact Subgroup.card_dvd_of_le hle
  have hψcard : Nat.card ψ.range = Nat.card (F4.reeGamma (fixSubfield β) b) :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  obtain ⟨e⟩ := reeGamma_centralizer_su3 hK hy
  have hTSU : Nat.card (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) =
      Nat.card (unitarySU 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3) :=
    Nat.card_congr e.toEquiv
  have h2pow := two_pow_dvd_card_su3 (f := 2 * a + 1) (K := GaloisField 2 (2 * (2 * a + 1)))
    (by omega) (card_galoisField_su3 a)
  have hdvd : 2 ^ (3 * (2 * a + 1)) ∣ Nat.card (F4.reeGamma (fixSubfield β) b) := by
    rw [← hψcard]
    exact h2pow.trans (hTSU ▸ hTcard)
  have hle12 := le_of_two_pow_dvd_card_reeGamma hk hdvd
  have h5 := Nat.mul_le_mul_left (2 * b + 1) hr5
  omega

theorem eq_one_of_fix_centralizer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ReeTag.F4.reeGamma K a} (hy : orderOf y = 3) (g : MulAut (ReeTag.F4.reeGamma K a))
    (hg : Nat.Coprime 3 (orderOf g))
    (hfix : ∀ t ∈ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)), g t = t) :
    g = 1 := by
  by_contra hg1
  have hn1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  have hnpos : 0 < orderOf g := orderOf_pos g
  have hr : (orderOf g).minFac.Prime := Nat.minFac_prime hn1
  have hrn : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
  set r := (orderOf g).minFac with hrdef
  have hr3 : r ≠ 3 := by
    intro h3
    rw [h3] at hrn
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 3) hrn) hg
  set h := g ^ (orderOf g / r) with hhdef
  have hho : orderOf h = r := orderOf_pow_orderOf_div hnpos.ne' hrn
  have hhr : h ^ r = 1 := by
    rw [← hho]
    exact pow_orderOf_eq_one h
  have hhfix : ∀ t ∈ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)), h t = t := by
    intro t ht
    have key : ∀ k : ℕ, (g ^ k) t = t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix t ht, ih]
    exact key _
  by_cases hin : h ∈ innerAut (ReeTag.F4.reeGamma K a)
  · obtain ⟨x, hx⟩ := hin
    have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_conj_fixes ha hK hy fun t ht => by
      have h1 := hhfix t ht
      rw [← hx] at h1
      simpa [MulAut.conj_apply] using h1
    have h3 : h ^ 3 = 1 := by
      rw [← hx, ← map_pow, hx3, map_one]
    have hr3' : r ∣ 3 := by
      rw [← hho]
      exact orderOf_dvd_of_pow_eq_one h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3')
  · exact false_of_outer_prime_fix ha hK hy hr hr3 hhr hin hhfix

end Faithful

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux
