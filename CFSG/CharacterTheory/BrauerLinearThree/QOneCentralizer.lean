module

public import CFSG.CharacterTheory.BrauerLinearThree.QOneLemmaOne
public import CFSG.CharacterTheory.BrauerLinearThree.SixBChar
public import CFSG.CharacterTheory.BrauerLinearThree.SixBLocal

public section

namespace CFSG.BrauerLinearThree.QOne

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers

theorem dvd_of_dvd_two_mul {N M : ℕ} (h1 : N ∣ 2 * M) (h2 : 2 ^ N.factorization 2 ∣ M) :
    N ∣ M := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [zero_dvd_iff] at h1 ⊢
    omega
  have hcop := Nat.coprime_ordCompl Nat.prime_two hN.ne'
  have hodd : N / 2 ^ N.factorization 2 ∣ M :=
    hcop.symm.dvd_of_dvd_mul_left ((Nat.div_dvd_of_dvd (Nat.ordProj_dvd N 2)).trans h1)
  rw [← Nat.ordProj_mul_ordCompl_eq_self N 2]
  exact (Nat.Coprime.pow_left _ hcop).mul_dvd_of_dvd_of_dvd h2 hodd

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 in
theorem two_part_card_centralizer [Finite G]
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) (hJ : orderOf J = 2)
    {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1) :
    2 ^ (Nat.card (Subgroup.centralizer ({Q} : Set G))).factorization 2 ∣ Nat.card F - 1 ∧
      (2 ∣ Nat.card (Subgroup.centralizer ({Q} : Set G)) →
        ∃ g : G, g * Q * g⁻¹ ∈ rootX₁ φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({Q} : Set G) with hCdef
  by_cases h2c : 2 ∣ Nat.card C
  swap
  · rw [Nat.factorization_eq_zero_of_not_dvd h2c, pow_zero]
    exact ⟨one_dvd _, fun h => absurd h h2c⟩
  obtain ⟨T₂⟩ : Nonempty (Sylow 2 C) := inferInstance
  set T : Subgroup G := (T₂ : Subgroup C).map C.subtype with hTdef
  have hTcard : Nat.card T = 2 ^ (Nat.card C).factorization 2 := by
    rw [hTdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective C),
      Sylow.card_eq_multiplicity]
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hTp : IsPGroup 2 T := T₂.isPGroup'.map _
  have hT1 : 1 < Nat.card T := by
    rw [hTcard]
    exact Nat.one_lt_pow (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne'
      h2c).ne' (by norm_num)
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hT1
  obtain ⟨t, ht⟩ : ∃ t : Subgroup.center T, orderOf t = 2 := by
    have hZT := hTp.center_nontrivial
    rcases (hTp.to_subgroup (Subgroup.center T)).card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZT).ne'
    · exact exists_prime_orderOf_dvd_card' 2 h
  set Jst : G := ((t : T) : G) with hJstdef
  have hJst2 : orderOf Jst = 2 := by rw [hJstdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have hJstT : Jst ∈ T := (t : T).2
  have hJstc : ∀ y ∈ T, y * Jst = Jst * y := by
    intro y hy
    have := Subgroup.mem_center_iff.mp t.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  obtain ⟨c, hc⟩ := isConj_iff.mp (hinv Jst J hJst2 hJ)
  set Q' := c * Q * c⁻¹ with hQ'def
  have hJQ' : J * Q' = Q' * J := by
    have hJstQ : Jst * Q = Q * Jst := Subgroup.mem_centralizer_singleton_iff.mp (hTC hJstT)
    rw [← hc, hQ'def]
    calc c * Jst * c⁻¹ * (c * Q * c⁻¹) = c * (Jst * Q) * c⁻¹ := by group
      _ = c * (Q * Jst) * c⁻¹ := by rw [hJstQ]
      _ = c * Q * c⁻¹ * (c * Jst * c⁻¹) := by group
  have hQ'p : Q' ^ ringChar F = 1 := by
    rw [hQ'def, show c * Q * c⁻¹ = MulAut.conj c Q from rfl, ← map_pow, hQp, map_one]
  obtain ⟨h, hhJ, hhQ⟩ := exists_conj_mem_rootX₁ φ hZ h2 hJQ' hQ'p
  refine ⟨?_, fun _ => ⟨h * c, by
    rw [show h * c * Q * (h * c)⁻¹ = h * Q' * h⁻¹ by rw [hQ'def]; group]
    exact hhQ⟩⟩
  obtain ⟨b₀, hb₀⟩ := (mem_rootX₁ φ).mp hhQ
  have hb₀0 : b₀ ≠ 0 := by
    rintro rfl
    apply hQ1
    have h1 : h * Q' * h⁻¹ = 1 := by rw [← hb₀, rootUp, upperGL_zero, map_one]
    have h2' : Q' = 1 := by
      calc Q' = h⁻¹ * (h * Q' * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    calc Q = c⁻¹ * Q' * c := by rw [hQ'def]; group
      _ = 1 := by rw [h2']; group
  have hle : T.map (conjHom (h * c)) ≤ centerSub φ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [conjHom_apply]
    apply mem_centerSub_of_commute_rootUp φ hZ hZodd h2 hb₀0 (k := (Nat.card C).factorization 2)
    ·
      have hyJst := hJstc y hy
      rw [← hc]
      calc c * Jst * c⁻¹ * (h * c * y * (h * c)⁻¹) =
            h * (h⁻¹ * (c * Jst * c⁻¹) * h) * (c * y * c⁻¹) * h⁻¹ := by group
        _ = h * (c * Jst * c⁻¹) * (c * y * c⁻¹) * h⁻¹ := by
          rw [show h⁻¹ * (c * Jst * c⁻¹) * h = c * Jst * c⁻¹ by
            rw [hc]; calc h⁻¹ * J * h = h⁻¹ * (J * h) := by group
              _ = h⁻¹ * (h * J) := by rw [hhJ]
              _ = J := by group]
        _ = h * (c * (Jst * y) * c⁻¹) * h⁻¹ := by group
        _ = h * (c * (y * Jst) * c⁻¹) * h⁻¹ := by rw [hyJst]
        _ = h * c * y * (h * c)⁻¹ * (h * (c * Jst * c⁻¹) * h⁻¹) := by group
        _ = h * c * y * (h * c)⁻¹ * (c * Jst * c⁻¹) := by
          rw [hc, show h * J * h⁻¹ = J by rw [← hhJ]; group]
    ·
      have hyQ : y * Q = Q * y := Subgroup.mem_centralizer_singleton_iff.mp (hTC hy)
      rw [hb₀, hQ'def]
      calc h * c * y * (h * c)⁻¹ * (h * (c * Q * c⁻¹) * h⁻¹) = h * c * (y * Q) * (h * c)⁻¹ := by
            group
        _ = h * c * (Q * y) * (h * c)⁻¹ := by rw [hyQ]
        _ = h * (c * Q * c⁻¹) * h⁻¹ * (h * c * y * (h * c)⁻¹) := by group
    ·
      have hyT : (⟨y, hy⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
      have hy1 : y ^ 2 ^ (Nat.card C).factorization 2 = 1 := by
        rw [← hTcard]
        exact congrArg Subtype.val hyT
      rw [show h * c * y * (h * c)⁻¹ = MulAut.conj (h * c) y from rfl, ← map_pow, hy1, map_one]
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [card_map_conjHom, hTcard] at hdvd
  have hU : Nat.card (centerSub φ) * Nat.card Z = Nat.card F - 1 := card_scalarImage φ hZ
  exact hdvd.trans (Dvd.intro _ hU)

variable [Fintype G] (basis : FiniteIrreducibleCharacterBasis G) {χ₄ : basis.index}
  (hχ₄ : (basis.representation χ₄).character 1 = (Nat.card F : ℂ) ^ 3 - 1)

include hχ₄ in
theorem cube_sub_one_dvd_index_centralizer {Q : G}
    (hQ4 : (basis.representation χ₄).character Q = -1) :
    Nat.card F ^ 3 - 1 ∣ (Subgroup.centralizer ({Q} : Set G)).index := by
  have h3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ Nat.card_pos
  have hdeg : Module.finrank ℂ (basis.representation χ₄).vector = Nat.card F ^ 3 - 1 :=
    finrank_eq_of_character_one basis χ₄ (by rw [hχ₄]; push_cast [Nat.cast_sub h3]; ring)
  have h := card_centralizer_mul_dvd_of_character_eq_neg_one basis χ₄ Q hQ4
  rw [hdeg] at h
  have h' : (Nat.card F ^ 3 - 1) * Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣
      (Subgroup.centralizer ({Q} : Set G)).index *
        Nat.card (Subgroup.centralizer ({Q} : Set G)) := by
    rw [Subgroup.index_mul_card, mul_comm]
    exact h
  exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h'

include hχ₄ in
theorem cube_sub_one_mul_card_centralizer_dvd {Q : G}
    (hQ4 : (basis.representation χ₄).character Q = -1) :
    (Nat.card F ^ 3 - 1) * Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card G := by
  rw [← Subgroup.index_mul_card (Subgroup.centralizer ({Q} : Set G))]
  exact Nat.mul_dvd_mul_right (cube_sub_one_dvd_index_centralizer basis hχ₄ hQ4) _

include φ hZ hZodd h2 hχ₄ in
theorem card_centralizer_mul_card_Z_dvd (hq : Nat.card F % 4 = 1)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) (hJ : orderOf J = 2)
    (hL1 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card F + 1 → ∀ g : G, orderOf g ≠ p * ringChar F)
    {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1)
    (hQ4 : (basis.representation χ₄).character Q = -1) :
    Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
      Nat.card F ^ 3 * (Nat.card F - 1) := by
  set C := Subgroup.centralizer ({Q} : Set G) with hCdef
  set q := Nat.card F with hqdef
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hp₀ : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp₀⟩
  have hQord : orderOf Q = ringChar F := orderOf_eq_prime hQp hQ1
  have h1 : Nat.card C * Nat.card Z ∣ q ^ 3 * (q ^ 2 - 1) := by
    obtain ⟨m, hm⟩ := cube_sub_one_mul_card_centralizer_dvd basis hχ₄ hQ4
    refine ⟨m, ?_⟩
    have hpos : 0 < q ^ 3 - 1 := by
      have : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
      omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc (q ^ 3 - 1) * (q ^ 3 * (q ^ 2 - 1)) = Nat.card G * Nat.card Z := by rw [hcard]; ring
      _ = (q ^ 3 - 1) * (Nat.card C * Nat.card Z * m) := by rw [hm]; ring
  obtain ⟨v, hv, hvodd⟩ : ∃ v, q + 1 = 2 * v ∧ Odd v :=
    ⟨(q + 1) / 2, by omega, by rw [Nat.odd_iff]; omega⟩
  have hcop : Nat.Coprime (Nat.card C * Nat.card Z) v := by
    apply Nat.coprime_of_dvd
    intro k hk hkN hkv
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hvodd) (even_iff_two_dvd.mpr hkv)
    have hkq : k ∣ q + 1 := hkv.trans ⟨2, by omega⟩
    rcases (Nat.Prime.dvd_mul hk).mp hkN with hkC | hkZ
    ·
      have : Fact k.Prime := ⟨hk⟩
      obtain ⟨P, hP⟩ := exists_prime_orderOf_dvd_card' k hkC
      have hPQ : Commute (P : G) Q := Subgroup.mem_centralizer_singleton_iff.mp P.2
      have hkp₀ : k ≠ ringChar F := by
        rintro rfl
        have hpq : ringChar F ∣ q := by
          obtain ⟨f, hf, hqf⟩ := exists_card_eq_ringChar_pow F
          rw [hqdef, hqf]
          exact dvd_pow_self _ hf.ne'
        have : ringChar F ∣ q + 1 - q := Nat.dvd_sub hkq hpq
        rw [Nat.add_sub_cancel_left] at this
        exact hp₀.one_lt.ne' (Nat.dvd_one.mp this)
      apply hL1 k hk hk2 hkq ((P : G) * Q)
      rw [hPQ.orderOf_mul_eq_mul_orderOf_of_coprime (by
        rw [Subgroup.orderOf_coe, hP, hQord]
        exact (Nat.coprime_primes hk hp₀).mpr hkp₀), Subgroup.orderOf_coe, hP, hQord]
    ·
      have hkq' : k ∣ q - 1 := hkZ.trans (card_Z_dvd hZ)
      have : k ∣ q + 1 - (q - 1) := Nat.dvd_sub hkq hkq'
      rw [show q + 1 - (q - 1) = 2 by omega] at this
      exact hk2 ((Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).mp this)
  have h2M : Nat.card C * Nat.card Z ∣ 2 * (q ^ 3 * (q - 1)) := by
    have e : q ^ 3 * (q ^ 2 - 1) = 2 * (q ^ 3 * (q - 1)) * v := by
      have h1' : 1 ≤ q := by omega
      have h2' : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1', h2'] at hv ⊢
      rw [show (q : ℤ) ^ 2 - 1 = ((q : ℤ) - 1) * ((q : ℤ) + 1) by ring, hv]
      ring
    rw [e] at h1
    exact hcop.dvd_of_dvd_mul_right h1
  have hZ2 : (Nat.card Z).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hZodd)
      (even_iff_two_dvd.mpr h))
  apply dvd_of_dvd_two_mul h2M
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hZ2, add_zero]
  exact ((two_part_card_centralizer φ hZ hZodd h2 hinv hJ hQ1 hQp).1).trans
    (dvd_mul_left _ _)

end CFSG.BrauerLinearThree.QOne
