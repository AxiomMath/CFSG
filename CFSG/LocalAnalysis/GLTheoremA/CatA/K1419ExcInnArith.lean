module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcArith
public import CFSG.Goldschmidt.Steps.G37Quot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

section Residual


@[expose] def InnerBigNonA (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .inner →
      14 ≤ (componentRoots (rootCharHom a) i).ncard →
      ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) + 1)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      27 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

end Residual

theorem l3u3_inn_card_centerQuotient_mul {C R : Type*} [Group C] [Group R]
    (hC : Group.IsPerfect C) (f : C →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center C) :
    Nat.card (R ⧸ Subgroup.center R) * Nat.card (Subgroup.center C) = Nat.card C := by
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hC f hf hker
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center C),
    Nat.card_congr e.toEquiv]

theorem l3u3_inn_two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b ∧ u = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u ≠ 0 := hu.pos.ne'
  have hw0 : w ≠ 0 := hw.pos.ne'
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hu0,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) hw0, padicValNat.prime_pow,
    padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hu)),
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hw))] at hv
  have hab : a = b := by omega
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) a) h⟩

theorem l3u3_inn_odd_sub_one_of_even {x : ℕ} (hx : Even x) (h0 : 0 < x) : Odd (x - 1) := by
  rcases hx with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

theorem l3u3_inn_odd_pow_two_sq_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd ((2 ^ m) ^ 2 - 1) := by
  refine l3u3_inn_odd_sub_one_of_even ?_ (by positivity)
  exact Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩

theorem l3u3_inn_not_three_dvd_of_card_eq {N m T Z S : ℕ} (hN : L3U3Order N) (hT : Odd T)
    (hS : Odd S) (hZ : Z ∣ T) (h : N * Z = T * (2 ^ m) ^ 3 * S) : ¬ 3 ∣ m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn3, hn1, hv⟩ := hN.padicValNat_two
  have hZodd : Odd Z := hT.of_dvd_nat hZ
  have h1 := congrArg (padicValNat 2) h
  have h2pow : ((2 : ℕ) ^ m) ^ 3 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  rw [padicValNat.mul hN.ne_zero hZodd.pos.ne',
    padicValNat.mul (mul_ne_zero hT.pos.ne' h2pow) hS.pos.ne',
    padicValNat.mul hT.pos.ne' h2pow,
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hZodd)),
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hT)),
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hS)),
    padicValNat.pow, padicValNat.prime_pow, hv] at h1
  intro h3
  apply hn3
  omega

theorem l3u3_inn_three_mul_ne_sl2_minus {X : ℕ} (hX : 2 ≤ X) :
    3 * (X ^ 6 - 1) ≠ (X ^ 2 - 1) * (X ^ 3 - 1) := by
  intro h
  have h2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h3, h6] at h
  have hx : (2 : ℤ) ≤ X := by exact_mod_cast hX
  have h5 : (32 : ℤ) ≤ (X : ℤ) ^ 5 := by
    calc (32 : ℤ) = 2 ^ 5 := by norm_num
      _ ≤ (X : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
  nlinarith [mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℤ) ≤ (X : ℤ) ^ 5)]

theorem l3u3_inn_three_mul_ne_sl2_plus {X : ℕ} (hX : 2 ≤ X) :
    3 * (X ^ 6 - 1) ≠ (X ^ 2 - 1) * (X ^ 3 + 1) := by
  intro h
  have h2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h6] at h
  have hx : (2 : ℤ) ≤ X := by exact_mod_cast hX
  have h5 : (32 : ℤ) ≤ (X : ℤ) ^ 5 := by
    calc (32 : ℤ) = 2 ^ 5 := by norm_num
      _ ≤ (X : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
  have h3 : (8 : ℤ) ≤ (X : ℤ) ^ 3 := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ (X : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
  have h2' : (X : ℤ) ^ 2 ≤ (X : ℤ) ^ 3 := pow_le_pow_right₀ (by omega) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℤ) ≤ (X : ℤ) ^ 5)]

theorem l3u3_inn_not_order_sl2 {m : ℕ} (hm : 1 ≤ m) :
    ¬ L3U3Order (2 ^ m * ((2 ^ m) ^ 2 - 1)) := by
  rintro ⟨n, ⟨hn6, hN⟩ | ⟨hn6, hn1, hN⟩⟩
  · have hn : n ≠ 0 := by omega
    have hodd1 : Odd (3 * ((2 ^ m) ^ 2 - 1)) :=
      (by decide : Odd 3).mul (l3u3_inn_odd_pow_two_sq_sub_one hm)
    have hodd2 : Odd ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) := by
      rw [two_pow_two_mul, two_pow_three_mul]
      exact (odd_four_pow_sub_one hn).mul (odd_eight_pow_sub_one hn)
    have hN' : 2 ^ m * (3 * ((2 ^ m) ^ 2 - 1)) =
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) := by rw [← hN]; ring
    obtain ⟨hm3, hEq⟩ := l3u3_inn_two_pow_mul_odd_inj hodd1 hodd2 hN'
    subst hm3
    have hX : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    have e3 : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
    have e6 : ((2 : ℕ) ^ (3 * n)) ^ 2 = (2 ^ n) ^ 6 := by rw [e3, ← pow_mul]
    rw [e6, e2, e3] at hEq
    exact l3u3_inn_three_mul_ne_sl2_minus hX hEq
  · have hn : n ≠ 0 := by omega
    have hodd1 : Odd (3 * ((2 ^ m) ^ 2 - 1)) :=
      (by decide : Odd 3).mul (l3u3_inn_odd_pow_two_sq_sub_one hm)
    have hodd2 : Odd ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by
      rw [two_pow_two_mul, two_pow_three_mul]
      exact (odd_four_pow_sub_one hn).mul (odd_eight_pow_add_one hn)
    have hN' : 2 ^ m * (3 * ((2 ^ m) ^ 2 - 1)) =
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by rw [← hN]; ring
    obtain ⟨hm3, hEq⟩ := l3u3_inn_two_pow_mul_odd_inj hodd1 hodd2 hN'
    subst hm3
    have hX : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    have e3 : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
    have e6 : ((2 : ℕ) ^ (3 * n)) ^ 2 = (2 ^ n) ^ 6 := by rw [e3, ← pow_mul]
    rw [e6, e2, e3] at hEq
    exact l3u3_inn_three_mul_ne_sl2_plus hX hEq

theorem l3u3_inn_sub_one_dvd_pow_sub_one (Q k : ℕ) : Q - 1 ∣ Q ^ k - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow Q 1 k

theorem l3u3_inn_three_dvd_of_mod_three_eq_one {y : ℕ} (hy : y % 3 = 1) :
    3 ∣ y - 1 ∧ 3 ∣ y ^ 2 - 1 ∧ 9 ∣ y ^ 3 - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, y = 3 * t + 1 := ⟨y / 3, by omega⟩
  refine ⟨⟨t, by omega⟩, ⟨3 * t ^ 2 + 2 * t, ?_⟩, ⟨3 * t ^ 3 + 3 * t ^ 2 + t, ?_⟩⟩
  · have : (3 * t + 1) ^ 2 = 9 * t ^ 2 + 6 * t + 1 := by ring
    rw [this]
    ring_nf
    omega
  · have : (3 * t + 1) ^ 3 = 27 * t ^ 3 + 27 * t ^ 2 + 9 * t + 1 := by ring
    rw [this]
    ring_nf
    omega

theorem l3u3_inn_three_mul_dvd_cube_sub_one {Q : ℕ} (hQ : Q % 3 = 1) :
    3 * (Q - 1) ∣ Q ^ 3 - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = 3 * t + 1 := ⟨Q / 3, by omega⟩
  refine ⟨3 * t ^ 2 + 3 * t + 1, ?_⟩
  have : (3 * t + 1) ^ 3 = 27 * t ^ 3 + 27 * t ^ 2 + 9 * t + 1 := by ring
  rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
  ring

theorem l3u3_inn_dvd_27_of_card_sl_one {N g E P Q : ℕ} (hg0 : g ≠ 0) (hg : g ∣ Q - 1)
    (h : N * g = Q ^ E * P) (hP : 3 * (Q - 1) ^ 4 ∣ P) (h3 : 3 ∣ Q - 1) : 27 ∣ N := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨u, hu⟩ := hg
  have h' : N * g = (Q ^ E * 3 * (Q - 1) ^ 3 * c * u) * g := by
    rw [h, hc]
    have : (Q - 1) ^ 4 = (Q - 1) ^ 3 * (g * u) := by rw [← hu]; ring
    rw [this]
    ring
  have hN := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hg0) h'
  rw [hN]
  have h27 : 27 ∣ (Q - 1) ^ 3 := by simpa using pow_dvd_pow_of_dvd h3 3
  exact ((Dvd.dvd.mul_left h27 _).mul_right _).mul_right _

theorem l3u3_inn_dvd_81_of_card_sl_two {N g E P Q : ℕ} (hcop : Nat.Coprime 3 g)
    (h : N * g = Q ^ E * P) (hP : 81 ∣ P) : 81 ∣ N := by
  have h81 : 81 ∣ N * g := h ▸ Dvd.dvd.mul_left hP _
  have hcop81 : Nat.Coprime 81 g := by
    have : (81 : ℕ) = 3 ^ 4 := by norm_num
    rw [this]
    exact Nat.Coprime.pow_left 4 hcop
  exact hcop81.dvd_of_dvd_mul_right h81

theorem l3u3_inn_two_pow_mod_three (m : ℕ) :
    (2 ^ m % 3 = 1 ∧ Even m) ∨ (2 ^ m % 3 = 2 ∧ Odd m) := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · left
    refine ⟨?_, ⟨k, by ring⟩⟩
    rw [pow_mul, Nat.pow_mod]
    norm_num
  · right
    refine ⟨?_, ⟨k, rfl⟩⟩
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem l3u3_inn_not_order_of_card_sl {ν m N : ℕ} (hν : 5 ≤ ν) (hm : 1 ≤ m) (hN : L3U3Order N)
    (hcard : N * Nat.gcd ν (2 ^ m - 1) =
      (2 ^ m) ^ (ν * (ν - 1) / 2) * ∏ k ∈ Finset.Icc 2 ν, ((2 ^ m) ^ k - 1)) : False := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ m := ⟨_, rfl⟩
  rw [← hQ] at hcard
  have hQeven : Even Q := hQ ▸ Nat.even_pow.2 ⟨even_two, by omega⟩
  have hQ2 : 2 ≤ Q := by
    rw [hQ]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd ν (Q - 1) := ⟨_, rfl⟩
  rw [← hg] at hcard
  have hg0 : g ≠ 0 := hg ▸ (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
  have hgdvd : g ∣ Q - 1 := hg ▸ Nat.gcd_dvd_right _ _
  obtain ⟨P, hP⟩ : ∃ P, P = ∏ k ∈ Finset.Icc 2 ν, (Q ^ k - 1) := ⟨_, rfl⟩
  rw [← hP] at hcard
  have hsub : ∀ T : Finset ℕ, T ⊆ Finset.Icc 2 ν → ∏ k ∈ T, (Q ^ k - 1) ∣ P :=
    fun T hT => hP ▸ Finset.prod_dvd_prod_of_subset T _ _ hT
  have h27 := hN.not_27_dvd
  rcases l3u3_inn_two_pow_mod_three m with ⟨hQ3, hme⟩ | ⟨hQ3, hmo⟩
  ·
    rw [← hQ] at hQ3
    have h3 : 3 ∣ Q - 1 := by omega
    have hT := hsub {2, 3, 4, 5} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      omega)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton] at hT
    have hdiv : 3 * (Q - 1) ^ 4 ∣ P := by
      have := mul_dvd_mul (l3u3_inn_sub_one_dvd_pow_sub_one Q 2) (mul_dvd_mul
        (l3u3_inn_three_mul_dvd_cube_sub_one hQ3) (mul_dvd_mul
          (l3u3_inn_sub_one_dvd_pow_sub_one Q 4) (l3u3_inn_sub_one_dvd_pow_sub_one Q 5)))
      refine dvd_trans ?_ hT
      convert this using 1
      ring
    exact h27 (l3u3_inn_dvd_27_of_card_sl_one hg0 hgdvd hcard hdiv h3)
  ·
    rw [← hQ] at hQ3
    have hcop : Nat.Coprime 3 g := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3g => ?_
      have := h3g.trans hgdvd
      omega
    have hy : (Q ^ 2) % 3 = 1 := by rw [Nat.pow_mod, hQ3]
    obtain ⟨hy1, hy2, hy3⟩ := l3u3_inn_three_dvd_of_mod_three_eq_one hy
    have h81 : 81 ∣ P := by
      by_cases h3m : 3 ∣ m
      · obtain ⟨m', hm'⟩ := h3m
        have hQ64 : Q ^ 2 = 64 ^ m' := by
          rw [hQ, ← pow_mul, hm', show 3 * m' * 2 = 6 * m' by ring, pow_mul]
          norm_num
        have h9 : 9 ∣ Q ^ 2 - 1 := by
          rw [hQ64]
          have := l3u3_inn_sub_one_dvd_pow_sub_one 64 m'
          exact dvd_trans (by norm_num) this
        have h9' : 9 ∣ Q ^ 4 - 1 := by
          have := l3u3_inn_sub_one_dvd_pow_sub_one (Q ^ 2) 2
          rw [← pow_mul] at this
          exact h9.trans this
        have hT := hsub {2, 4} (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_Icc]
          omega)
        rw [Finset.prod_insert (by decide), Finset.prod_singleton] at hT
        exact dvd_trans (by simpa using mul_dvd_mul h9 h9') hT
      · have hν6 : 6 ≤ ν := by
          by_contra hlt
          have hν5 : ν = 5 := by omega
          subst hν5
          obtain ⟨n, hn3, hn1, hv⟩ := hN.padicValNat_two
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hQodd : Odd (Q - 1) := l3u3_inn_odd_sub_one_of_even hQeven (by omega)
          have hgodd : Odd g := hQodd.of_dvd_nat hgdvd
          have hPodd : Odd P := by
            rw [hP]
            refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one ?_
            intro k hk
            rw [Finset.mem_Icc] at hk
            exact l3u3_inn_odd_sub_one_of_even (Nat.even_pow.2 ⟨hQeven, by omega⟩)
              (by positivity)
          have h1 := congrArg (padicValNat 2) hcard
          rw [padicValNat.mul hN.ne_zero hg0,
            padicValNat.mul (pow_ne_zero _ (by omega)) hPodd.pos.ne',
            padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hgodd)),
            padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hPodd)),
            padicValNat.pow, hQ, padicValNat.prime_pow, hv] at h1
          norm_num at h1
          omega
        have hT := hsub {2, 4, 6} (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_Icc]
          omega)
        rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
          Finset.prod_singleton] at hT
        have h4 : 3 ∣ Q ^ 4 - 1 := by
          have := hy2
          rwa [← pow_mul] at this
        have h6 : 9 ∣ Q ^ 6 - 1 := by
          have := hy3
          rwa [← pow_mul] at this
        exact dvd_trans (by simpa using mul_dvd_mul hy1 (mul_dvd_mul h4 h6)) hT
    exact h27 ((by norm_num : 27 ∣ 81).trans (l3u3_inn_dvd_81_of_card_sl_two hcop hcard h81))

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
