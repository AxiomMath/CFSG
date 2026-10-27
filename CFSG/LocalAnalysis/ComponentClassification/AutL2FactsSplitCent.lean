module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisT
public import CFSG.Walter.PSL2Facts.Odd

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

theorem fu_eq_self_of_odd {σ : F ≃+* F} (hσ : Odd (orderOf σ)) {c : Fˣ} {r : ℕ}
    (hc : c ^ 2 ^ r = 1) : fu F σ c = c := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, c ^ k = fu F σ c := by
    have h := fu_mem_zpowers σ c (mem_zpowers c)
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  have hit : ∀ i : ℕ, fu F (σ ^ i) c = c ^ (k ^ i) := by
    intro i
    induction i with
    | zero => simp [fu_one]
    | succ i ih => rw [pow_succ', fu_mul, ih, map_pow, ← hk, ← pow_mul, ← pow_succ']
  have hm : c ^ (k ^ orderOf σ) = c ^ 1 := by rw [← hit, pow_orderOf_eq_one, fu_one, pow_one]
  rw [pow_eq_pow_iff_modEq] at hm
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hc)
  rw [← hk]
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · rw [pow_zero, orderOf_eq_one_iff] at hs
    rw [hs, one_pow]
  rw [hs] at hm
  have hkodd : Odd k := by
    have h2 : k ^ orderOf σ ≡ 1 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 hs0.ne') hm
    have h2' : Odd (k ^ orderOf σ) := Nat.odd_iff.mpr h2
    rcases Nat.even_or_odd k with he | ho
    · exact absurd (Nat.even_pow.mpr ⟨he, (orderOf_pos σ).ne'⟩) (Nat.not_even_iff_odd.mpr h2')
    · exact ho
  have hcop : Nat.Coprime k (2 ^ s) := Nat.Coprime.pow_right s (Nat.coprime_two_right.mpr hkodd)
  have h1 : ((k : ZMod (2 ^ s))) ^ orderOf σ = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
    push_cast at this
    exact this
  have h2 : ((k : ZMod (2 ^ s))) ^ Nat.totient (2 ^ s) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hcop)
    push_cast at this
    exact this
  have hg : Nat.gcd (orderOf σ) (Nat.totient (2 ^ s)) = 1 := by
    rw [Nat.totient_prime_pow Nat.prime_two hs0]
    apply Nat.Coprime.mul_right _ (by norm_num)
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hσ)
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hg, pow_one] at h3
  have hmod : k ≡ 1 [MOD 2 ^ s] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [h3]; simp)
  calc c ^ k = c ^ 1 := (pow_eq_pow_iff_modEq.mpr (by rw [hs]; exact hmod))
    _ = c := pow_one c

omit [Finite F] in
theorem pow_odd_part_two_pow {M R : ℕ} (hRM : Nat.card Fˣ = 2 ^ R * M) (c : Fˣ) :
    (c ^ M) ^ 2 ^ R = 1 := by
  rw [← pow_mul, mul_comm, ← hRM, pow_card_eq_one']

omit [Finite F] in
theorem nm_false_pow_eq_prod (a : Fˣ) (σ : F ≃+* F) (j : ℕ) :
    nm F a false σ ^ j = nm F (∏ i ∈ Finset.range j, fu F (σ ^ i) a) false (σ ^ j) := by
  induction j with
  | zero => simp [nm_one]
  | succ j ih =>
    rw [pow_succ, ih, nm_mul, Finset.prod_range_succ, pow_succ]
    rfl

omit [Finite F] in
theorem nm_pow_exists (a : Fˣ) (ε : Bool) (σ : F ≃+* F) (j : ℕ) :
    ∃ c : Fˣ, nm F a ε σ ^ j = nm F c (ε && decide (j % 2 = 1)) (σ ^ j) := by
  induction j with
  | zero => exact ⟨1, by simp [nm_one]⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * twist F (ε && decide (j % 2 = 1)) (fu F (σ ^ j) a), ?_⟩
    rw [pow_succ, hc, nm_mul, pow_succ]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> cases ε <;> simp [h, Nat.add_mod]

theorem odd_nm_struct {M R : ℕ} (hRM : Nat.card Fˣ = 2 ^ R * M) {a : Fˣ} {ε : Bool}
    {σ : F ≃+* F} (h : Odd (orderOf (nm F a ε σ))) :
    ε = false ∧ Odd (orderOf σ) ∧ a ^ M = 1 := by
  have hσ : Odd (orderOf σ) :=
    Odd.of_dvd_nat h (orderOf_map_dvd (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) _)
  have hε : ε = false := by
    obtain ⟨c, hc⟩ := nm_pow_exists a ε σ (orderOf (nm F a ε σ))
    rw [pow_orderOf_eq_one, ← nm_one] at hc
    have h1 := (nm_injective hc).2.1
    rw [Nat.odd_iff.mp h] at h1
    simpa using h1.symm
  subst hε
  refine ⟨rfl, hσ, ?_⟩
  set m := orderOf (nm F a false σ)
  have h1 := nm_false_pow_eq_prod a σ m
  rw [pow_orderOf_eq_one, ← nm_one] at h1
  have hP := (nm_injective h1).1
  have h2 : (a ^ M) ^ m = 1 := by
    have := congrArg (· ^ M) hP
    simp only [one_pow] at this
    rw [← Finset.prod_pow] at this
    have hfix : ∀ i ∈ Finset.range m, (fu F (σ ^ i) a) ^ M = a ^ M := by
      intro i _
      rw [← map_pow]
      exact fu_eq_self_of_odd (Odd.of_dvd_nat hσ (orderOf_pow_dvd i))
        (pow_odd_part_two_pow hRM a)
    rw [Finset.prod_congr rfl hfix, Finset.prod_const, Finset.card_range] at this
    exact this.symm
  have h3 := pow_odd_part_two_pow hRM a
  have := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right R (Nat.coprime_two_right.mpr h)),
    pow_one] at this

omit [Finite F] in
theorem odd_orderOf_nm_false {M : ℕ} (hM : Odd M) {c : Fˣ} (hc : c ^ M = 1)
    {ρ : F ≃+* F} (hρ : Odd (orderOf ρ)) : Odd (orderOf (nm F c false ρ)) := by
  have h1 := nm_false_pow_eq_prod c ρ (orderOf ρ)
  rw [pow_orderOf_eq_one] at h1
  have hP : (∏ i ∈ Finset.range (orderOf ρ), fu F (ρ ^ i) c) ^ M = 1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i _
    rw [← map_pow, hc, map_one]
  have h2 : nm F c false ρ ^ (orderOf ρ * M) = 1 := by
    rw [pow_mul, h1, nm_false_pow_eq_prod,
      Finset.prod_congr rfl (fun i _ => by rw [one_pow, fu_one]), Finset.prod_const,
      Finset.card_range, hP, one_pow, nm_one]
  exact Odd.of_dvd_nat (hρ.mul hM) (orderOf_dvd_of_pow_eq_one h2)

theorem odd_mul_of_commute_z (hneg : (-1 : Fˣ) ≠ 1) {x y : PGammaL2 F}
    (hx : x * SemidirectProduct.inl (tor F (-1)) = SemidirectProduct.inl (tor F (-1)) * x)
    (hy : y * SemidirectProduct.inl (tor F (-1)) = SemidirectProduct.inl (tor F (-1)) * y)
    (hxo : Odd (orderOf x)) (hyo : Odd (orderOf y)) : Odd (orderOf (x * y)) := by
  obtain ⟨R, M, hM, hRM⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := Fˣ)).ne'
  have hconj : ∀ w : PGammaL2 F,
      w * SemidirectProduct.inl (tor F (-1)) = SemidirectProduct.inl (tor F (-1)) * w →
        ∃ a ε, w = nm F a ε w.right := fun w hw =>
    exists_nm_of_conj_tor w hneg (by rw [hw, mul_inv_cancel_right])
  obtain ⟨a, ε, hxa⟩ := hconj x hx
  obtain ⟨b, δ, hyb⟩ := hconj y hy
  rw [hxa] at hxo
  rw [hyb] at hyo
  obtain ⟨rfl, hσ, ha⟩ := odd_nm_struct hRM hxo
  obtain ⟨rfl, hτ, hb⟩ := odd_nm_struct hRM hyo
  rw [hxa, hyb, nm_mul]
  apply odd_orderOf_nm_false hM
  · rw [twist_false, mul_pow, ← map_pow, ha, hb, map_one, one_mul]
  · have hc : Commute x.right y.right := ringAut_comm _ _
    exact Odd.of_dvd_nat (hσ.mul hτ) ((hc.orderOf_mul_dvd_lcm).trans (Nat.lcm_dvd_mul _ _))

theorem HarrisHyp.odd_mul_of_commute_inv (hH : HarrisHyp F) {ι : PGammaL2 F}
    (hιL : ι ∈ pGammaL2PSLRange F) (hι : orderOf ι = 2) {x y : PGammaL2 F}
    (hx : x * ι = ι * x) (hy : y * ι = ι * y) (hxo : Odd (orderOf x)) (hyo : Odd (orderOf y)) :
    Odd (orderOf (x * y)) := by
  obtain ⟨p, f, hp, hp2, hF, -⟩ := hH.char
  have : Fact p.Prime := ⟨hp⟩
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hF
      exact absurd hF (Finite.one_lt_card (α := F)).ne'
    · exact h
  obtain ⟨i₀, rfl⟩ := hιL
  change orderOf (incl F i₀) = 2 at hι
  have hi₀ : orderOf i₀ = 2 := by rwa [orderOf_injective _ (incl_injective F)] at hι
  set z : PGammaL2 F := SemidirectProduct.inl (tor F (-1)) with hzdef
  have hzL : z ∈ pGammaL2PSLRange F := by
    rw [hzdef, inl_tor]
    exact rStd_le_pslRange hH.zStd_mem_rStd
  obtain ⟨z₀, hz₀⟩ := hzL
  change incl F z₀ = z at hz₀
  have hz₀o : orderOf z₀ = 2 := by
    have hz2 : z * z = 1 := by rw [hzdef, inl_tor, z_mul_self]
    have hz1 : z ≠ 1 := by rw [hzdef, inl_tor]; exact hH.zStd_ne_one
    have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    rwa [← hz₀, orderOf_injective _ (incl_injective F)] at hzo
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (CFSG.Walter.psl2_isConj_of_orderOf_eq_two F hF (hp.odd_of_ne_two hp2) hf hz₀o hi₀)
  set G := incl F g
  change x * incl F i₀ = incl F i₀ * x at hx
  change y * incl F i₀ = incl F i₀ * y at hy
  have hι' : incl F i₀ = G * z * G⁻¹ := by rw [← hg, map_mul, map_mul, map_inv, hz₀]
  have hcz : ∀ w : PGammaL2 F, w * incl F i₀ = incl F i₀ * w →
      G⁻¹ * w * G * z = z * (G⁻¹ * w * G) := by
    intro w hw
    rw [hι'] at hw
    calc G⁻¹ * w * G * z = G⁻¹ * (w * (G * z * G⁻¹)) * G := by group
      _ = G⁻¹ * ((G * z * G⁻¹) * w) * G := by rw [hw]
      _ = z * (G⁻¹ * w * G) := by group
  have hord : ∀ w : PGammaL2 F, orderOf (G⁻¹ * w * G) = orderOf w := fun w => by
    have := MulEquiv.orderOf_eq (MulAut.conj G⁻¹) w
    rwa [MulAut.conj_apply, inv_inv] at this
  have key := odd_mul_of_commute_z hH.neg_one_ne_one (hcz x hx) (hcz y hy)
    (by rw [hord]; exact hxo) (by rw [hord]; exact hyo)
  rw [show G⁻¹ * x * G * (G⁻¹ * y * G) = G⁻¹ * (x * y) * G by group, hord] at key
  exact key

end CFSG.ComponentClassification.AutL2Facts
