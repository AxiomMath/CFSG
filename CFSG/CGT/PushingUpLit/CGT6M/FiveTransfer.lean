module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveLines
public import CFSG.CGT.PushingUpLit.CGT6M.FiveFrob
public import CFSG.CGT.PushingUpLit.CGT6M.FiveLift

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open scoped commutatorElement

section Lift

variable {L Q : Type*} [Group L] [Group Q]

theorem eq_one_of_pow_eq_one_of_mem_ker [Finite L] {ν : L →* Q} {p : ℕ} (hp : p.Prime)
    (hC : ¬ p ∣ Nat.card ν.ker) {c : L} (hc : c ∈ ν.ker) (hcp : c ^ p = 1) : c = 1 := by
  have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have h2 : orderOf c ∣ Nat.card ν.ker := by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : ν.ker)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hC

theorem eq_of_map_eq_of_pow_eq_one [Finite L] {ν : L →* Q} (hcent : ν.ker ≤ Subgroup.center L)
    {p : ℕ} (hp : p.Prime) (hC : ¬ p ∣ Nat.card ν.ker) {x y : L} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : ν x = ν y) : x = y := by
  have hc : x⁻¹ * y ∈ ν.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hcomm : Commute x (x⁻¹ * y) :=
    (Subgroup.mem_center_iff.mp (hcent hc) x : x * (x⁻¹ * y) = (x⁻¹ * y) * x)
  have hy' : y = x * (x⁻¹ * y) := by group
  have hcp : (x⁻¹ * y) ^ p = 1 := by
    have h := hy
    rw [hy', hcomm.mul_pow, hx, one_mul] at h
    exact h
  have := eq_one_of_pow_eq_one_of_mem_ker hp hC hc hcp
  rw [inv_mul_eq_one] at this
  exact this

theorem exists_lift_of_pow_eq_one [Finite L] {ν : L →* Q} (hν : Function.Surjective ν) {p : ℕ}
    (hp : p.Prime) (hC : ¬ p ∣ Nat.card ν.ker) {b : Q} (hb : b ^ p = 1) :
    ∃ a : L, ν a = b ∧ a ^ p = 1 := by
  obtain ⟨a₀, rfl⟩ := hν b
  set N := Nat.card ν.ker with hN
  have hcop : Nat.Coprime N p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hC).symm
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨a₀ ^ (N * u), ?_, ?_⟩
  · have hpow : ∀ n : ℕ, ν a₀ ^ n = ν a₀ ^ (n % p) := fun n => by
      conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hb, one_pow, mul_one]
    rw [map_pow, hpow (N * u), hu, pow_one]
  · have hc : a₀ ^ p ∈ ν.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hb
    have h1 : (⟨a₀ ^ p, hc⟩ : ν.ker) ^ N = 1 := pow_card_eq_one'
    have h2 : (a₀ ^ p) ^ N = 1 := congrArg Subtype.val h1
    rw [← pow_mul, show N * u * p = p * N * u by ring, pow_mul, pow_mul, h2, one_pow]

end Lift

section Sylow

variable {L : Type*} [Group L] [Finite L]

theorem exists_conj_mem_of_card {p : ℕ} (hp : p.Prime) (S : Subgroup L) {k : ℕ}
    (hS : Nat.card S = p ^ k) (hL : ¬ p ^ (k + 1) ∣ Nat.card L) {y : L} (hy : y ^ p = 1) :
    ∃ g : L, g * y * g⁻¹ ∈ S := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ k ∣ Nat.card L := hS ▸ Subgroup.card_subgroup_dvd_card S
  have hfac : (Nat.card L).factorization p = k := by
    have h1 : k ≤ (Nat.card L).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hdvd
    have h2 : ¬ k + 1 ≤ (Nat.card L).factorization p := fun h =>
      hL ((Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mpr h)
    omega
  let T : Sylow p L := Sylow.ofCard S (by rw [hS, hfac])
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    have hord : orderOf y ∣ p ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hy
    exact IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, pow_one]; simpa using hord)
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q T
  refine ⟨g, ?_⟩
  have hyQ : y ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers y)
  have : g * y * g⁻¹ ∈ ((g • Q : Sylow p L) : Subgroup L) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨y, hyQ, rfl⟩
  rw [hg] at this
  exact this

end Sylow

section Order

variable {L Q : Type*} [Group L] [Finite L] [Group Q]

omit [Finite L] in
theorem not_pow_dvd_card_of_surjective {ν : L →* Q} (hν : Function.Surjective ν) {p n : ℕ}
    (hp : p.Prime) (hC : ¬ p ∣ Nat.card ν.ker) (hQ : ¬ p ^ n ∣ Nat.card Q) :
    ¬ p ^ n ∣ Nat.card L := by
  intro h
  rw [← Subgroup.card_ker_mul_card_of_surjective hν] at h
  have hcop : Nat.Coprime (p ^ n) (Nat.card ν.ker) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hC)
  exact hQ (hcop.dvd_of_dvd_mul_left h)

end Order

section Transfer

variable {V : Type} [CommGroup V] [Finite V]

theorem card_commSub_le_of_card_le {x : MulAut V} (h : Nat.card V ≤ 2 ^ 4 * Nat.card (fixSub x)) :
    Nat.card (commSub x) ≤ 16 := by
  have h1 := card_commSub_mul_card_fixSub x
  have hpos : 0 < Nat.card (fixSub x) := Nat.card_pos
  by_contra hlt
  have h2 : 16 < Nat.card (commSub x) := Nat.lt_of_not_le hlt
  have h3 := Nat.mul_lt_mul_of_pos_right h2 hpos
  omega

@[expose] def LinesData (Q : Type*) [Group Q] : Prop :=
  ∃ a b g : Q, a ≠ 1 ∧ a ^ 5 = 1 ∧ Commute a b ∧ g * a * g⁻¹ = b ∧ g * b * g⁻¹ = (a * b)⁻¹ ∧
    ¬ 5 ^ 3 ∣ Nat.card Q

@[expose] def FrobData (Q : Type*) [Group Q] : Prop :=
  ∃ a b : Q, a ^ 11 = 1 ∧ a ≠ 1 ∧ b ^ 5 = 1 ∧ b * a * b⁻¹ = a ^ 3 ∧ ¬ 5 ^ 2 ∣ Nat.card Q

theorem false_of_linesData {L Q : Type} [Group L] [Finite L] [Group Q] (ρ : L →* MulAut V)
    (hρ : Function.Injective ρ) (hV : ∀ v : V, v ^ 2 = 1) (π : L →* Q)
    (hπ : Function.Surjective π) (hK : π.ker ≤ Subgroup.center L) (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hd : LinesData Q) {y : L} (hy1 : y ≠ 1) (hy5 : y ^ 5 = 1)
    (h16 : Nat.card V ≤ 2 ^ 4 * Nat.card (fixSub (ρ y))) : False := by
  obtain ⟨a, b, g, ha1, ha5, hab, hga, hgb, hQ⟩ := hd
  obtain ⟨a', b', g', ha1', ha5', hab', hga', hgb'⟩ :=
    exists_five_data_of_surjective π hπ hK hK5 ha1 ha5 hab hga hgb
  have hb5' : b' ^ 5 = 1 := by rw [← hga', conj_pow, ha5']; group
  let Φ₀ : C55 →* L := phi a' b' ha5' hb5' hab'
  have hΦ₀ : Function.Injective Φ₀ := phi_injective ha1' ha5' hb5' hab' hga' hgb'
  have hcardS : Nat.card Φ₀.range = 5 ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦ₀).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod, ZMod.card]
    norm_num
  have hL : ¬ 5 ^ (2 + 1) ∣ Nat.card L :=
    not_pow_dvd_card_of_surjective hπ Nat.prime_five hK5 hQ
  obtain ⟨ℓ, hℓ⟩ := exists_conj_mem_of_card Nat.prime_five Φ₀.range hcardS hL hy5
  obtain ⟨u, hu⟩ := hℓ
  set w : ZMod 5 × ZMod 5 := Multiplicative.toAdd u with hwdef
  have huw : u = Multiplicative.ofAdd w := rfl
  rw [huw] at hu
  have hw : w ≠ 0 := by
    intro h
    rw [h, ofAdd_zero, map_one] at hu
    apply hy1
    have : y = ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * ℓ := by group
    rw [this, ← hu]
    group
  have hM : ∀ u : C55, (ρ.comp Φ₀) (AddMonoidHom.toMultiplicative mapM u) =
      ρ g' * (ρ.comp Φ₀) u * (ρ g')⁻¹ := by
    intro u
    simp only [MonoidHom.comp_apply, Φ₀]
    rw [phi_mapM ha5' hb5' hab' hga' hgb' u, map_mul, map_mul, map_inv]
  have hcomm : Nat.card (commSub ((ρ.comp Φ₀) (Multiplicative.ofAdd w))) ≤ 16 := by
    simp only [MonoidHom.comp_apply]
    rw [hu, map_mul, map_mul, map_inv, card_commSub_conj]
    exact card_commSub_le_of_card_le h16
  exact false_of_lines_hom (ρ.comp Φ₀) (ρ g') hM (hρ.comp hΦ₀) hw hV hcomm

theorem false_of_frobData {L Q : Type} [Group L] [Finite L] [Group Q] (ρ : L →* MulAut V)
    (hρ : Function.Injective ρ) (hV : ∀ v : V, v ^ 2 = 1) (π : L →* Q)
    (hπ : Function.Surjective π) (hK : π.ker ≤ Subgroup.center L) (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hK11 : ¬ 11 ∣ Nat.card π.ker) (hd : FrobData Q) {y : L} (hy1 : y ≠ 1) (hy5 : y ^ 5 = 1)
    (h16 : Nat.card V ≤ 2 ^ 4 * Nat.card (fixSub (ρ y))) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a, b, ha11, ha1, hb5, hba, hQ⟩ := hd
  obtain ⟨a', ha', ha11'⟩ := exists_lift_of_pow_eq_one hπ (by decide : Nat.Prime 11) hK11 ha11
  obtain ⟨b', hb', hb5'⟩ := exists_lift_of_pow_eq_one hπ Nat.prime_five hK5 hb5
  have hba' : b' * a' * b'⁻¹ = a' ^ 3 := by
    refine eq_of_map_eq_of_pow_eq_one hK (by decide : Nat.Prime 11) hK11 ?_ ?_ ?_
    · rw [conj_pow, ha11']; group
    · rw [← pow_mul, mul_comm, pow_mul, ha11', one_pow]
    · rw [map_mul, map_mul, map_inv, map_pow, ha', hb', hba]
  have ha1' : a' ≠ 1 := fun h => ha1 (by rw [← ha', h, map_one])
  have hb1' : b' ≠ 1 := by
    intro h
    rw [h] at hba'
    simp only [one_mul, inv_one, mul_one] at hba'
    apply ha1'
    have h2 : a' ^ 2 = 1 := by
      have : a' ^ 3 = a' * a' ^ 2 := by group
      rw [this] at hba'
      exact (mul_eq_left.mp hba'.symm)
    calc a' = a' ^ 11 * (a' ^ 2)⁻¹ ^ 5 := by group
      _ = 1 := by rw [ha11', h2]; group
  have hord : orderOf b' = 5 := orderOf_eq_prime hb5' hb1'
  have hcardS : Nat.card (Subgroup.zpowers b') = 5 ^ 1 := by rw [Nat.card_zpowers, hord, pow_one]
  have hL : ¬ 5 ^ (1 + 1) ∣ Nat.card L :=
    not_pow_dvd_card_of_surjective hπ Nat.prime_five hK5 hQ
  obtain ⟨ℓ, hℓ⟩ := exists_conj_mem_of_card Nat.prime_five (Subgroup.zpowers b') hcardS hL hy5
  have hfin : IsOfFinOrder b' := isOfFinOrder_of_finite b'
  obtain ⟨r, hr⟩ := Submonoid.mem_powers_iff _ _ |>.mp
    ((hfin.mem_powers_iff_mem_zpowers).mpr hℓ)
  have hr5 : ¬ 5 ∣ r := by
    rintro ⟨c, rfl⟩
    apply hy1
    have h1 : ℓ * y * ℓ⁻¹ = 1 := by rw [← hr, pow_mul, hb5', one_pow]
    have : y = ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * ℓ := by group
    rw [this, h1]
    group
  have hfrob := two_pow_five_le_card_commSub_of_frobenius (a := ρ a') (b := ρ b')
    (by rw [← map_pow, ha11', map_one]) (fun h => ha1' (hρ (by rw [h, map_one])))
    (by rw [← map_inv, ← map_mul, ← map_mul, hba', map_pow]) hV
  have hbr : (ρ b') ^ 5 = 1 := by rw [← map_pow, hb5', map_one]
  have hcomm : Nat.card (commSub (ρ y)) ≤ 16 := card_commSub_le_of_card_le h16
  have hcard : Nat.card (commSub (ρ y)) = Nat.card (commSub (ρ b')) := by
    have h1 : Nat.card (commSub ((ρ b') ^ r)) = Nat.card (commSub (ρ b')) := by
      rw [commSub_pow_eq_of_not_dvd hbr hr5]
    have h2 : (ρ b') ^ r = ρ ℓ * ρ y * (ρ ℓ)⁻¹ := by
      rw [← map_pow, hr, map_mul, map_mul, map_inv]
    rw [h2, card_commSub_conj] at h1
    exact h1
  omega

end Transfer

end CFSG.CGT.PushingUpLit.CGT6M
