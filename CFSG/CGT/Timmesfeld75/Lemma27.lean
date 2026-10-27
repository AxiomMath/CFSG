module

public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonNonsplitTorus

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Timmesfeld

theorem faithful_le_of_primitive {X N : Type*} [Group X] [Finite X] [Group N] [Finite N]
    (ρ : X →* MulAut N) (hρ : Function.Injective ρ) {d k r : ℕ} (hk : 0 < k)
    (hN : Nat.card N = 2 ^ d) (hr : IsPrimitivePrimeDivisor r k) (hX : r ∣ Nat.card X) :
    k ≤ d := by
  have : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' r hX
  have hne : ρ h ≠ 1 := by
    intro h1
    have : h = 1 := hρ (by rw [h1, map_one])
    rw [this, orderOf_one] at hh
    exact hr.prime.one_lt.ne hh
  obtain ⟨e, hed, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow Nat.prime_two hr.prime ρ
    hh hne hN
  have hfac : 2 ^ d - 2 ^ e = 2 ^ e * (2 ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
  rw [hfac] at hdvd
  have hr2 : ¬ r ∣ 2 ^ e := fun h' =>
    hr.ne_two hk ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp
      (hr.prime.dvd_of_dvd_pow h'))
  have hdvd' : r ∣ 2 ^ (d - e) - 1 :=
    (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hr.prime).mpr hr2) hdvd)
  by_contra hlt
  push Not at hlt
  exact hr.2.2 (d - e) (by omega) (by omega) hdvd'

theorem primitive_dvd_card_sz
    {a r : ℕ} (hr : IsPrimitivePrimeDivisor r (4 * (2 * a + 1))) :
    r ∣ Nat.card (Sz a) := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
  have hk : 0 < 4 * (2 * a + 1) := by omega
  have h1 : r ∣ 2 ^ (2 * (2 * a + 1)) + 1 := by
    rw [hr.dvd_add_one_iff hk]
    refine ⟨?_, fun h => ?_⟩
    · exact ⟨1, by ring⟩
    · have := Nat.le_of_dvd (by omega) h
      omega
  have h2 : (2 ^ (2 * a + 1)) ^ 2 + 1 = 2 ^ (2 * (2 * a + 1)) + 1 := by
    rw [← pow_mul, mul_comm]
  rw [h2]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _

theorem primitive_dvd_card_psu3 {f r : ℕ} (hf : 1 ≤ f) (hr : IsPrimitivePrimeDivisor r (6 * f)) :
    r ∣ Nat.card (PSU3 2 f) := by
  have hk : 0 < 6 * f := by omega
  have hmul := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd hf
  have h1 : r ∣ 2 ^ (3 * f) + 1 := by
    rw [hr.dvd_add_one_iff hk]
    refine ⟨⟨1, by ring⟩, fun h => ?_⟩
    have := Nat.le_of_dvd (by omega) h
    omega
  have h2 : r ∣ Nat.card (PSU3 2 f) * Nat.gcd 3 (2 ^ f + 1) := by
    rw [hmul]
    have h3 : (2 ^ f) ^ 3 + 1 = 2 ^ (3 * f) + 1 := by rw [← pow_mul, mul_comm]
    have h4 : r ∣ (2 ^ f) ^ 3 + 1 := h3 ▸ h1
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h4 _) _
  rcases hr.prime.dvd_mul.mp h2 with h | h
  · exact h
  · exfalso
    have h3 : r ∣ 3 := h.trans (Nat.gcd_dvd_left 3 _)
    have := hr.eq_two_of_dvd_three hk h3
    omega

theorem lemma27_sz
    {X N : Type*} [Group X] [Finite X] [Group N] [Finite N] {a d : ℕ}
    (ha : 1 ≤ a) (hX : Nat.card (Sz a) ∣ Nat.card X) (ρ : X →* MulAut N)
    (hρ : Function.Injective ρ) (hN : Nat.card N = 2 ^ d) : 4 * (2 * a + 1) ≤ d := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * (2 * a + 1)) (by omega) (by omega)
  exact faithful_le_of_primitive ρ hρ (by omega) hN hr ((primitive_dvd_card_sz hr).trans hX)

theorem lemma27_psu3 {X N : Type*} [Group X] [Finite X] [Group N] [Finite N] {f d : ℕ}
    (hf : 2 ≤ f) (hX : Nat.card (PSU3 2 f) ∣ Nat.card X) (ρ : X →* MulAut N)
    (hρ : Function.Injective ρ) (hN : Nat.card N = 2 ^ d) : 6 * f ≤ d := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 6 * f) (by omega) (by omega)
  exact faithful_le_of_primitive ρ hρ (by omega) hN hr
    ((primitive_dvd_card_psu3 (by omega) hr).trans hX)

theorem lemma27_psl2 {X N : Type*} [Group X] [Finite X] [Group N] [Finite N] {n d : ℕ}
    (hn : 2 ≤ n) (hn3 : n ≠ 3) (hX : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card X)
    (ρ : X →* MulAut N) (hρ : Function.Injective ρ) (hN : Nat.card N = 2 ^ d) : 2 * n ≤ d :=
  CFSG.SL2MinimalFaithful.two_mul_le_of_injective Nat.prime_two (by omega) hX
    (fun _ => by
      obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
      exact ⟨r, hr.1, hr.2.1, hr.2.2⟩) ρ hρ hN

theorem card_dvd_card_sub_of_fixed_subset {K β : Type*} [Group K] [Finite K] [MulAction K β]
    [Finite β] {C : Set β} (hC : ∀ k : K, ∀ x ∈ C, k • x ∈ C)
    (hfix : ∀ k : K, k ≠ 1 → ∀ x : β, k • x = x → x ∈ C) :
    Nat.card K ∣ Nat.card β - Nat.card C := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype β := Fintype.ofFinite β
  let S : SubMulAction K β :=
    { carrier := Cᶜ
      smul_mem' := fun k x hx hk => hx (by
        have := hC k⁻¹ _ hk
        simpa using this) }
  have hfree : ∀ k : K, k ≠ 1 → ∀ x : S, k • x ≠ x := by
    intro k hk x hx
    have hx' : k • (x : β) = x := by
      have := congrArg Subtype.val hx
      simpa using this
    exact x.2 (hfix k hk x hx')
  have : Fintype S := Fintype.ofFinite S
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group K S
  have hsum : (∑ k : K, Fintype.card (MulAction.fixedBy S k)) = Fintype.card S := by
    rw [Finset.sum_eq_single (1 : K)]
    · simp
    · intro k _ hk
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨x, hx⟩ => hfree k hk x hx⟩
    · simp
  rw [hsum] at h
  have hS : Nat.card S = Nat.card β - Nat.card C := by
    have h1 : Nat.card S = Nat.card (Cᶜ : Set β) := rfl
    rw [h1, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_compl]
  rw [← hS, Nat.card_eq_fintype_card (α := S), Nat.card_eq_fintype_card (α := K)]
  exact ⟨Fintype.card (Quotient (MulAction.orbitRel K S)), by rw [h, mul_comm]⟩

theorem six_dvd_of_nine_dvd_two_pow_sub_one {m : ℕ} (h : 9 ∣ 2 ^ m - 1) : 6 ∣ m := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 2 ^ m % 9 = 1 := by omega
  have h3 : 2 ^ m % 9 = 2 ^ (m % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod m 6, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [h3] at h2
  have h4 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have h5 : m % 6 = 0 := by
    interval_cases hr : m % 6 <;> simp_all
  omega

theorem exists_pow_eq_pow_three_of_orderOf_nine {X : Type*} [Group X] {c : X}
    (hc : orderOf c = 9) {k : X} (hk : k ∈ Subgroup.zpowers c) (hk1 : k ≠ 1) :
    ∃ j : ℕ, k ^ j = c ^ 3 := by
  have hc9 : c ^ 9 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hi : c ^ i = c ^ (i % 9).toNat := by
    have h1 := zpow_mod_orderOf c i
    rw [hc] at h1
    have h2 : (0 : ℤ) ≤ i % 9 := Int.emod_nonneg _ (by norm_num)
    rw [← h1, ← zpow_natCast, Int.toNat_of_nonneg h2]
    simp
  have hr : (i % 9).toNat < 9 := by
    have := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < 9)
    omega
  have hr0 : (i % 9).toNat ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hi
    exact hk1 hi
  rw [hi]
  set r := (i % 9).toNat with hrdef
  have key : ∀ j : ℕ, r * j % 9 = 3 → ∃ j : ℕ, (c ^ r) ^ j = c ^ 3 := by
    intro j hj
    refine ⟨j, ?_⟩
    rw [← pow_mul, pow_eq_pow_mod _ hc9, hj]
  interval_cases r
  · exact absurd rfl hr0
  · exact key 3 (by norm_num)
  · exact key 6 (by norm_num)
  · exact key 1 (by norm_num)
  · exact key 3 (by norm_num)
  · exact key 6 (by norm_num)
  · exact key 2 (by norm_num)
  · exact key 3 (by norm_num)
  · exact key 6 (by norm_num)

theorem faithful_le_of_orderOf_nine {X N : Type*} [Group X] [Group N] [Finite N]
    (ρ : X →* MulAut N) (hρ : Function.Injective ρ) {d : ℕ} (hN : Nat.card N = 2 ^ d)
    {c : X} (hc : orderOf c = 9) : 6 ≤ d := by
  have hg3 : orderOf (c ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hc]; norm_num), hc]
  have hρg : ρ (c ^ 3) ≠ 1 := by
    intro h1
    have : c ^ 3 = 1 := hρ (by rw [h1, map_one])
    rw [this, orderOf_one] at hg3
    omega
  let C : Subgroup N :=
    { carrier := {x | ρ (c ^ 3) x = x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ (c ^ 3) a = a := ha
        have hb' : ρ (c ^ 3) b = b := hb
        show ρ (c ^ 3) (a * b) = a * b
        rw [map_mul, ha', hb']
      one_mem' := by
        show ρ (c ^ 3) 1 = 1
        simp
      inv_mem' := fun {a} ha => by
        have ha' : ρ (c ^ 3) a = a := ha
        show ρ (c ^ 3) a⁻¹ = a⁻¹
        rw [map_inv, ha'] }
  obtain ⟨e, hed, hCe⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (hN ▸ Subgroup.card_subgroup_dvd_card C)
  have hlt : e < d := by
    refine lt_of_le_of_ne hed fun hde => hρg ?_
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hCe, hN, hde])
    ext x
    exact (htop ▸ Subgroup.mem_top x : x ∈ C)
  let K : Subgroup X := Subgroup.zpowers c
  have hK9 : Nat.card K = 9 := by rw [Nat.card_zpowers, hc]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK9]; norm_num)
  let _ : MulAction K N := MulAction.compHom N (ρ.comp K.subtype)
  have hsmul : ∀ (k : K) (x : N), k • x = ρ (k : X) x := fun k x => rfl
  have hcomm : ∀ k : K, Commute (k : X) (c ^ 3) := by
    intro k
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp k.2
    rw [← hj]
    exact Commute.zpow_left (Commute.pow_right (Commute.refl c) 3) j
  have hdvd := card_dvd_card_sub_of_fixed_subset (K := K) (β := N) (C := (C : Set N))
    (fun k x hx => by
      have hx' : ρ (c ^ 3) x = x := hx
      show ρ (c ^ 3) (k • x) = k • x
      rw [hsmul, ← MulAut.mul_apply, ← map_mul, (hcomm k).symm.eq, map_mul, MulAut.mul_apply, hx'])
    (fun k hk x hx => by
      have hk' : (k : X) ≠ 1 := fun h => hk (Subtype.ext h)
      obtain ⟨j, hj⟩ := exists_pow_eq_pow_three_of_orderOf_nine hc k.2 hk'
      have hfix : ∀ n : ℕ, ρ ((k : X) ^ n) x = x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, map_mul, MulAut.mul_apply]
          have : ρ (k : X) x = x := hx
          rw [this, ih]
      show ρ (c ^ 3) x = x
      rw [← hj]
      exact hfix j)
  rw [hK9, hN] at hdvd
  have hCcard : Nat.card (C : Set N) = 2 ^ e := hCe
  rw [hCcard] at hdvd
  have hfac : 2 ^ d - 2 ^ e = 2 ^ e * (2 ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
  rw [hfac] at hdvd
  have hcop : Nat.Coprime 9 (2 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
  have h6 := six_dvd_of_nine_dvd_two_pow_sub_one (hcop.dvd_of_dvd_mul_left hdvd)
  have := Nat.le_of_dvd (by omega) h6
  omega

theorem exists_orderOf_nine_of_surjective_psl2_eight {X : Type*} [Group X] [Finite X]
    (π : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))
    (hπ : Function.Surjective π) : ∃ c : X, orderOf c = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨S, hS, hScard, -⟩ := CFSG.Glauberman.Dickson.h84_nonsplit_torus_data
    (F := GaloisField 2 3) (p := 2) (f := 3) hcard
  rw [hcard] at hScard
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hg9 : orderOf (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) = 9 := by
    rw [Subgroup.orderOf_coe, hg, hScard]
    norm_num
  obtain ⟨x, hx⟩ := hπ g
  have hdvd : 9 ∣ orderOf x := by
    have := orderOf_map_dvd π x
    rw [hx, hg9] at this
    exact this
  have hne : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨x ^ (orderOf x / 9), ?_⟩
  exact orderOf_pow_orderOf_div hne hdvd

theorem lemma27_psl2_eight {X N : Type*} [Group X] [Finite X] [Group N] [Finite N] {d : ℕ}
    (π : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))
    (hπ : Function.Surjective π) (ρ : X →* MulAut N) (hρ : Function.Injective ρ)
    (hN : Nat.card N = 2 ^ d) : 6 ≤ d := by
  obtain ⟨c, hc⟩ := exists_orderOf_nine_of_surjective_psl2_eight π hπ
  exact faithful_le_of_orderOf_nine ρ hρ hN hc

end CFSG.CGT.Timmesfeld75
