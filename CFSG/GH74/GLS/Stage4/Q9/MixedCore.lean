module

public import CFSG.GH74.GLS.Stage4.Q9.Rigidity
public import CFSG.GH74.GLS.Stage4.Q9.OddCore
public import CFSG.Assembly.OrderReductions.InvariantSylow

public section

namespace CFSG.GH74.GLS.Stage4.Q9

private theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(X ⊔ N) * Nat.card ↥(X ⊓ N) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card ↥(X ⊓ N) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

private theorem card_inf_eq_three_pow {G : Type*} [Group G] [Finite G] (O P : Subgroup G)
    (hP81 : Nat.card P = 81) (hPO : ∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O)
    (hG3 : (Nat.card G).factorization 3 ≤ 4) :
    Nat.card ↥(P ⊓ O) = 3 ^ (Nat.card O).factorization 3 := by
  have hle : P ≤ Subgroup.normalizer (O : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro o
    refine ⟨fun ho => hPO a ha o ho, fun ho => ?_⟩
    have := hPO a⁻¹ (inv_mem ha) _ ho
    simpa [mul_assoc] using this
  have hprod := card_sup_mul_card_inf_of_le_normalizer hle
  rw [hP81] at hprod
  have h0₁ : Nat.card ↥(P ⊔ O) ≠ 0 := Nat.card_pos.ne'
  have h0₂ : Nat.card ↥(P ⊓ O) ≠ 0 := Nat.card_pos.ne'
  have h0₃ : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hsup3 : (Nat.card ↥(P ⊔ O)).factorization 3 ≤ 4 :=
    ((Nat.factorization_le_iff_dvd h0₁ (Nat.card_pos (α := G)).ne').2
      (Subgroup.card_subgroup_dvd_card _) 3).trans hG3
  have hinf : Nat.card ↥(P ⊓ O) ∣ 3 ^ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ O ≤ P)
    rw [hP81] at this
    simpa using this
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hinf
  have h81 : (81 : ℕ).factorization 3 = 4 := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hs3 : (Nat.card ↥(P ⊓ O)).factorization 3 = s := by
    rw [hs, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hfac := congrArg (fun n => n.factorization 3) hprod
  simp only [Nat.factorization_mul h0₁ h0₂, Nat.factorization_mul (show (81 : ℕ) ≠ 0 by norm_num) h0₃,
    Finsupp.add_apply, h81, hs3] at hfac
  have hdvdO : Nat.card ↥(P ⊓ O) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_right
  have hsle : s ≤ (Nat.card O).factorization 3 := by
    have := (Nat.factorization_le_iff_dvd h0₂ h0₃).2 hdvdO 3
    rwa [hs3] at this
  rw [hs]
  congr 1
  omega

private theorem eq_three_pow_mul_five_pow {n : ℕ} (hn : n ≠ 0)
    (hprime : ∀ r : ℕ, r.Prime → r ∣ n → r = 3 ∨ r = 5) :
    n = 3 ^ n.factorization 3 * 5 ^ n.factorization 5 := by
  have hsupp : n.factorization.support ⊆ ({3, 5} : Finset ℕ) := by
    intro p hp
    have hp' : p ∈ n.primeFactors := by simpa using hp
    simpa using hprime p (Nat.prime_of_mem_primeFactors hp') (Nat.dvd_of_mem_primeFactors hp')
  calc n = n.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hn).symm
    _ = ∏ p ∈ ({3, 5} : Finset ℕ), p ^ n.factorization p :=
        Finsupp.prod_of_support_subset _ hsupp _ (fun p _ => pow_zero p)
    _ = 3 ^ n.factorization 3 * 5 ^ n.factorization 5 := by
        rw [Finset.prod_pair (by norm_num)]

private theorem card_inverted_mul_card_le {G : Type*} [Group G] [Finite G] (z : G)
    (O : Subgroup G) (hOodd : Odd (Nat.card O)) :
    Nat.card {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} *
      Nat.card ↥(O ⊓ Subgroup.centralizer ({z} : Set G)) ≤ Nat.card O := by
  classical
  obtain ⟨k, hk⟩ := hOodd
  let ψ : G → G := fun x => x * (z * x * z⁻¹)⁻¹
  have hψ1 : ∀ i : G, i ∈ O → z * i * z⁻¹ = i⁻¹ → ψ (i ^ (k + 1)) = i := by
    intro i hi hzi
    have h1 : z * i ^ (k + 1) * z⁻¹ = (i⁻¹) ^ (k + 1) := by
      rw [← hzi]
      exact (conj_pow (a := z) (b := i) (i := k + 1)).symm
    have h2 : i ^ (2 * k + 1) = 1 := by
      have : (⟨i, hi⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
      rw [hk] at this
      exact congrArg Subtype.val this
    show i ^ (k + 1) * (z * i ^ (k + 1) * z⁻¹)⁻¹ = i
    rw [h1, inv_pow, inv_inv, ← pow_add]
    have : k + 1 + (k + 1) = (2 * k + 1) + 1 := by ring
    rw [this, pow_succ, h2, one_mul]
  have hψ2 : ∀ x c : G, z * c * z⁻¹ = c → ψ (x * c) = ψ x := by
    intro x c hc
    show x * c * (z * (x * c) * z⁻¹)⁻¹ = x * (z * x * z⁻¹)⁻¹
    have : z * (x * c) * z⁻¹ = (z * x * z⁻¹) * c := by
      calc z * (x * c) * z⁻¹ = (z * x * z⁻¹) * (z * c * z⁻¹) := by group
        _ = (z * x * z⁻¹) * c := by rw [hc]
    rw [this, mul_inv_rev]
    group
  let C := O ⊓ Subgroup.centralizer ({z} : Set G)
  let g : {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} → O ⧸ C.subgroupOf O := fun i =>
    QuotientGroup.mk ⟨i.1 ^ (k + 1), Subgroup.pow_mem O i.2.1 _⟩
  have hinj : Function.Injective g := by
    intro i j h
    have h' := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h'
    have hcz := (Subgroup.mem_centralizer_singleton_iff.1 h'.2)
    set c : G := (i.1 ^ (k + 1))⁻¹ * j.1 ^ (k + 1) with hc
    have hcz' : z * c * z⁻¹ = c := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcz.symm
    have hj : j.1 ^ (k + 1) = i.1 ^ (k + 1) * c := by
      rw [hc]
      group
    apply Subtype.ext
    rw [← hψ1 j.1 j.2.1 j.2.2, hj, hψ2 _ _ hcz', hψ1 i.1 i.2.1 i.2.2]
  have hle : Nat.card {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} ≤ Nat.card (O ⧸ C.subgroupOf O) :=
    Nat.card_le_card_of_injective g hinj
  have hcard1 : Nat.card O = Nat.card (O ⧸ C.subgroupOf O) * Nat.card (C.subgroupOf O) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcard2 : Nat.card (C.subgroupOf O) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} * Nat.card C
      ≤ Nat.card (O ⧸ C.subgroupOf O) * Nat.card C := Nat.mul_le_mul_right _ hle
    _ = Nat.card O := by rw [hcard1, hcard2]

private theorem exists_conj_invariant_sylow {G : Type*} [Group G] [Finite G] {z : G}
    (hz : z * z = 1) (O : Subgroup G) (hOodd : Odd (Nat.card O))
    (hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O) (q : ℕ) [Fact q.Prime] :
    ∃ R : Subgroup G, R ≤ O ∧ Nat.card R = q ^ (Nat.card O).factorization q ∧
      ∀ r ∈ R, z * r * z⁻¹ ∈ R := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzz : ∀ a : G, z * (z * a * z⁻¹) * z⁻¹ = a := fun a => by
    rw [hzi]
    calc z * (z * a * z) * z = (z * z) * a * (z * z) := by group
      _ = a := by rw [hz]; group
  let σ : MulAut O :=
    { toFun := fun o => ⟨z * o * z⁻¹, hOz o o.2⟩
      invFun := fun o => ⟨z * o * z⁻¹, hOz o o.2⟩
      left_inv := fun o => Subtype.ext (hzz o)
      right_inv := fun o => Subtype.ext (hzz o)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hσ : Function.Involutive σ := fun o => Subtype.ext (hzz o)
  obtain ⟨S, hS⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_odd q hOodd σ hσ
  refine ⟨(S : Subgroup O).map O.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective O.subtype_injective]
    exact S.card_eq_multiplicity
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨σ x, ?_, rfl⟩
    rw [← hS]
    exact ⟨x, hx, rfl⟩

theorem mixed_core_trivial {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (O P : Subgroup G) (hOodd : Odd (Nat.card O)) (hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O)
    (hP3 : IsPGroup 3 P) (hP81 : Nat.card P = 81) (hPz : ∀ p ∈ P, p * z = z * p)
    (hPO : ∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O)
    (hCz : ∀ o ∈ O, z * o = o * z → o ∈ P)
    (hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card O → r = 3 ∨ r = 5)
    (h5 : (Nat.card O).factorization 5 ≤ 2)
    (hG3 : (Nat.card G).factorization 3 ≤ 4)
    (hC5 : ∀ r ∈ O, orderOf r = 5 → ¬ 27 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({r} : Set G))) :
    ∀ o ∈ O, z * o = o * z := by
  classical
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hz]
    exact pow_orderOf_eq_one z
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a, ha⟩ : ∃ a, a = (Nat.card O).factorization 3 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (Nat.card O).factorization 5 := ⟨_, rfl⟩
  have hO : Nat.card O = 3 ^ a * 5 ^ b := by
    rw [ha, hb]
    exact eq_three_pow_mul_five_pow Nat.card_pos.ne' hprime
  have hPOcard : Nat.card ↥(P ⊓ O) = 3 ^ a := by
    rw [ha]
    exact card_inf_eq_three_pow O P hP81 hPO hG3
  have hCeq : O ⊓ Subgroup.centralizer ({z} : Set G) = P ⊓ O := by
    ext o
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨ho, hc⟩
      exact ⟨hCz o ho hc.symm, ho⟩
    · rintro ⟨hp, ho⟩
      exact ⟨ho, hPz o hp⟩
  have hI := card_inverted_mul_card_le z O hOodd
  rw [hCeq, hPOcard, hO] at hI
  obtain ⟨R, hRO, hRcard, hRz⟩ := exists_conj_invariant_sylow hz2 O hOodd hOz 5
  rw [← hb] at hRcard
  have hRP : ∀ r ∈ R, r ∈ P → r = 1 := by
    intro r hrR hrP
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hP3) ⟨r, hrP⟩
    rw [Subgroup.orderOf_mk] at hn
    have hord : orderOf r ∣ 5 ^ b := by
      have := orderOf_dvd_natCard (⟨r, hrR⟩ : R)
      rwa [Subgroup.orderOf_mk, hRcard] at this
    rw [hn] at hord
    have hcop : Nat.Coprime (3 ^ n) (5 ^ b) := Nat.Coprime.pow _ _ (by norm_num)
    rw [← orderOf_eq_one_iff, hn]
    exact hcop.eq_one_of_dvd hord
  have hRfix : ∀ r ∈ R, z * r * z⁻¹ = r → r = 1 := by
    intro r hrR hr
    exact hRP r hrR (hCz r (hRO hrR) (mul_inv_eq_iff_eq_mul.1 hr))
  have hRinv : ∀ r ∈ R, z * r * z⁻¹ = r⁻¹ :=
    (inverted_of_fixedpointfree hz2 R hRz hRfix).1
  have hRI : ∀ i : G, i ∈ O → z * i * z⁻¹ = i⁻¹ → i ∈ R := by
    let f : R → {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} := fun r => ⟨r, hRO r.2, hRinv r r.2⟩
    have hf : Function.Injective f := fun x y h =>
      Subtype.ext (congrArg (fun s : {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} => s.1) h)
    have hcardle : Nat.card {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} ≤ Nat.card R := by
      rw [hRcard]
      have h3pos : 0 < 3 ^ a := by positivity
      rw [mul_comm (3 ^ a) (5 ^ b)] at hI
      exact Nat.le_of_mul_le_mul_right hI h3pos
    have hbij := hf.bijective_of_nat_card_le hcardle
    intro i hi hzi
    obtain ⟨r, hr⟩ := hbij.2 ⟨i, hi, hzi⟩
    have h : (r : G) = i := congrArg (fun s : {i : G // i ∈ O ∧ z * i * z⁻¹ = i⁻¹} => s.1) hr
    rw [← h]
    exact r.2
  have hPR : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R := by
    intro p hp r hr
    apply hRI _ (hPO p hp r (hRO hr))
    have h1 : z * p = p * z := (hPz p hp).symm
    calc z * (p * r * p⁻¹) * z⁻¹ = (z * p) * r * (z * p)⁻¹ := by group
      _ = (p * z) * r * (p * z)⁻¹ := by rw [h1]
      _ = p * (z * r * z⁻¹) * p⁻¹ := by group
      _ = (p * r * p⁻¹)⁻¹ := by rw [hRinv r hr]; group
  have hb0 : b = 0 := by
    by_contra hb0
    have h5R : 5 ∣ Nat.card R := by
      rw [hRcard]
      exact dvd_pow_self 5 hb0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 5 h5R
    have hrR : (x : G) ∈ R := x.2
    have hr5 : orderOf (x : G) = 5 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    have hPle : P ≤ Subgroup.normalizer (R : Set G) := by
      intro p hp
      rw [Subgroup.mem_normalizer_iff]
      intro r
      refine ⟨fun hr => hPR p hp r hr, fun hr => ?_⟩
      have := hPR p⁻¹ (inv_mem hp) _ hr
      simpa [mul_assoc] using this
    let ψ : P →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hPle)
    have hψk : ∀ y : P, y ∈ ψ.ker → ∀ r ∈ R, (y : G) * r = r * y := by
      intro y hy r hr
      have h := congrArg (fun f : MulAut R => ((f ⟨r, hr⟩ : R) : G)) (MonoidHom.mem_ker.1 hy)
      simp [ψ] at h
      exact mul_inv_eq_iff_eq_mul.1 h
    have hR25 : Nat.card R ∣ 25 := by
      rw [hRcard]
      exact (pow_dvd_pow 5 (by omega : b ≤ 2)).trans (by norm_num)
    have hker : Nat.card ψ.ker * ψ.ker.index = 81 := by
      rw [Subgroup.card_mul_index, hP81]
    have hidx : ψ.ker.index ∣ 480 := by
      rw [Subgroup.index_ker]
      exact (Subgroup.card_subgroup_dvd_card ψ.range).trans (card_mulAut_dvd_480 hR25)
    have hidx3 : ψ.ker.index ∣ 3 := by
      have h81 : ψ.ker.index ∣ 81 := ⟨Nat.card ψ.ker, by rw [← hker]; ring⟩
      have := Nat.dvd_gcd h81 hidx
      simpa using this
    have hker27 : 27 ∣ Nat.card ψ.ker := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hidx3 with h | h
      · rw [h] at hker
        omega
      · rw [h] at hker
        omega
    have hsub : ψ.ker.map P.subtype ≤ P ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2 (hψk y hy x hrR)⟩
    have hdvd := Subgroup.card_dvd_of_le hsub
    rw [Subgroup.card_map_of_injective P.subtype_injective] at hdvd
    exact hC5 x (hRO hrR) hr5 (hker27.trans hdvd)
  have hPOO : P ⊓ O = O := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
    rw [hPOcard, hO, hb0]
    simp
  intro o ho
  have : o ∈ P ⊓ O := by
    rw [hPOO]
    exact ho
  exact (hPz o this.1).symm

end CFSG.GH74.GLS.Stage4.Q9
