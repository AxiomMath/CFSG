module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMGeom

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup

section Generic

theorem isPSolvable_of_solvable {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (hX : Group.IsSolvable X) : CFSG.HallHigman.IsPSolvable p X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = p ∨ Nat.Coprime p (Nat.card (↥H ⧸ T))
  by_cases h : Nat.card (↥H ⧸ T) = p
  · exact Or.inl h
  · exact Or.inr ((Nat.coprime_primes hp hq).mpr (Ne.symm h))

theorem centralizes_of_card_le_thirteen_cube {H : Type*} [Group H] [Finite H] {R : Subgroup H}
    [R.Normal] (hR : IsPGroup 13 R) (hle : Nat.card R ≤ 13 ^ 3) {z : H} (hz : orderOf z = 5) :
    ∀ r ∈ R, z * r = r * z := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h5 : Nat.Prime 5 := by norm_num
  have hF : ∀ g ∈ zpowers z, ∀ s ∈ (R : Set H), g * s * g⁻¹ ∈ (R : Set H) := fun g _ s hs =>
    Subgroup.Normal.conj_mem inferInstance s hs g
  have hmod := ncard_modEq_fixed h5 hz hF
  set K : Subgroup H := R ⊓ centralizer ({z} : Set H) with hK
  have hset : {s | s ∈ (R : Set H) ∧ z * s = s * z} = (K : Set H) := by
    ext s
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, hK, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
  rw [hset] at hmod
  have hKR : K ≤ R := inf_le_left
  have hKp : IsPGroup 13 K := hR.to_le hKR
  obtain ⟨d, hd⟩ := hR.exists_card_eq
  obtain ⟨e, he⟩ := hKp.exists_card_eq
  have hmod' : 13 ^ d ≡ 13 ^ e [MOD 5] := by
    have h1 : (R : Set H).ncard = Nat.card R := by
      rw [← Nat.card_coe_set_eq]; rfl
    have h2 : (K : Set H).ncard = Nat.card K := by
      rw [← Nat.card_coe_set_eq]; rfl
    rw [h1, h2, hd, he] at hmod
    exact hmod
  have hd3 : d ≤ 3 := by
    by_contra hd3
    push Not at hd3
    have : 13 ^ 4 ≤ 13 ^ d := Nat.pow_le_pow_right (by norm_num) hd3
    rw [hd] at hle
    omega
  have hed : e ≤ d := by
    have hdvd : Nat.card K ∣ Nat.card R := Subgroup.card_dvd_of_le hKR
    rw [hd, he] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hed' : e = d := by
    interval_cases d <;> interval_cases e <;> simp_all [Nat.ModEq]
  have hcard : Nat.card R ≤ Nat.card K := by rw [hd, he, hed']
  have hKeq : K = R := Subgroup.eq_of_le_of_card_ge hKR hcard
  intro r hr
  have : r ∈ K := hKeq ▸ hr
  exact ((Subgroup.mem_inf.1 this).2 |> Subgroup.mem_centralizer_singleton_iff.1).symm

theorem exists_mul_centralizer_of_zStar {H : Type*} [Group H] {v : H} (hv : v * v = 1)
    {N : Subgroup H} (hodd : Odd (Nat.card N)) (hN : ∀ g : H, g * v * g⁻¹ * v⁻¹ ∈ N) (h : H) :
    ∃ m ∈ N, ∃ k ∈ centralizer ({v} : Set H), h = m * k := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  set n0 : H := h * v * h⁻¹ * v⁻¹ with hn0
  have hn0N : n0 ∈ N := hN h
  have ht : h * v * h⁻¹ = n0 * v := by
    rw [hn0]; group
  have ht2 : (n0 * v) * (n0 * v) = 1 := by
    rw [← ht]
    calc h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ := by group
      _ = 1 := by rw [hv]; group
  have hinv : v * n0 * v = n0⁻¹ := by
    have h1 : n0 * (v * n0 * v) = 1 := by
      calc n0 * (v * n0 * v) = (n0 * v) * (n0 * v) := by group
        _ = 1 := ht2
    exact eq_inv_of_mul_eq_one_right h1
  have hodd0 : Odd (orderOf n0) := by
    have hd : orderOf (⟨n0, hn0N⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have : orderOf (⟨n0, hn0N⟩ : N) = orderOf n0 := by
      rw [← Subgroup.orderOf_coe]
    rw [this] at hd
    exact Odd.of_dvd_nat hodd hd
  obtain ⟨a, ha⟩ := hodd0
  set m : H := n0 ^ (a + 1) with hm
  have hmN : m ∈ N := N.pow_mem hn0N _
  have hmm : m * m = n0 := by
    calc m * m = n0 ^ (a + 1 + (a + 1)) := (pow_add n0 (a + 1) (a + 1)).symm
      _ = n0 ^ (orderOf n0) * n0 := by
          rw [show a + 1 + (a + 1) = orderOf n0 + 1 by omega, pow_succ]
      _ = n0 := by rw [pow_orderOf_eq_one, one_mul]
  have hvm : v * m * v = m⁻¹ := by
    have hconj : ∀ j : ℕ, v * n0 ^ j * v = (n0⁻¹) ^ j := by
      intro j
      induction j with
      | zero => simpa using hv
      | succ j ih =>
        calc v * n0 ^ (j + 1) * v = (v * n0 ^ j * v) * (v * n0 * v) := by
              rw [pow_succ]
              calc v * (n0 ^ j * n0) * v = v * n0 ^ j * (v * v) * n0 * v := by
                    rw [hv]; group
                _ = (v * n0 ^ j * v) * (v * n0 * v) := by group
          _ = (n0⁻¹) ^ (j + 1) := by rw [ih, hinv, pow_succ]
    rw [hm, hconj, inv_pow]
  have hmv : m * v * m⁻¹ = n0 * v := by
    have hvm' : v * m⁻¹ * v = m := by
      calc v * m⁻¹ * v = (v * m * v)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, hvinv]; group
        _ = m := by rw [hvm, inv_inv]
    calc m * v * m⁻¹ = m * (v * m⁻¹ * v) * v := by
          calc m * v * m⁻¹ = m * (v * m⁻¹ * (v * v)) := by rw [hv]; group
            _ = m * (v * m⁻¹ * v) * v := by group
      _ = m * m * v := by rw [hvm']
      _ = n0 * v := by rw [hmm]
  refine ⟨m, hmN, m⁻¹ * h, ?_, by group⟩
  have h3 : (m⁻¹ * h) * v * (m⁻¹ * h)⁻¹ = v := by
    calc (m⁻¹ * h) * v * (m⁻¹ * h)⁻¹ = m⁻¹ * (h * v * h⁻¹) * m := by group
      _ = v := by rw [ht, ← hmv]; group
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.1 h3)


theorem not_five_dvd_card_of_zStar {H : Type} [Group H] [Finite H]
    (hcore : ∀ K : Subgroup H, K.Normal → Nat.Coprime 13 (Nat.card K) → K = ⊥)
    (hsmall : ∀ R : Subgroup H, IsPGroup 13 R → Nat.card R ≤ 13 ^ 3)
    {v : H} (hv : v * v = 1) (hv1 : v ≠ 1)
    (hiso : ∀ g : H, (g * v * g⁻¹) * v = v * (g * v * g⁻¹) → g * v * g⁻¹ = v)
    (h5 : ¬ 5 ∣ Nat.card (centralizer ({v} : Set H))) : ¬ 5 ∣ Nat.card H := by
  classical
  intro hdvd
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar H v hv1 hv hiso
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 hdvd
  have hfr := exists_mul_centralizer_of_zStar hv hNodd hNc
  have hzN : z ∈ N := by
    let q : H →* H ⧸ N := QuotientGroup.mk' N
    let φ : centralizer ({v} : Set H) →* H ⧸ N := q.comp (centralizer ({v} : Set H)).subtype
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨m, hm, k, hk, rfl⟩ := hfr h
      refine ⟨⟨k, hk⟩, ?_⟩
      show q k = q (m * k)
      refine (QuotientGroup.eq).2 ?_
      simpa [mul_assoc] using hNn.conj_mem m hm k⁻¹
    have hdq : Nat.card (H ⧸ N) ∣ Nat.card (centralizer ({v} : Set H)) :=
      Subgroup.card_dvd_of_surjective (f := φ) hφ
    have hq5 : (q z) ^ 5 = 1 := by rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
    have hdiv : orderOf (q z) ∣ 5 := orderOf_dvd_of_pow_eq_one hq5
    have h1 : orderOf (q z) = 1 := by
      rcases (Nat.dvd_prime (by norm_num)).1 hdiv with h1 | h5'
      · exact h1
      · exfalso
        apply h5
        exact (h5' ▸ orderOf_dvd_natCard (q z)).trans hdq
    exact (QuotientGroup.eq_one_iff z).1 (orderOf_eq_one_iff.1 h1)
  have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hNps : CFSG.HallHigman.IsPSolvable 13 N := isPSolvable_of_solvable (by norm_num) hNsolv
  have hnormal : ∀ C : Subgroup N, (∀ e : N ≃* N, C.map e.toMonoidHom = C) → (C.map N.subtype).Normal := by
    intro C hC
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy' : MulAut.conjNormal g y ∈ C := by
      have := hC (MulAut.conjNormal g)
      rw [← this]
      exact Subgroup.mem_map_of_mem _ hy
    exact Subgroup.mem_map.2 ⟨MulAut.conjNormal g y, hy', by simp⟩
  have hNcore : CFSG.pPrimeCore 13 N = ⊥ := by
    have hK := hnormal (CFSG.pPrimeCore 13 N) (fun e => CFSG.pPrimeCore_map_iso 13 e)
    have hcop : Nat.Coprime 13 (Nat.card ((CFSG.pPrimeCore 13 N).map N.subtype)) := by
      rw [Subgroup.card_map_of_injective N.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card (p := 13) (G := N)
    have := hcore _ hK hcop
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 this
  have hchar : CFSG.IsCharacteristicP 13 N :=
    CFSG.HallHigman.isCharacteristicP_of_isPSolvable hNps hNcore
  haveI hRn : (CFSG.pCore 13 N |>.map N.subtype).Normal :=
    hnormal (CFSG.pCore 13 N) (fun e => CFSG.pCore_map_iso 13 e)
  have hRp : IsPGroup 13 ((CFSG.pCore 13 N).map N.subtype) :=
    (CFSG.pCore_isPGroup (p := 13) (G := N)).map N.subtype
  have hcen : ∀ r ∈ (CFSG.pCore 13 N).map N.subtype, z * r = r * z :=
    centralizes_of_card_le_thirteen_cube hRp (hsmall _ hRp) hz
  have hz' : (⟨z, hzN⟩ : N) ∈ Subgroup.centralizer ((CFSG.pCore 13 N : Subgroup N) : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hcen r (Subgroup.mem_map_of_mem _ hr)).symm
  have hzP : (⟨z, hzN⟩ : N) ∈ CFSG.pCore 13 N := hchar hz'
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 13) (G := N)) ⟨⟨z, hzN⟩, hzP⟩
  have hk' : z ^ (13 ^ k) = 1 := by
    have := congrArg (fun x : CFSG.pCore 13 N => ((x : N) : H)) hk
    simpa using this
  have h5k : 5 ∣ 13 ^ k := by rw [← hz]; exact orderOf_dvd_of_pow_eq_one hk'
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5k)
  omega

end Generic

end CFSG.HardMathSupport.Dickson.Sec6.I1431
