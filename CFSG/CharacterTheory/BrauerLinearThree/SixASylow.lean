module

public import CFSG.CharacterTheory.BrauerLinearThree.SixATorus
public import CFSG.CharacterTheory.BrauerLinearThree.LayerOrder

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.Open

open Finset in
theorem mem_zpowers_of_pow_orderOf_eq_one {α : Type*} [Group α] [Finite α] [IsCyclic α]
    {g x : α} (hx : x ^ orderOf g = 1) : x ∈ Subgroup.zpowers g := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set n := orderOf g with hn
  have hle := IsCyclic.card_pow_eq_one_le (α := α) (orderOf_pos g)
  have hsub : (Subgroup.zpowers g : Set α).toFinset ⊆ ({a : α | a ^ n = 1} : Finset α) := by
    intro a ha
    rw [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at ha
    obtain ⟨k, rfl⟩ := ha
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hn,
      pow_orderOf_eq_one, _root_.one_zpow]
  have hcard : (Subgroup.zpowers g : Set α).toFinset.card = n := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact Nat.card_zpowers g
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hxS : x ∈ ({a : α | a ^ n = 1} : Finset α) := by simp [hx]
  rw [← heq, Set.mem_toFinset] at hxS
  exact hxS

theorem conj_eq_of_conj_mem_zpowers {G : Type*} [Group G] {h n J : G} {k : ℕ} (hJ : h ^ k = J)
    (hJ2 : J * J = 1) (hJ1 : J ≠ 1) (hn : n * h * n⁻¹ ∈ Subgroup.zpowers h) :
    n * J * n⁻¹ = J := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hconj : n * J * n⁻¹ = J ^ i := by
    calc n * J * n⁻¹ = (n * h * n⁻¹) ^ k := by rw [conj_pow, hJ]
      _ = (h ^ i) ^ k := by rw [hi]
      _ = J ^ i := by
        rw [← hJ, ← zpow_natCast (h ^ i) k, ← _root_.zpow_mul, ← zpow_natCast h k,
          ← _root_.zpow_mul, mul_comm]
  have hord : orderOf J = 2 := orderOf_eq_prime (by rw [sq]; exact hJ2) hJ1
  rcases Int.emod_two_eq_zero_or_one i with h0 | h1
  · exfalso
    have hJi : J ^ i = 1 := by rw [← zpow_mod_orderOf, hord]; push_cast; rw [h0, zpow_zero]
    apply hJ1
    have h' : n * J * n⁻¹ = 1 := by rw [hconj, hJi]
    calc J = n⁻¹ * (n * J * n⁻¹) * n := by group
      _ = 1 := by rw [h']; group
  · rw [hconj, ← zpow_mod_orderOf, hord]
    push_cast
    rw [h1, zpow_one]

theorem relIndex_centralizer_normalizer_eq_two {G : Type*} [Group G] {y t : G} (hyy : y⁻¹ ≠ y)
    (ht : t * y * t⁻¹ = y⁻¹)
    (hN : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G),
      g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹) :
    (Subgroup.centralizer (Subgroup.zpowers y : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers y : Set G)) = 2 := by
  have ht' : t⁻¹ * y * t = y⁻¹ := by
    have h := congrArg (fun a => t⁻¹ * a⁻¹ * t) ht
    simp only [_root_.mul_inv_rev, inv_inv] at h
    rw [← h]
    group
  have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← conj_zpow, ht]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) i
    · intro ha
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      have : a = (t⁻¹ * y * t) ^ i := by
        rw [show t⁻¹ * y * t = t⁻¹ * y * t⁻¹⁻¹ by rw [inv_inv], conj_zpow, hi]
        group
      rw [this, ht']
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) i
  have hmemC : ∀ g : G, g ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) ↔
      g * y * g⁻¹ = y := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      rw [← h y (Subgroup.mem_zpowers y), mul_inv_cancel_right]
    · intro h a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hc : Commute g y := by
        show g * y = y * g
        calc g * y = g * y * g⁻¹ * g := by group
          _ = y * g := by rw [h]
      exact ((hc.zpow_right i).eq).symm
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htN⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hmemC, hmemC]
  have hbt : ((b * ⟨t, htN⟩ : Subgroup.normalizer (Subgroup.zpowers y : Set G)) : G) * y *
      ((b * ⟨t, htN⟩ : Subgroup.normalizer (Subgroup.zpowers y : Set G)) : G)⁻¹ =
        ((b : G) * y * (b : G)⁻¹)⁻¹ := by
    rw [Subgroup.coe_mul, _root_.mul_inv_rev]
    calc (b : G) * t * y * (t⁻¹ * (b : G)⁻¹) = (b : G) * (t * y * t⁻¹) * (b : G)⁻¹ := by group
      _ = ((b : G) * y * (b : G)⁻¹)⁻¹ := by rw [ht]; group
  rw [hbt]
  rcases hN b b.2 with hw | hw
  · rw [hw]
    exact Or.inr ⟨rfl, hyy⟩
  · rw [hw, inv_inv]
    exact Or.inl ⟨rfl, hyy⟩

theorem factorization_eq_of_dvd_add_one {g l q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : 2 ≤ q)
    (hrq : r ∣ q + 1) (hrl : ¬ r ∣ l) (hg : g ≠ 0) (hl : l ≠ 0)
    (hcard : g * l = q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1)) :
    g.factorization r = (q + 1).factorization r := by
  have hrq' : ¬ r ∣ q := fun h => hr.one_lt.ne' (Nat.dvd_one.mp (by
    have := Nat.dvd_sub hrq h
    rwa [Nat.add_sub_cancel_left] at this))
  have hrq1 : ¬ r ∣ q - 1 := by
    intro h
    have h2 : r ∣ 2 := by
      have := Nat.dvd_sub hrq h
      rwa [show q + 1 - (q - 1) = 2 by omega] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
  have hrq2 : ¬ r ∣ q ^ 2 + q + 1 := by
    intro h
    have h1 : r ∣ q * (q + 1) := dvd_mul_of_dvd_right hrq q
    have : r ∣ 1 := by
      have := Nat.dvd_sub h h1
      rwa [show q ^ 2 + q + 1 - q * (q + 1) = 1 by ring_nf; omega] at this
    exact hr.one_lt.ne' (Nat.dvd_one.mp this)
  have e3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have e2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hq0 : q ≠ 0 := by omega
  have hq10 : q - 1 ≠ 0 := by omega
  have hq3 : q ^ 2 + q + 1 ≠ 0 := by positivity
  have h1 : (g * l).factorization r = g.factorization r := by
    rw [Nat.factorization_mul hg hl, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hrl,
      add_zero]
  rw [← h1, hcard, e3, e2, Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd hrq', Nat.factorization_eq_zero_of_not_dvd hrq1,
    Nat.factorization_eq_zero_of_not_dvd hrq2, mul_zero, zero_add]

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem exists_semidihedral_sylow_of_element [Finite G] (hq : Nat.card F % 4 = 3)
    (A : GL (Fin 2) F) (hAord : orderOf A = 2 ^ ((Nat.card F + 1).factorization 2 + 1))
    (hA2 : A ^ 2 ^ (Nat.card F + 1).factorization 2 = -1)
    (hAconj : diagGL 1 (-1) * A * (diagGL 1 (-1))⁻¹ = A ^ Nat.card F) :
    4 ≤ (Nat.card F + 1).factorization 2 + 2 ∧
      ∃ (S : Sylow 2 G) (e' : SemidihedralGroup ((Nat.card F + 1).factorization 2 + 2) ≃*
          (S : Subgroup G)),
        (e' (CFSG.Semidihedral.r _) : G) = linearCentralizerHom φ A ∧
        (e' (CFSG.Semidihedral.r _) : G) ^
            (CFSG.Semidihedral.modulus ((Nat.card F + 1).factorization 2 + 2) / 2) = J ∧
        (e' (CFSG.Semidihedral.s _) : G) = invJ₁ φ := by
  obtain ⟨hm2, ⟨j, hj⟩, -, w, hw, hcard⟩ := semidihedral_arith hq
  have hAq : A ^ Nat.card F = A ^ (2 ^ (Nat.card F + 1).factorization 2 - 1) := by
    conv_lhs => rw [hj]
    rw [pow_add, pow_mul, ← hAord, pow_orderOf_eq_one, one_pow, one_mul]
  set m := (Nat.card F + 1).factorization 2 with hm
  set h := linearCentralizerHom φ A with hh
  have hhJ : h ^ 2 ^ m = J := by
    rw [hh, ← map_pow, hA2, linearCentralizerHom_neg_one φ hZ hZodd h2 hJ]
  have hJ1 : J ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hJ2 : J ^ 2 = 1 := by rw [← hJ]; exact pow_orderOf_eq_one J
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf h = 2 ^ (m + 1) := by
    apply orderOf_eq_prime_pow
    · rw [hhJ]; exact hJ1
    · rw [pow_succ, pow_mul, hhJ, hJ2]
  have hconj : invJ₁ φ * h * (invJ₁ φ)⁻¹ = h ^ (2 ^ m - 1) := by
    rw [invJ₁, hh, ← map_inv, ← map_mul, ← map_mul, hAconj, hAq, map_pow]
  have ht : invJ₁ φ ^ 2 = 1 := by rw [sq]; exact invJ₁_mul_self φ
  obtain ⟨hP, e, he₀, he₁⟩ := semidihedral_sup_zpowers hm2 hord ht hconj
  have hle : Subgroup.zpowers h ⊔ Subgroup.zpowers (invJ₁ φ) ≤
      Subgroup.centralizer ({J} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (linearCentralizerHom_mem φ A))
      (Subgroup.zpowers_le.mpr (linearCentralizerHom_mem φ _))
  have hC : Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card Z = 2 ^ (m + 2) * w := by
    rw [card_centralizer_J φ, hcard]
  obtain ⟨SC, hSC⟩ := exists_sylow_map_subtype_eq hle hP hw hC
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC hSC
  have hmod : CFSG.Semidihedral.modulus (m + 2) / 2 = 2 ^ m := by
    rw [CFSG.Semidihedral.modulus, show m + 2 - 1 = m + 1 by omega, pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]
  refine ⟨by omega, S, e.trans (MulEquiv.subgroupCongr hS.symm), ?_, ?_, ?_⟩
  · change ((e (CFSG.Semidihedral.r (m + 2)) : G)) = h
    exact he₀
  · rw [hmod]
    change ((e (CFSG.Semidihedral.r (m + 2)) : G)) ^ 2 ^ m = J
    rw [he₀, hhJ]
  · change ((e (CFSG.Semidihedral.s (m + 2)) : G)) = invJ₁ φ
    exact he₁

variable {K : Type} [Field K] [Finite K] {μ : Kˣ →* GL (Fin 2) F} (hμ : IsNonsplitTorus μ)

omit [Finite F] in
include hμ in
theorem exists_two_part (hq : Nat.card F % 4 = 3) :
    ∃ ζ : Kˣ, orderOf ζ = 2 ^ ((Nat.card F + 1).factorization 2 + 1) ∧
      μ ζ ^ 2 ^ (Nat.card F + 1).factorization 2 = -1 ∧
      ¬ 2 ^ ((Nat.card F + 1).factorization 2 + 2) ∣ Nat.card F ^ 2 - 1 := by
  obtain ⟨-, -, hdvd, -, -, -⟩ := semidihedral_arith hq
  set m := (Nat.card F + 1).factorization 2 with hm
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd_natCard (α := Kˣ) (d := 2 ^ (m + 1))
    (by rw [hμ.card]; exact hdvd)
  have hζ2 : ζ ^ 2 ^ m = -1 := by
    apply units_eq_neg_one_of_orderOf_eq_two
    rw [orderOf_pow_of_dvd (by positivity) ⟨2, by rw [hζ, pow_succ]⟩, hζ, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨ζ, hζ, by rw [← map_pow, hζ2, hμ.neg_one], ?_⟩
  intro h
  have hq1 : Nat.card F - 1 = 2 * (2 * (Nat.card F / 4) + 1) := by omega
  have hdec : Nat.card F + 1 = 2 ^ m * ((Nat.card F + 1) / 2 ^ m) :=
    (Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)).symm
  have hodd : ¬ 2 ∣ (Nat.card F + 1) / 2 ^ m := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have e2 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, Nat.card F = t + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [ht]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [e2, hq1, hdec] at h
  have h' : 2 ^ (m + 1) * 2 ∣ 2 ^ (m + 1) *
      ((2 * (Nat.card F / 4) + 1) * ((Nat.card F + 1) / 2 ^ m)) := by
    rw [← pow_succ]
    convert h using 1
    ring
  rw [Nat.mul_dvd_mul_iff_left (by positivity)] at h'
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h' with h'' | h''
  · omega
  · exact hodd h''

omit [Finite F] [Finite K] in
include hZ hμ in
theorem torus_conj_eq_or_eq_pow {n : G} (hn : J * n = n * J) (x y : Kˣ)
    (h : n * linearCentralizerHom φ (μ x) * n⁻¹ = linearCentralizerHom φ (μ y)) :
    linearCentralizerHom φ (μ y) = linearCentralizerHom φ (μ x) ∨
      linearCentralizerHom φ (μ y) = linearCentralizerHom φ (μ x) ^ Nat.card F := by
  obtain ⟨N, rfl⟩ := exists_linearCentralizerHom_eq φ hn
  rw [← map_inv, ← map_mul, ← map_mul] at h
  have hmem : N * μ x * N⁻¹ * (μ y)⁻¹ ∈ Z := (linearCentralizerHom_eq_iff φ _ _).mp h
  obtain ⟨c, hc⟩ := hZ hmem
  obtain ⟨c', hc'⟩ := hμ.scalar_mem c
  have hc'Z : μ c' ∈ Z := by rw [hc', hc]; exact hmem
  have hπc' : linearCentralizerHom φ (μ c') = 1 := (linearCentralizerHom_eq_one_iff φ _).mpr hc'Z
  have hconj : N * μ x * N⁻¹ = μ (c' * y) := by
    rw [map_mul, hc', hc, inv_mul_cancel_right]
  have hy : linearCentralizerHom φ (μ y) = linearCentralizerHom φ (μ (c' * y)) := by
    rw [map_mul, map_mul, hπc', one_mul]
  rcases hμ.fusion x (c' * y) N hconj with h1 | h1
  · left
    rw [hy, h1]
  · right
    rw [hy, h1, map_pow, map_pow]

omit [Finite F] in
include hZ hZodd h2 hμ in
theorem mem_zpowers_of_commute_torus {ζ : Kˣ} {k : ℕ} (hζ : orderOf ζ = 2 ^ k)
    (hk : ¬ 2 ^ (k + 1) ∣ Nat.card F ^ 2 - 1) {x : Kˣ}
    (hx : ∀ c : Fˣ, μ x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c) {g : G}
    (hgJ : J * g = g * J)
    (hg : g * linearCentralizerHom φ (μ x) = linearCentralizerHom φ (μ x) * g) {j : ℕ}
    (hgj : g ^ 2 ^ j = 1) : g ∈ Subgroup.zpowers (linearCentralizerHom φ (μ ζ)) := by
  have hcop : Nat.Coprime (Nat.card Z) (2 ^ j) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hZodd)
  obtain ⟨N, rfl, hN⟩ := exists_lift_pow_eq_one φ hZ hgJ hcop hgj
  obtain ⟨κ, hκ⟩ := hμ.commutant x hx N
    (commute_of_linearCentralizerHom_commute φ hZ hZodd h2 hg)
  have hκj : κ ^ 2 ^ j = 1 := hμ.injective (by rw [map_pow, hκ, hN, map_one])
  obtain ⟨i, -, hiκ⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hκj)
  have hcardK : orderOf κ ∣ Nat.card F ^ 2 - 1 := by
    rw [← hμ.card]
    exact orderOf_dvd_natCard κ
  have hik : i ≤ k := by
    by_contra hlt
    apply hk
    rw [hiκ] at hcardK
    exact (pow_dvd_pow 2 (by omega)).trans hcardK
  have hmem : κ ∈ Subgroup.zpowers ζ := by
    apply mem_zpowers_of_pow_orderOf_eq_one
    rw [hζ, ← orderOf_dvd_iff_pow_eq_one, hiκ]
    exact pow_dvd_pow 2 hik
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩
  rw [← map_zpow, ← map_zpow, ht, hκ]

omit [Finite F] in
include hZ hZodd h2 hJ hμ in
theorem map_sylow_eq_zpowers [Finite G] {ζ : Kˣ} {m : ℕ} (hζ : orderOf ζ = 2 ^ (m + 1))
    (hζJ : linearCentralizerHom φ (μ ζ) ^ 2 ^ m = J)
    (hk : ¬ 2 ^ (m + 2) ∣ Nat.card F ^ 2 - 1) {x : Kˣ}
    (hx : ∀ c : Fˣ, μ x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (S' : Sylow 2 (Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G)))
    (hle : Subgroup.zpowers (linearCentralizerHom φ (μ ζ)) ≤
      (S' : Subgroup (Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G))).map
        (Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G)).subtype) :
    (S' : Subgroup (Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G))).map
        (Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G)).subtype =
      Subgroup.zpowers (linearCentralizerHom φ (μ ζ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := (S' : Subgroup (Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G))).map
    (Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G)).subtype with hX
  set U := Subgroup.zpowers (linearCentralizerHom φ (μ ζ)) with hU
  have hXp : IsPGroup 2 X := S'.isPGroup'.map _
  have hXnil : Group.IsNilpotent X := hXp.isNilpotent
  by_contra hne
  have hK : U.subgroupOf X < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm _ hle
    intro z hz
    have : (⟨z, hz⟩ : X) ∈ U.subgroupOf X := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have hN := Group.normalizerCondition_of_isNilpotent (G := X) (U.subgroupOf X) hK
  obtain ⟨y, hyN, hyK⟩ := IsConcreteLE.exists_of_lt hN
  have hyU : (y : G) * linearCentralizerHom φ (μ ζ) * (y : G)⁻¹ ∈ U := by
    have hmem : (⟨linearCentralizerHom φ (μ ζ), hle (Subgroup.mem_zpowers _)⟩ : X) ∈
        U.subgroupOf X := Subgroup.mem_zpowers _
    exact (Subgroup.mem_normalizer_iff.mp hyN _).mp hmem
  have hJ1 : J ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hyJ : (y : G) * J * (y : G)⁻¹ = J :=
    conj_eq_of_conj_mem_zpowers hζJ (J_mul_self hJ) hJ1 hyU
  have hyJ' : J * (y : G) = (y : G) * J := by
    calc J * (y : G) = (y : G) * J * (y : G)⁻¹ * (y : G) := by rw [hyJ]
      _ = (y : G) * J := by group
  have hyH : (y : G) ∈ Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G) := by
    obtain ⟨w, -, hw⟩ := y.2
    rw [← hw]
    exact w.2
  have hyx : (y : G) * linearCentralizerHom φ (μ x) = linearCentralizerHom φ (μ x) * (y : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyH
  obtain ⟨j, hj⟩ := hXp y
  have hyj : (y : G) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  exact hyK (mem_zpowers_of_commute_torus φ hZ hZodd h2 hμ hζ hk hx hyJ' hyx hyj)

omit [Finite F] in
include hZ hZodd h2 hJ hμ in
theorem conj_eq_or_eq_pow_of_mem_normalizer [Finite G] {ζ : Kˣ} {m : ℕ}
    (hζ : orderOf ζ = 2 ^ (m + 1)) (hζJ : linearCentralizerHom φ (μ ζ) ^ 2 ^ m = J)
    (hk : ¬ 2 ^ (m + 2) ∣ Nat.card F ^ 2 - 1) {η : Kˣ}
    (hP : ∀ y' ∈ Subgroup.zpowers (linearCentralizerHom φ (μ η)), y' ≠ 1 →
      ∃ x : Kˣ, y' = linearCentralizerHom φ (μ x) ∧
        ∀ c : Fˣ, μ x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (hη1 : linearCentralizerHom φ (μ η) ≠ 1) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (Subgroup.zpowers (linearCentralizerHom φ (μ η)) : Set G)) :
    g * linearCentralizerHom φ (μ η) * g⁻¹ = linearCentralizerHom φ (μ η) ∨
      g * linearCentralizerHom φ (μ η) * g⁻¹ = linearCentralizerHom φ (μ η) ^ Nat.card F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y := linearCentralizerHom φ (μ η) with hy
  set h := linearCentralizerHom φ (μ ζ) with hh
  have hy'P : g * y * g⁻¹ ∈ Subgroup.zpowers y :=
    (Subgroup.mem_normalizer_iff.mp hg y).mp (Subgroup.mem_zpowers y)
  have hy'1 : g * y * g⁻¹ ≠ 1 := by
    intro h1
    apply hη1
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨x, hx, hxs⟩ := hP _ hy'P hy'1
  set H := Subgroup.centralizer ({linearCentralizerHom φ (μ x)} : Set G) with hH
  have hcomm : ∀ a b : Kˣ, linearCentralizerHom φ (μ a) * linearCentralizerHom φ (μ b) =
      linearCentralizerHom φ (μ b) * linearCentralizerHom φ (μ a) := by
    intro a b
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm a b]
  have hhH : h ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm ζ x
  have hghH : g * h * g⁻¹ ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff, ← hx]
    have := hcomm ζ η
    calc g * h * g⁻¹ * (g * y * g⁻¹) = g * (h * y) * g⁻¹ := by group
      _ = g * (y * h) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * (g * h * g⁻¹) := by group
  set U := Subgroup.zpowers h with hU
  set V := Subgroup.zpowers (g * h * g⁻¹) with hV
  have hUH : U ≤ H := Subgroup.zpowers_le.mpr hhH
  have hVH : V ≤ H := Subgroup.zpowers_le.mpr hghH
  have hJ1 : J ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hhord : orderOf h = 2 ^ (m + 1) := by
    apply orderOf_eq_prime_pow
    · rw [hζJ]; exact hJ1
    · rw [pow_succ, pow_mul, hζJ, sq, J_mul_self hJ]
  have hUp : IsPGroup 2 (U.subgroupOf H) := by
    apply IsPGroup.of_card (n := m + 1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv, Nat.card_zpowers, hhord]
  obtain ⟨SU, hSU⟩ := hUp.exists_le_sylow
  have hSUeq : (SU : Subgroup H).map H.subtype = U := by
    apply map_sylow_eq_zpowers φ hZ hZodd h2 hJ hμ hζ hζJ hk hxs SU
    intro z hz
    exact ⟨⟨z, hUH hz⟩, hSU hz, rfl⟩
  have hSUcard : Nat.card SU = 2 ^ (m + 1) := by
    rw [← hhord, ← Nat.card_zpowers, ← hU, ← hSUeq,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hVcard : Nat.card (V.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv, Nat.card_zpowers,
      ← Sylow.card_eq_multiplicity SU, hSUcard, ← hhord]
    have := MulEquiv.orderOf_eq (MulAut.conj g) h
    rwa [MulAut.conj_apply] at this
  set SV : Sylow 2 H := Sylow.ofCard (V.subgroupOf H) hVcard with hSV
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H SV SU
  have h1 := Subgroup.smul_mem_pointwise_smul (⟨g * h * g⁻¹, hghH⟩ : H) (MulAut.conj c)
    (SV : Subgroup H) (by rw [hSV, Sylow.coe_ofCard]; exact Subgroup.mem_zpowers _)
  rw [MulAut.smul_def, MulAut.conj_apply] at h1
  have h2' : (c * ⟨g * h * g⁻¹, hghH⟩ * c⁻¹ : H) ∈ (SU : Subgroup H) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact h1
  have h3 : ((c * ⟨g * h * g⁻¹, hghH⟩ * c⁻¹ : H) : G) ∈ U := by
    rw [← hSUeq]
    exact ⟨_, h2', rfl⟩
  set n := (c : G) * g with hn
  have hnh : n * h * n⁻¹ ∈ U := by
    have : n * h * n⁻¹ = ((c * ⟨g * h * g⁻¹, hghH⟩ * c⁻¹ : H) : G) := by
      rw [hn]
      push_cast
      group
    rw [this]
    exact h3
  have hnJ : n * J * n⁻¹ = J := conj_eq_of_conj_mem_zpowers hζJ (J_mul_self hJ) hJ1 hnh
  have hnJ' : J * n = n * J := by
    calc J * n = n * J * n⁻¹ * n := by rw [hnJ]
      _ = n * J := by group
  have hcx : (c : G) * linearCentralizerHom φ (μ x) = linearCentralizerHom φ (μ x) * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hny : n * y * n⁻¹ = linearCentralizerHom φ (μ x) := by
    calc n * y * n⁻¹ = (c : G) * (g * y * g⁻¹) * (c : G)⁻¹ := by rw [hn]; group
      _ = (c : G) * linearCentralizerHom φ (μ x) * (c : G)⁻¹ := by rw [hx]
      _ = linearCentralizerHom φ (μ x) := by rw [hcx, mul_inv_cancel_right]
  rcases torus_conj_eq_or_eq_pow φ hZ hμ hnJ' η x hny with h4 | h4
  · left
    rw [hx, h4]
  · right
    rw [hx, h4]

include φ hZ hZodd h2 hJ hμ in
theorem exists_torus_sylow_relIndex_eq_two [Finite G] (hq : Nat.card F % 4 = 3)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hrq : r ∣ Nat.card F + 1) :
    ∃ (η : Kˣ) (P : Sylow r G),
      (P : Subgroup G) = Subgroup.zpowers (linearCentralizerHom φ (μ η)) ∧
      orderOf (linearCentralizerHom φ (μ η)) = r ^ (Nat.card F + 1).factorization r ∧
      (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2 := by
  have hr : r.Prime := Fact.out
  set q := Nat.card F with hqdef
  set a := (q + 1).factorization r with ha
  have hq3 : 3 ≤ q := by omega
  have hrq1 : ¬ r ∣ q - 1 := by
    intro h
    have h2' : r ∣ 2 := by
      have := Nat.dvd_sub hrq h
      rwa [show q + 1 - (q - 1) = 2 by omega] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2')
  have hrZ : ¬ r ∣ Nat.card Z := fun h => hrq1 (h.trans (card_Z_dvd hZ))
  have e2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    rw [ht]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hra : r ^ a ∣ Nat.card Kˣ := by
    rw [hμ.card, e2]
    exact (Nat.ordProj_dvd _ _).trans (dvd_mul_left _ _)
  obtain ⟨η, hη⟩ := exists_orderOf_eq_of_dvd_natCard hra
  set y := linearCentralizerHom φ (μ η) with hy
  have ha1 : 1 ≤ a := Nat.Prime.factorization_pos_of_dvd hr (by omega) hrq
  have hyord : orderOf y = r ^ a := by
    obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [ha']
    apply orderOf_eq_prime_pow
    · intro h
      have hmem : μ (η ^ r ^ a') ∈ Z := by
        rw [← linearCentralizerHom_eq_one_iff φ, map_pow, map_pow]
        exact h
      have h1 : (μ (η ^ r ^ a')) ^ Nat.card Z = 1 := by
        have := pow_card_eq_one' (x := (⟨_, hmem⟩ : Z))
        exact congrArg Subtype.val this
      have h2' : η ^ (r ^ a' * Nat.card Z) = 1 :=
        hμ.injective (by rw [pow_mul, map_pow, h1, map_one])
      have h3 := orderOf_dvd_of_pow_eq_one h2'
      rw [hη, ha', pow_succ] at h3
      exact hrZ (Nat.dvd_of_mul_dvd_mul_left (pow_pos hr.pos a') h3)
    · rw [← ha', hy, ← map_pow, ← map_pow, ← hη, pow_orderOf_eq_one, map_one, map_one]
  have hvG : (Nat.card G).factorization r = a :=
    factorization_eq_of_dvd_add_one hr hr2 (by omega) hrq hrZ Nat.card_pos.ne' Nat.card_pos.ne'
      hcard
  refine ⟨η, Sylow.ofCard (Subgroup.zpowers y) (by rw [Nat.card_zpowers, hyord, hvG]),
    Sylow.coe_ofCard _ _, hyord, ?_⟩
  change (Subgroup.centralizer (Subgroup.zpowers y : Set G)).relIndex
    (Subgroup.normalizer (Subgroup.zpowers y : Set G)) = 2
  have hyq : y ^ q = y⁻¹ := by
    have h1 : y ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hyord ▸ Nat.ordProj_dvd _ _)
    rw [pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    exact (Nat.one_lt_pow (by omega) hr.one_lt).ne' hyord.symm
  have hyy : y⁻¹ ≠ y := by
    intro h
    have hsq : y ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel y
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [hyord] at hdvd
    have : r ∣ 2 := (dvd_pow_self r (by omega)).trans hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)
  have ht : invJ₁ φ * y * (invJ₁ φ)⁻¹ = y⁻¹ := by
    rw [invJ₁, hy, ← map_inv, ← map_mul, ← map_mul, hμ.frob, map_pow, map_pow, ← hy, hyq]
  obtain ⟨ζ, hζ, hζ2, hk⟩ := exists_two_part hμ hq
  have hζJ : linearCentralizerHom φ (μ ζ) ^ 2 ^ (q + 1).factorization 2 = J := by
    rw [← map_pow, hζ2, linearCentralizerHom_neg_one φ hZ hZodd h2 hJ]
  have hP' : ∀ y' ∈ Subgroup.zpowers y, y' ≠ 1 →
      ∃ x : Kˣ, y' = linearCentralizerHom φ (μ x) ∧
        ∀ c : Fˣ, μ x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    intro y' hy' hy'1
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    refine ⟨η ^ i, by rw [hy, map_zpow, map_zpow], fun c hc => hy'1 ?_⟩
    have hc1 : c ^ (q - 1) = 1 := by
      have := pow_card_eq_one' (x := c)
      rwa [Nat.card_units] at this
    have h1 : (η ^ i) ^ (q - 1) = 1 := by
      apply hμ.injective
      rw [map_pow, hc, ← map_pow, hc1, map_one, map_one]
    have h2' : (η ^ i) ^ r ^ a = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hη,
        pow_orderOf_eq_one, _root_.one_zpow]
    have hcop : Nat.Coprime (q - 1) (r ^ a) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrq1).symm
    have h3 : η ^ i = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h1, h2'⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    rw [hy, ← map_zpow, ← map_zpow, h3, map_one, map_one]
  have hN : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G),
      g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹ := by
    intro g hg
    rcases conj_eq_or_eq_pow_of_mem_normalizer φ hZ hZodd h2 hJ hμ hζ hζJ hk hP' hy1 hg with
      h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hyq)
  exact relIndex_centralizer_normalizer_eq_two hyy ht hN

end CFSG.BrauerLinearThree
