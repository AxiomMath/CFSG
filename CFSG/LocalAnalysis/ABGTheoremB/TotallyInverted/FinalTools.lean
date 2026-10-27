module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalBasic
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport
import CFSG.Walter.Transitivity.Coprime
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

theorem odd_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup p X) : Odd (Nat.card X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

theorem odd_orderOf_of_mem {X : Subgroup G} (hX : Odd (Nat.card X)) {u : G} (hu : u ∈ X) :
    Odd (orderOf u) :=
  hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hu)

theorem exists_pow_sq_eq {u : G} (hu : Odd (orderOf u)) : ∃ m : ℕ, (u ^ 2) ^ m = u := by
  obtain ⟨m, hm⟩ := hu
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show 2 * (m + 1) = orderOf u + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

theorem mem_of_sq_mem {u : G} {X : Subgroup G} (hu : Odd (orderOf u)) (h : u ^ 2 ∈ X) :
    u ∈ X := by
  obtain ⟨m, hm⟩ := exists_pow_sq_eq hu
  rw [← hm]
  exact X.pow_mem h _

theorem eq_one_of_conj_eq_inv_of_commute {t u : G} (hu : Odd (orderOf u))
    (hinv : t * u * t⁻¹ = u⁻¹) (hcomm : t * u = u * t) : u = 1 := by
  have h1 : u = u⁻¹ := by rw [← hinv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : u ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel u
  have := mem_of_sq_mem (X := ⊥) hu (by rw [h2]; exact Subgroup.one_mem _)
  exact Subgroup.mem_bot.mp this

theorem commute_of_sq_commute {u a : G} (hu : Odd (orderOf u)) (h : u ^ 2 * a = a * u ^ 2) :
    u * a = a * u := by
  obtain ⟨m, hm⟩ := exists_pow_sq_eq hu
  have hc : Commute (u ^ 2) a := h
  have := (hc.pow_left m).eq
  rwa [hm] at this

theorem commute_of_inverted {t u a : G} (hu : Odd (orderOf u)) (hinv : t * u * t⁻¹ = u⁻¹)
    (ha : t * a = a * t) (hua : t * (u * a * u⁻¹) = (u * a * u⁻¹) * t) : u * a = a * u := by
  have hta : t * a * t⁻¹ = a := by rw [ha, mul_inv_cancel_right]
  have htua : t * (u * a * u⁻¹) * t⁻¹ = u * a * u⁻¹ := by rw [hua, mul_inv_cancel_right]
  have hconj : t * (u * a * u⁻¹) * t⁻¹ = u⁻¹ * a * u := by
    calc t * (u * a * u⁻¹) * t⁻¹ = (t * u * t⁻¹) * (t * a * t⁻¹) * (t * u * t⁻¹)⁻¹ := by group
      _ = u⁻¹ * a * u := by rw [hinv, hta, inv_inv]
  have key : u ^ 2 * a = a * u ^ 2 := by
    have e : u * a * u⁻¹ = u⁻¹ * a * u := htua.symm.trans hconj
    rw [pow_two]
    calc u * u * a = u * (u * a * u⁻¹) * u := by group
      _ = u * (u⁻¹ * a * u) * u := by rw [e]
      _ = a * (u * u) := by group
  exact commute_of_sq_commute hu key

theorem mem_centralizer_of_inverted {t u : G} {A : Subgroup G} (hu : Odd (orderOf u))
    (hinv : t * u * t⁻¹ = u⁻¹) (hA : ∀ a ∈ A, t * a = a * t)
    (huA : u ∈ Subgroup.normalizer (A : Set G)) :
    u ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hua : u * a * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp huA a).mp ha
  exact (commute_of_inverted hu hinv (hA a ha) (hA _ hua)).symm

theorem mem_oddCoreIn_of_inverted {H : Subgroup G} {t u : G} (ht : t ∈ H)
    (hH : oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) = H) (hu : u ∈ H)
    (huo : Odd (orderOf u)) (hinv : t * u * t⁻¹ = u⁻¹) : u ∈ oddCoreIn H := by
  have hle : H ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
    inf_le_left.trans (le_normalizer_oddCoreIn H)
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreIn H)
    (H ⊓ Subgroup.centralizer ({t} : Set G)) hle
  have hu' : u ∈ ((oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) : Subgroup G) :
      Set G) := by rw [hH]; exact hu
  rw [hset] at hu'
  obtain ⟨o, ho, n, hn, rfl⟩ := hu'
  have htn : t * n * t⁻¹ = n := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hn.2
    rw [← this, mul_inv_cancel_right]
  have hto : t * o⁻¹ * t⁻¹ ∈ oddCoreIn H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H ht) _).mp
      ((oddCoreIn H).inv_mem ho)
  have hsq : (o * n) ^ 2 = o * (t * o⁻¹ * t⁻¹) := by
    have e : (o * n) * (t * (o * n) * t⁻¹)⁻¹ = o * (t * o⁻¹ * t⁻¹) := by
      calc (o * n) * (t * (o * n) * t⁻¹)⁻¹ = o * n * (t * o * t⁻¹ * (t * n * t⁻¹))⁻¹ := by
            group
        _ = o * (t * o⁻¹ * t⁻¹) := by rw [htn]; group
    rw [hinv, inv_inv, ← pow_two] at e
    exact e
  exact mem_of_sq_mem huo (by rw [hsq]; exact (oddCoreIn H).mul_mem ho hto)

theorem card_sup_mul_card_inf {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB).toEquiv
  change B.relIndex A = B.relIndex (A ⊔ B) at he
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr le_sup_right] at h1
  rw [← h1, ← he, ← h2, inf_comm]
  ring

theorem card_sup_of_inf_eq_bot {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hinf : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h := card_sup_mul_card_inf hAB
  rwa [hinf, Subgroup.card_bot, mul_one] at h

theorem mem_sup_iff_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hAB]
  exact Iff.rfl

theorem inf_sup_eq_of_le {A B M : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBM : B ≤ M) : M ⊓ (A ⊔ B) = (M ⊓ A) ⊔ B := by
  apply le_antisymm
  · rintro g ⟨hgM, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hAB).mp hg
    have haM : a ∈ M := by
      have := M.mul_mem hgM (M.inv_mem (hBM hb))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem_sup ⟨haM, ha⟩ hb
  · exact sup_le (inf_le_inf_left _ le_sup_left) (le_inf hBM le_sup_right)

section Coprime

variable [Finite G]

private theorem isPiSubgroup_of_isPGroup {p : ℕ} [hp : Fact p.Prime] {Z : Subgroup G}
    (hZ : IsPGroup p Z) : CFSG.IsPiSubgroup {(⟨p, hp.out⟩ : Nat.Primes)} Z := by
  intro q hq
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
  rw [hk] at hq
  have := (Nat.prime_dvd_prime_iff_eq q.2 hp.out).mp (q.2.dvd_of_dvd_pow hq)
  exact Set.mem_singleton_iff.mpr (Subtype.ext this)

private theorem isPGroup_of_isPiSubgroup {p : ℕ} [hp : Fact p.Prime] {Z : Subgroup G}
    (hZ : CFSG.IsPiSubgroup {(⟨p, hp.out⟩ : Nat.Primes)} Z) : IsPGroup p Z := by
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card Z).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd
    Nat.card_pos.ne' fun {d} hd hdZ => ?_⟩
  have h := hZ ⟨d, hd⟩ hdZ
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp h)

omit [Finite G] in
private theorem conjBy_eq_conjSub (S : Subgroup G) (c : G) : S.conjBy c = conjSub c S := rfl

theorem exists_le_conjSub_of_coprime {p : ℕ} [Fact p.Prime] {A K X B : Subgroup G}
    (hA : Nat.card A = 4) (hK : Odd (Nat.card K)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hX : IsSylowOf p X K) (hBK : B ≤ K) (hB : IsPGroup p B)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G), B ≤ conjSub c X := by
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    rw [hA, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_left.mpr hK).pow_left 2
  obtain ⟨S, hSK, hSπ, -, hXS, c, hc, hBS⟩ :=
    CFSG.Walter.Transitivity.exists_conjBy_of_coprime_action hAK hsolv hcop hX.le hBK
      (isPiSubgroup_of_isPGroup hX.isPGroup) (isPiSubgroup_of_isPGroup hB) hAX hAB
  have hSX : S = X := hX.eq_of_le hXS hSK (isPGroup_of_isPiSubgroup hSπ)
  rw [hSX, conjBy_eq_conjSub] at hBS
  exact ⟨c, hc, hBS⟩

theorem exists_conjSub_eq_of_coprime {p : ℕ} [Fact p.Prime] {A K X Y : Subgroup G}
    (hA : Nat.card A = 4) (hK : Odd (Nat.card K)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hX : IsSylowOf p X K) (hY : IsSylowOf p Y K) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G), conjSub c X = Y := by
  obtain ⟨c, hc, hYX⟩ := exists_le_conjSub_of_coprime hA hK hAK hX hY.le hY.isPGroup hAX hAY
  refine ⟨c, hc, (Subgroup.eq_of_le_of_card_ge hYX ?_).symm⟩
  rw [card_conjSub, hX.card_eq, hY.card_eq]

theorem exists_conjSub_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : IsSylowOf p P K) (hQ : IsSylowOf p Q K) : ∃ k ∈ K, conjSub k P = Q := by
  obtain ⟨S₁, rfl⟩ := hP
  obtain ⟨S₂, rfl⟩ := hQ
  obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq K S₁ S₂
  refine ⟨k, k.2, ?_⟩
  ext y
  rw [mem_conjSub_iff]
  simp only [Subgroup.mem_map, Sylow.coe_subgroup_smul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨u, hu, hu'⟩
    refine ⟨k * u * k⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, mul_assoc] using hu
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu' ⊢
      rw [hu']
      group
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_, hu, ?_⟩
    simp [MulAut.smul_def]

theorem exists_mul_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {H O X : Subgroup G}
    (hX : IsSylowOf p X O) (hOH : H ≤ Subgroup.normalizer (O : Set G)) {h : G} (hh : h ∈ H) :
    ∃ o ∈ O, ∃ n ∈ Subgroup.normalizer (X : Set G), o * n = h := by
  have hO : conjSub h O = O := conjSub_eq_self_iff.mpr (hOH hh)
  have hX' : IsSylowOf p (conjSub h X) O := hO ▸ isSylowOf_conjSub hX h
  obtain ⟨o, ho, hoX⟩ := exists_conjSub_eq_of_isSylowOf hX' hX
  refine ⟨o⁻¹, O.inv_mem ho, o * h, ?_, by group⟩
  rw [← conjSub_eq_self_iff, ← conjSub_conjSub, hoX]

end Coprime

section TDecomposition

variable {σ : Setting G}

theorem mem_comp {U : Subgroup G} {i : Fin 3} {u : G} :
    u ∈ comp σ U i ↔ u ∈ U ∧ σ.xs i * u = u * σ.xs i ∧
      σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹ := Iff.rfl

theorem comp_subset (U : Subgroup G) (i : Fin 3) : comp σ U i ⊆ U := fun _ hu => hu.1

theorem comp_mono {U V : Subgroup G} (h : U ≤ V) (i : Fin 3) : comp σ U i ⊆ comp σ V i :=
  fun _ hu => ⟨h hu.1, hu.2⟩

theorem one_mem_comp (U : Subgroup G) (i : Fin 3) : (1 : G) ∈ comp σ U i :=
  ⟨U.one_mem, by group, by group⟩

theorem mem_comp_inf {U V : Subgroup G} {i : Fin 3} {u : G} :
    u ∈ comp σ (U ⊓ V) i ↔ u ∈ comp σ U i ∧ u ∈ V :=
  ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩

variable [Finite G]

theorem x_ne_one (hσ : σ.IsValid) : σ.x ≠ 1 := fun h => by
  have := hσ.x_order
  rw [h, orderOf_one] at this
  omega

theorem x₂_ne_one (hσ : σ.IsValid) : σ.x₂ ≠ 1 := fun h => by
  have := hσ.x₂_order
  rw [h, orderOf_one] at this
  omega

theorem x_mul_x (hσ : σ.IsValid) : σ.x * σ.x = 1 := by
  rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]

theorem x₂_mul_x₂ (hσ : σ.IsValid) : σ.x₂ * σ.x₂ = 1 := by
  rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]

theorem x_inv (hσ : σ.IsValid) : σ.x⁻¹ = σ.x := inv_eq_of_mul_eq_one_right (x_mul_x hσ)

theorem x₂_inv (hσ : σ.IsValid) : σ.x₂⁻¹ = σ.x₂ := inv_eq_of_mul_eq_one_right (x₂_mul_x₂ hσ)

theorem xs_ne_one (hσ : σ.IsValid) (i : Fin 3) : σ.xs i ≠ 1 := by
  match i with
  | 0 => exact x_ne_one hσ
  | 1 => exact x₂_ne_one hσ
  | 2 =>
    intro h
    apply hσ.x_ne_x₂
    have h' : σ.x * σ.x₂ = 1 := h
    calc σ.x = σ.x * (σ.x₂ * σ.x₂) := by rw [x₂_mul_x₂ hσ, mul_one]
      _ = σ.x₂ := by rw [← mul_assoc, h', one_mul]

theorem xs_ne_xs_succ (hσ : σ.IsValid) (i : Fin 3) : σ.xs i ≠ σ.xs (i + 1) := by
  match i with
  | 0 => exact hσ.x_ne_x₂
  | 1 =>
    intro h
    have h' : σ.x₂ = σ.x * σ.x₂ := h
    exact x_ne_one hσ (by simpa using congrArg (· * σ.x₂⁻¹) h'.symm)
  | 2 =>
    intro h
    have h' : σ.x * σ.x₂ = σ.x := h
    exact x₂_ne_one hσ (by simpa using congrArg (σ.x⁻¹ * ·) h')

omit [Finite G] in
private theorem eq_one_or_eq_of_mem_zpowers {x g : G} (hx : orderOf x = 2)
    (hg : g ∈ Subgroup.zpowers x) : g = 1 ∨ g = x := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one i with h | h <;> rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (zpow_one x)

theorem isKleinFour_T (hσ : σ.IsValid) : IsKleinFour σ.T := by
  refine CFSG.Wreathed.isKleinFour_closure_pair hσ.x_order hσ.x₂_order hσ.commute ?_
  rw [Subgroup.disjoint_def]
  intro g h1 h2
  rcases eq_one_or_eq_of_mem_zpowers hσ.x_order h1 with h | rfl
  · exact h
  rcases eq_one_or_eq_of_mem_zpowers hσ.x₂_order h2 with h | h
  · exact h
  · exact absurd h hσ.x_ne_x₂

theorem card_T (hσ : σ.IsValid) : Nat.card σ.T = 4 :=
  (isKleinFour_T hσ).card_four

theorem xs_add_two (hσ : σ.IsValid) (i : Fin 3) : σ.xs (i + 2) = σ.xs i * σ.xs (i + 1) := by
  have h1 := x_mul_x hσ
  have h2 := x₂_mul_x₂ hσ
  match i with
  | 0 => rfl
  | 1 =>
    change σ.x = σ.x₂ * (σ.x * σ.x₂)
    rw [← mul_assoc, ← hσ.commute, mul_assoc, h2, mul_one]
  | 2 =>
    change σ.x₂ = σ.x * σ.x₂ * σ.x
    rw [mul_assoc, ← hσ.commute, ← mul_assoc, h1, one_mul]

theorem xs_mul_xs (hσ : σ.IsValid) (i : Fin 3) : σ.xs i * σ.xs i = 1 := by
  have h1 := x_mul_x hσ
  have h2 := x₂_mul_x₂ hσ
  match i with
  | 0 => exact h1
  | 1 => exact h2
  | 2 =>
    change σ.x * σ.x₂ * (σ.x * σ.x₂) = 1
    rw [mul_assoc, ← mul_assoc σ.x₂, ← hσ.commute, mul_assoc, h2, mul_one, h1]

theorem xs_inv (hσ : σ.IsValid) (i : Fin 3) : (σ.xs i)⁻¹ = σ.xs i :=
  inv_eq_of_mul_eq_one_right (xs_mul_xs hσ i)

theorem xs_comm (hσ : σ.IsValid) (i j : Fin 3) : σ.xs i * σ.xs j = σ.xs j * σ.xs i := by
  have hT := (isKleinFour_T hσ)
  have hc := hT.isMulCommutative
  have := hc.is_comm.comm ⟨_, xs_mem_T i⟩ ⟨_, xs_mem_T j⟩
  exact congrArg Subtype.val this

theorem conj_xs_add_two_of_mem_comp (hσ : σ.IsValid) {U : Subgroup G} {i : Fin 3} {u : G}
    (hu : u ∈ comp σ U i) : σ.xs (i + 2) * u * (σ.xs (i + 2))⁻¹ = u⁻¹ := by
  obtain ⟨-, h1, h2⟩ := hu
  have h1' : σ.xs i * u * (σ.xs i)⁻¹ = u := by rw [h1, mul_inv_cancel_right]
  rw [xs_add_two hσ]
  calc σ.xs i * σ.xs (i + 1) * u * (σ.xs i * σ.xs (i + 1))⁻¹ =
        σ.xs i * (σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹) * (σ.xs i)⁻¹ := by group
    _ = σ.xs i * u⁻¹ * (σ.xs i)⁻¹ := by rw [h2]
    _ = (σ.xs i * u * (σ.xs i)⁻¹)⁻¹ := by group
    _ = u⁻¹ := by rw [h1']

theorem mem_comp_iff' (hσ : σ.IsValid) {U : Subgroup G} {i : Fin 3} {u : G} :
    u ∈ comp σ U i ↔ u ∈ U ∧ σ.xs i * u = u * σ.xs i ∧
      σ.xs (i + 2) * u * (σ.xs (i + 2))⁻¹ = u⁻¹ := by
  refine ⟨fun hu => ⟨hu.1, hu.2.1, conj_xs_add_two_of_mem_comp hσ hu⟩, ?_⟩
  rintro ⟨hU, h1, h2⟩
  refine ⟨hU, h1, ?_⟩
  have h1' : σ.xs i * u * (σ.xs i)⁻¹ = u := by rw [h1, mul_inv_cancel_right]
  have e : σ.xs (i + 1) = σ.xs i * σ.xs (i + 2) := by
    rw [xs_add_two hσ, ← mul_assoc, xs_mul_xs hσ, one_mul]
  rw [e]
  calc σ.xs i * σ.xs (i + 2) * u * (σ.xs i * σ.xs (i + 2))⁻¹ =
        σ.xs i * (σ.xs (i + 2) * u * (σ.xs (i + 2))⁻¹) * (σ.xs i)⁻¹ := by group
    _ = σ.xs i * u⁻¹ * (σ.xs i)⁻¹ := by rw [h2]
    _ = (σ.xs i * u * (σ.xs i)⁻¹)⁻¹ := by group
    _ = u⁻¹ := by rw [h1']

omit [Finite G] in
private theorem comm_iff_conj {a u : G} : a * u = u * a ↔ a * u * a⁻¹ = u := by
  rw [mul_inv_eq_iff_eq_mul]

omit [Finite G] in
theorem comp_zero_eq (U : Subgroup G) : comp σ U 0 = fourInverted U σ.x σ.x₂ := by
  ext u
  simp only [comp, fourInverted, Set.mem_ofPred_eq]
  rw [comm_iff_conj]
  rfl

theorem comp_one_eq (hσ : σ.IsValid) (U : Subgroup G) :
    comp σ U 1 = fourInverted U σ.x₂ σ.x := by
  ext u
  rw [mem_comp_iff' hσ]
  simp only [fourInverted, Set.mem_ofPred_eq]
  rw [comm_iff_conj]
  rfl

omit [Finite G] in
theorem comp_two_eq (U : Subgroup G) : comp σ U 2 = fourInverted U (σ.x * σ.x₂) σ.x := by
  ext u
  simp only [comp, fourInverted, Set.mem_ofPred_eq]
  rw [comm_iff_conj]
  rfl

theorem coe_eq_mul_comp (hσ : σ.IsValid) {U : Subgroup G} (hU : Odd (Nat.card U))
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) :
    (U : Set G) =
      ((U ⊓ σ.C : Subgroup G) : Set G) * comp σ U 0 * comp σ U 1 * comp σ U 2 := by
  have := isKleinFour_T hσ
  rw [comp_zero_eq, comp_one_eq hσ, comp_two_eq]
  exact (four_group_T_decomposition hU hTU σ.x_mem_T σ.x₂_mem_T (x_ne_one hσ) (x₂_ne_one hσ)
    hσ.x_ne_x₂).2

theorem exists_mul_comp (hσ : σ.IsValid) {U : Subgroup G} (hU : Odd (Nat.card U))
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) {u : G} (hu : u ∈ U) :
    ∃ u₀ ∈ U ⊓ σ.C, ∃ u₁ ∈ comp σ U 0, ∃ u₂ ∈ comp σ U 1, ∃ u₃ ∈ comp σ U 2,
      u = u₀ * u₁ * u₂ * u₃ := by
  have hu' : u ∈ (U : Set G) := hu
  rw [coe_eq_mul_comp hσ hU hTU] at hu'
  obtain ⟨_, ⟨_, ⟨u₀, h₀, u₁, h₁, rfl⟩, u₂, h₂, rfl⟩, u₃, h₃, rfl⟩ := hu'
  exact ⟨u₀, h₀, u₁, h₁, u₂, h₂, u₃, h₃, rfl⟩

theorem le_of_comp_subset (hσ : σ.IsValid) {U B : Subgroup G} (hU : Odd (Nat.card U))
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) (hUC : U ⊓ σ.C ≤ B)
    (hcomp : ∀ i, comp σ U i ⊆ B) : U ≤ B := by
  intro u hu
  obtain ⟨u₀, h₀, u₁, h₁, u₂, h₂, u₃, h₃, rfl⟩ := exists_mul_comp hσ hU hTU hu
  exact B.mul_mem (B.mul_mem (B.mul_mem (hUC h₀) (hcomp 0 h₁)) (hcomp 1 h₂)) (hcomp 2 h₃)

theorem coe_inf_Ns_eq (hσ : σ.IsValid) {U : Subgroup G} (hU : Odd (Nat.card U))
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) (i : Fin 3) :
    ((U ⊓ σ.Ns i : Subgroup G) : Set G) = ((U ⊓ σ.C : Subgroup G) : Set G) * comp σ U i := by
  have := isKleinFour_T hσ
  have h := (centralizer_eq_mul_fourInverted hU hTU (xs_mem_T i) (xs_mem_T (i + 1))
    (xs_ne_one hσ i) (xs_ne_one hσ (i + 1)) (xs_ne_xs_succ hσ i)).1
  have hf : fourInverted U (σ.xs i) (σ.xs (i + 1)) = comp σ U i := by
    ext u
    simp only [comp, fourInverted, Set.mem_ofPred_eq]
    rw [comm_iff_conj]
  rw [hf] at h
  exact h

end TDecomposition

end CFSG.ABGTheoremB.TotallyInverted.Sec11
