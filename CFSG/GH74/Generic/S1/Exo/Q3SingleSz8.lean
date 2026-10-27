module

public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.GH74.Filter.ClassicalOdd.Basic
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.GH74.GLS Subgroup
open CFSG.GH74.Filter.ClassicalOdd
open CFSG.LieType.Ree

section SylowU

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem card_suzukiU_eq' (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiU a K) = 2 ^ (Nat.card (suzukiGroup a K)).factorization 2 := by
  rw [(suzuki_unipotent_structure hK).2.1, suzuki_order hK]
  set q := 2 ^ (2 * a + 1) with hq
  have h2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : 2 ∣ q := dvd_pow_self 2 (by omega)
  have hq0 : q ^ 2 ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by omega
  have hodd1 : ¬ 2 ∣ q - 1 := by
    have h : ∀ m : ℕ, 2 ∣ m → 2 ≤ m → ¬ 2 ∣ m - 1 := by omega
    exact h q hq2 h2
  have hodd2 : ¬ 2 ∣ q ^ 2 + 1 := by
    have h : ∀ m : ℕ, 2 ∣ m → ¬ 2 ∣ m + 1 := by omega
    exact h _ (dvd_pow hq2 two_ne_zero)
  rw [Nat.factorization_mul (mul_ne_zero hq0 hq1) (by positivity), Nat.factorization_mul hq0 hq1,
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd1,
    Nat.factorization_eq_zero_of_not_dvd hodd2, add_zero, add_zero, hq, ← pow_mul,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    smul_eq_mul, mul_one, mul_comm]


theorem exists_conj_mem_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1))
    {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) (ψ : Q →* suzukiGroup a K) :
    ∃ g : suzukiGroup a K, ∀ x : Q, g⁻¹ * ψ x * g ∈ suzukiU a K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U' : Sylow 2 (suzukiGroup a K) := Sylow.ofCard (suzukiU a K) (card_suzukiU_eq' hK)
  have hrange : IsPGroup 2 ψ.range := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    obtain ⟨n, hn⟩ := hQ x
    exact ⟨n, Subtype.ext (by simp [← map_pow, hn])⟩
  obtain ⟨P, hP⟩ := hrange.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) U' P
  refine ⟨g, fun x => ?_⟩
  have hx : ψ x ∈ (P : Subgroup (suzukiGroup a K)) := hP ⟨x, rfl⟩
  rw [← hg] at hx
  change ψ x ∈ ((g • U' : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) at hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  have h2 : g⁻¹ * ψ x * g ∈ (U' : Subgroup (suzukiGroup a K)) := by
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hx
  exact h2

end SylowU

theorem no_q8_of_suzukiGroup_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (ψ : Q8 →* suzukiGroup 1 K) (hψ : Function.Injective ψ) :
    False := by
  have hQ : IsPGroup 2 Q8 := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_eq_fintype_card, show Fintype.card Q8 = 8 from QuaternionGroup.card (n := 2)]
    norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_suzukiU hK hQ ψ
  let φ : Q8 →* suzukiGroup 1 K := (MulAut.conj g⁻¹).toMonoidHom.comp ψ
  have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective.comp hψ
  have hφU : ∀ x, φ x ∈ suzukiU 1 K := fun x => by
    simpa [φ, MulAut.conj_apply, mul_assoc] using hg x
  have hii : (QuaternionGroup.a 1 : Q8) * QuaternionGroup.a 1 = QuaternionGroup.a 2 := by decide
  have hjj : (QuaternionGroup.xa 0 : Q8) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 := by decide
  have hz1 : (QuaternionGroup.a 2 : Q8) ≠ 1 := by decide
  have hij : (QuaternionGroup.a 1 : Q8) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  obtain ⟨u₁, v₁, h1⟩ := (mem_suzukiU_iff hK).1 (hφU (QuaternionGroup.a 1))
  obtain ⟨u₂, v₂, h2⟩ := (mem_suzukiU_iff hK).1 (hφU (QuaternionGroup.xa 0))
  have h2K : (2 : K) = 0 := (suzuki_frob_data 1 hK).1
  have hsq : ∀ u v : K, suzukiSElt 1 K u v * suzukiSElt 1 K u v =
      suzukiSElt 1 K 0 (u ^ 2 ^ (1 + 1) * u) := by
    intro u v
    rw [suzukiSElt_mul hK]
    congr 1
    · linear_combination u * h2K
    · linear_combination v * h2K
  have hsq1 : suzukiSElt 1 K 0 (u₁ ^ 2 ^ (1 + 1) * u₁) = φ (QuaternionGroup.a 2) := by
    rw [← hii, map_mul, ← h1, hsq]
  have hsq2 : suzukiSElt 1 K 0 (u₂ ^ 2 ^ (1 + 1) * u₂) = φ (QuaternionGroup.a 2) := by
    rw [← hjj, map_mul, ← h2, hsq]
  have hne : u₁ ^ 2 ^ (1 + 1) * u₁ ≠ 0 := by
    intro h0
    apply hz1
    apply hφ
    rw [← hsq1, h0, suzukiSElt_zero_zero hK, map_one]
  have heq : u₁ ^ 2 ^ (1 + 1) * u₁ = u₂ ^ 2 ^ (1 + 1) * u₂ := by
    have := (suzukiSElt_inj (a := 1) (K := K)).1 (hsq1.trans hsq2.symm)
    exact this.2
  have hu₁ : u₁ ≠ 0 := by
    intro h0
    apply hne
    rw [h0]
    simp
  have hu₂ : u₂ ≠ 0 := by
    intro h0
    apply hne
    rw [heq, h0]
    simp
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 8 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  have h7 : ∀ x : K, x ≠ 0 → x ^ 7 = 1 := fun x hx => by
    have := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [hcard] at this
  have h15 : ∀ x : K, x ≠ 0 → x ^ 15 = x := fun x hx => by
    calc x ^ 15 = (x ^ 7) ^ 2 * x := by ring
      _ = x := by rw [h7 x hx]; ring
  have hu : u₁ = u₂ := by
    have e5 : ∀ x : K, x ^ 2 ^ (1 + 1) * x = x ^ 5 := fun x => by
      rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
      ring
    rw [e5, e5] at heq
    calc u₁ = u₁ ^ 15 := (h15 u₁ hu₁).symm
      _ = (u₁ ^ 5) ^ 3 := by ring
      _ = (u₂ ^ 5) ^ 3 := by rw [heq]
      _ = u₂ ^ 15 := by ring
      _ = u₂ := h15 u₂ hu₂
  apply hij
  apply hφ
  rw [map_mul, map_mul, ← h1, ← h2, suzukiSElt_mul hK, suzukiSElt_mul hK, hu]
  congr 1
  rw [add_comm v₁ v₂]

theorem no_q8_of_twistedB2 {S : Type} [Group S]
    (h : LieModel S .twistedB2 0 2 3) : ¬ ∃ ψ : Q8 →* S, Function.Injective ψ := by
  rintro ⟨ψ, hψ⟩
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain rfl : a = 1 := by omega
    exact no_q8_of_suzukiGroup_one (by rw [hK]) (e.toMonoidHom.comp ψ) (e.injective.comp hψ)

end CFSG.GH74.Generic.S1.Exo
