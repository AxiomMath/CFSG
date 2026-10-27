module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Rank
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.QuasithinUnique.Unc25G2.M2x

theorem exists_conj_mem_of_isPGroup {Γ : Type} [Group Γ] [Finite Γ] {P A : Subgroup Γ}
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) (hA : IsPGroup 2 A) :
    ∃ g : Γ, ∀ x ∈ A, g * x * g⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q (hP.toSylow hodd)
  refine ⟨g, fun x hx => ?_⟩
  have hmem : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 Γ) : Subgroup Γ) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hQ hx, by simp [MulAut.conj_apply]⟩
  rw [hg] at hmem
  exact hmem

theorem card_le_sixteen_of_twoEAt {Γ : Type} [Group Γ] [Finite Γ] {P : Subgroup Γ}
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) (h : TwoEAt P) {A : Subgroup Γ}
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1) : Nat.card A ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ea, Eb, -, -, -, -, -, -, -, hEa, hEb, honly, hselfa, hselfb, -, -⟩ := h
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hs x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hP hodd hA2
  let φ : Γ ≃* Γ := MulAut.conj g
  have hφ : ∀ x, φ x = g * x * g⁻¹ := fun x => by simp [φ]
  set B : Subgroup Γ := A.map φ.toMonoidHom with hB
  have hBP : B ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    show φ x ∈ P
    rw [hφ]
    exact hg x hx
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hBs : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show φ a * φ a = 1
    rw [← map_mul, hs a ha, map_one]
  have hcard : Nat.card B = Nat.card A := Subgroup.card_map_of_injective φ.injective
  by_contra hlt
  rw [not_le] at hlt
  have hB2 : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hBs x x.2)⟩
  obtain ⟨n, hn⟩ := hB2.exists_card_eq
  have h16 : 2 ^ 4 ∣ Nat.card B := by
    rw [hn]
    have hn5 : 4 ≤ n := by
      by_contra hn4
      rw [not_le] at hn4
      have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact pow_dvd_pow 2 hn5
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 2 h16
  let A' : Subgroup Γ := K.map B.subtype
  have hA'B : A' ≤ B := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hA'card : Nat.card A' = 16 := by
    have := Subgroup.card_map_of_injective (f := B.subtype) (K := K) B.subtype_injective
    rw [hK] at this
    simpa [A'] using this
  have hA'c : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy => hBc x (hA'B hx) y (hA'B hy)
  have hA's : ∀ x ∈ A', x * x = 1 := fun x hx => hBs x (hA'B hx)
  have key : ∀ E : Subgroup Γ, (∀ x : Γ, (∀ e ∈ E, x * e = e * x) → x ∈ E) → E ≤ B → A' = E →
      False := by
    intro E hself hEB hA'E
    have hBE : B ≤ E := fun x hx => hself x fun e he => hBc x hx e (hEB he)
    have h1 := Subgroup.card_le_of_le hBE
    have h2 : Nat.card E = 16 := by
      rw [← hA'E]
      exact hA'card
    omega
  rcases honly A' (hA'B.trans hBP) ⟨hA'c, hA's⟩ hA'card with h1 | h1
  · exact key Ea hselfa (h1 ▸ hA'B) h1
  · exact key Eb hselfb (h1 ▸ hA'B) h1

theorem rankFour_range_of_twoEAt {Γ G : Type} [Group Γ] [Finite Γ] [Group G] [Finite G]
    {P : Subgroup Γ} (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) (h : TwoEAt P) {φ : Γ →* G}
    (hφ : Function.Injective φ) : RankFour φ.range := by
  intro B hBL hc hs
  have hBmap : (B.comap φ).map φ = B := Subgroup.map_comap_eq_self hBL
  have hcard : Nat.card B = Nat.card (B.comap φ) := by
    conv_lhs => rw [← hBmap]
    exact Subgroup.card_map_of_injective hφ
  rw [hcard]
  refine card_le_sixteen_of_twoEAt hP hodd h (fun x hx y hy => ?_) (fun x hx => ?_)
  · apply hφ
    rw [map_mul, map_mul]
    exact hc _ hx _ hy
  · apply hφ
    rw [map_mul, map_one]
    exact hs _ hx

end CFSG.EvenSporadicStandard.M23Std
