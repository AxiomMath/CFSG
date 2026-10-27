module

public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneTorusNormalizer
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_trivial_core_prime_torus_gives_actual_principal_block_family
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (ℓ : ℕ) (hℓ : (ℓ : ℤ) = ((p ^ f : ℕ) + (if p ^ f % 4 = 1 then 1 else -1 : ℤ)) / 2)
    (hℓp : ℓ.Prime) (hℓ7 : 7 ≤ ℓ) :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    (ℓ : ℤ) = ((q : ℤ) + e) / 2 ∧ IsCyclic W ∧ Nat.card W = ℓ ∧
      (∃ P : Sylow ℓ G, (P : Subgroup G) = W) ∧
      K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      (∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K ∧
        Subgroup.normalizer (Subgroup.zpowers w : Set G) = H) ∧
      (∀ w₁ ∈ W, ∀ w₂ ∈ W, w₁ ≠ 1 → w₂ ≠ 1 → (IsConj w₁ w₂ ↔ w₂ = w₁ ∨ w₂ = w₁⁻¹)) ∧
      ∀ u : G, Subgroup.zpowers u = W →
        ∀ (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
          (basis.representation principal).character = 1 →
          ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
            [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ],
          ∃ (δ : ℤ) (χ : basis.index) (ψ : ℕ → basis.index),
            (δ = 1 ∨ δ = -1) ∧ χ ≠ principal ∧
            (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ψ i ≠ principal ∧ ψ i ≠ χ) ∧
            Set.InjOn ψ (Finset.Icc 1 ((ℓ - 1) / 2)) ∧
            coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
              insert principal (insert χ ((Finset.Icc 1 ((ℓ - 1) / 2)).image ψ)) ∧
            (∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal, ∀ g : G,
              starRingEnd ℂ ((basis.representation θ).character g) =
                (basis.representation θ).character g) ∧
            0 < (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ ∧
            (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), (basis.representation (ψ i)).character 1 =
              (basis.representation χ).character 1 + δ) ∧
            (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ∀ x : G, ¬ ℓ ∣ orderOf x →
              (basis.representation (ψ i)).character x =
                (basis.representation χ).character x + δ) ∧
            (∀ j ∈ Finset.Icc 1 (ℓ - 1), ∀ y ∈ K, ¬ ℓ ∣ orderOf y →
              (basis.representation χ).character (u ^ j * y) = δ ∧
              ∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
                (basis.representation (ψ i)).character (u ^ j * y) =
                  δ * (Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ ((i * j : ℕ) : ℤ) +
                    Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ (-((i * j : ℕ) : ℤ)))) ∧
            ∀ x₁ x₂ z : G, ¬ ℓ ∣ orderOf x₁ → ¬ ℓ ∣ orderOf x₂ → ℓ ∣ orderOf z →
              ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
                (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
                  (basis.representation θ).character z / (basis.representation θ).character 1 =
                ((basis.representation χ).character 1 - (basis.representation χ).character x₁) *
                  ((basis.representation χ).character 1 -
                    (basis.representation χ).character x₂) /
                    ((basis.representation χ).character 1 *
                      ((basis.representation χ).character 1 + δ)) := by
  intro q e s₀ V D W H K
  have : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨-, -, hWcyc, -, hWcard, -, -, -, -, ⟨d, hd, -, -, -, hdW, -⟩, -, -, -, hKH, hinvH, -,
      -, -, -, -, -, ⟨hcases, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hWcyc : IsCyclic W := hWcyc
  have hd : d ∈ Subgroup.centralizer {t} ⊓ H := hd
  have hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹ := hdW
  have hKH : K.relIndex H = 2 := hKH
  have hinvH : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ := hinvH
  have hWℓ : Nat.card W = ℓ := by
    have h : ((Nat.card W : ℕ) : ℤ) = (ℓ : ℤ) := hWcard.trans hℓ.symm
    exact_mod_cast h
  have hHcard : Nat.card H = 24 * ℓ ∨ Nat.card H = 120 * ℓ := by
    rcases hcases with h | h
    · exact Or.inl (hWℓ ▸ h.2.2)
    · exact Or.inr (hWℓ ▸ h.2.2)
  have hℓpos : 0 < ℓ := hℓp.pos
  have hH2 : ¬ ℓ ^ 2 ∣ Nat.card H := by
    intro h2
    have hdiv : ∀ c : ℕ, Nat.card H = c * ℓ → ℓ ∣ c := by
      intro c hc
      rw [hc, sq] at h2
      exact Nat.dvd_of_mul_dvd_mul_right hℓpos h2
    rcases hHcard with h | h
    · have h24 := hdiv 24 h
      have hle := Nat.le_of_dvd (by norm_num) h24
      interval_cases ℓ <;> first | omega | exact absurd hℓp (by norm_num)
    · have h120 := hdiv 120 h
      have hle := Nat.le_of_dvd (by norm_num) h120
      interval_cases ℓ <;> first | omega | exact absurd hℓp (by norm_num)
  have hmod := Sylow.card_normalizer_modEq_card (p := ℓ) (n := 1) (H := W) (by rw [hWℓ, pow_one])
  have hidx : ¬ ℓ ∣ W.index := by
    intro hdvd
    apply hH2
    have hG : ℓ ^ 2 ∣ Nat.card G := by
      rw [← Subgroup.card_mul_index W, hWℓ, sq]
      exact Nat.mul_dvd_mul_left ℓ hdvd
    have h0 : Nat.card G % ℓ ^ 2 = 0 := Nat.mod_eq_zero_of_dvd hG
    have h1 : Nat.card H % ℓ ^ 2 = Nat.card G % ℓ ^ 2 := hmod
    exact Nat.dvd_of_mod_eq_zero (h1.trans h0)
  have hWp : IsPGroup ℓ W := IsPGroup.of_card (n := 1) (by rw [hWℓ, pow_one])
  let P : Sylow ℓ G := hWp.toSylow hidx
  have hPW : (P : Subgroup G) = W := rfl
  have hgen : ∀ w ∈ W, w ≠ 1 → Subgroup.zpowers w = W := by
    intro w hw hw1
    have hle : Subgroup.zpowers w ≤ W := Subgroup.zpowers_le.mpr hw
    have hord : orderOf w = ℓ := by
      have hdvd : orderOf w ∣ ℓ := hWℓ ▸ Subgroup.orderOf_dvd_natCard W hw
      rcases hℓp.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hw1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hWℓ])
  have hcentw : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K := by
    intro w hw hw1
    change _ = Subgroup.centralizer (W : Set G)
    rw [← hgen w hw hw1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).2
  refine ⟨hℓ, hWcyc, hWℓ, ⟨P, hPW⟩, hKH, hinvH, fun w hw hw1 => ⟨hcentw w hw hw1, by
    rw [hgen w hw hw1]⟩, ?_, ?_⟩
  ·
    intro w₁ hw₁ w₂ hw₂ hw₁1 hw₂1
    constructor
    · intro hconj
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have hcH : c ∈ H := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hgen w₁ hw₁ hw₁1, MonoidHom.map_zpowers]
        change Subgroup.zpowers (c * w₁ * c⁻¹) = _
        rw [hc, hgen w₂ hw₂ hw₂1, hgen w₁ hw₁ hw₁1]
      by_cases hcK : c ∈ K
      · left
        rw [← hc]
        exact (Subgroup.mem_centralizer_iff.mp hcK w₁ hw₁).symm ▸ by group
      · right
        rw [← hc]
        exact hinvH c hcH hcK w₁ hw₁
    · rintro (h | h)
      · rw [h]
      · exact isConj_iff.mpr ⟨d, by rw [hdW w₁ hw₁, h]⟩
  ·
    intro u hu basis principal hprincipal ideal _ _
    have hindex : (Subgroup.centralizer (P : Set G)).relIndex
        (Subgroup.normalizer (P : Set G)) = 2 := hKH
    obtain ⟨δ, χ, ψ, hδ, hχ, hψ, hinj, hB, hreal, hpos, hdeg, hreg, hsec, -, hsum⟩ :=
      prime_order_sylow_inversion_normalizer_exact_principal_block_family basis ideal ℓ
        (by omega) principal hprincipal P u (hPW.trans hu.symm) (by rw [hPW, hWℓ]) hindex
    exact ⟨δ, χ, ψ, hδ, hχ, hψ, hinj, hB, hreal, hpos, hdeg, hreg, hsec, hsum⟩

end CFSG.Semidihedral.Principal
