module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignmentSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionOddMember
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusPrincipalFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_trivial_core_prime_torus_two_block_alignment_and_local_signs
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
    let c : ℕ := Nat.card (C t)
    let d : ℕ := Nat.card D
    let M : ℕ := 2 ^ (n - 1)
    (ℓ : ℤ) = ((q : ℤ) + e) / 2 ∧ IsCyclic W ∧ Nat.card W = ℓ ∧
      (∃ P : Sylow ℓ G, (P : Subgroup G) = W) ∧
      c = 2 * q * (q ^ 2 - 1) ∧ (d : ℤ) = 2 * ((q : ℤ) + e) ∧
      K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      (∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K ∧
        ∀ g : G, g ∈ H ↔ (g⁻¹ * w * g = w ∨ g⁻¹ * w * g = w⁻¹)) ∧
      ∀ (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
        (basis.representation principal).character = 1 →
        ∀ (ideal₂ : Ideal ComplexAlgebraicIntegers) [ideal₂.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2]
          (idealℓ : Ideal ComplexAlgebraicIntegers) [idealℓ.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ idealℓ) ℓ] (u : G), Subgroup.zpowers u = W →
        ∃ (α₁ α₂ α₃ : basis.index) (ε₁ ε₂ ε₃ : ℤ),
          [principal, α₁, α₂, α₃].Nodup ∧
          (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
          (∀ θ : basis.index,
            (θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal ∧
              Odd (Module.finrank ℂ (basis.representation θ).vector)) ↔
            θ = principal ∨ θ = α₁ ∨ θ = α₂ ∨ θ = α₃) ∧
          (Odd (Module.finrank ℂ (basis.representation α₁).vector) ∧
            Odd (Module.finrank ℂ (basis.representation α₂).vector) ∧
            Odd (Module.finrank ℂ (basis.representation α₃).vector)) ∧
          (1 < Module.finrank ℂ (basis.representation α₁).vector ∧
            1 < Module.finrank ℂ (basis.representation α₂).vector ∧
            1 < Module.finrank ℂ (basis.representation α₃).vector) ∧
          ((ε₁ = -1 ∧ ε₂ = -1 ∧ ε₃ = 1) ∨ (ε₁ = -1 ∧ ε₂ = 1 ∧ ε₃ = -1) ∨
            (ε₁ = 1 ∧ ε₂ = -1 ∧ ε₃ = -1)) ∧
          1 + ε₁ * (Module.finrank ℂ (basis.representation α₁).vector : ℤ) +
              ε₂ * (Module.finrank ℂ (basis.representation α₂).vector : ℤ) +
              ε₃ * (Module.finrank ℂ (basis.representation α₃).vector : ℤ) = 0 ∧
          Module.finrank ℂ (basis.representation α₁).vector *
              Module.finrank ℂ (basis.representation α₂).vector =
            q ^ 2 * Module.finrank ℂ (basis.representation α₃).vector ∧
          (basis.representation α₁).character t = ε₁ * e * q ∧
          (basis.representation α₂).character t = -(ε₂ * e * q) ∧
          (basis.representation α₃).character t = -ε₃ ∧
          (∀ w ∈ W, w ≠ 1 →
            (basis.representation α₁).character (t * w) = -ε₁ ∧
            (basis.representation α₂).character (t * w) = ε₂ ∧
            (basis.representation α₃).character (t * w) = -ε₃) ∧
          (∀ v : ℤ, ¬ v ≡ 0 [ZMOD M] → ¬ v ≡ (M / 2 : ℕ) [ZMOD M] →
            (basis.representation α₃).character ((fS (r n) : G) ^ v) = -ε₃ * (-1 : ℂ) ^ v) ∧
          ((Module.finrank ℂ (basis.representation α₁).vector : ℚ) - e * ε₁ * q ≠ 0) ∧
          ((Module.finrank ℂ (basis.representation α₂).vector : ℚ) + e * ε₂ * q ≠ 0) ∧
          (Nat.card G : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
            ((Module.finrank ℂ (basis.representation α₁).vector : ℚ) *
                (Module.finrank ℂ (basis.representation α₁).vector + ε₁) /
              (Module.finrank ℂ (basis.representation α₁).vector - e * ε₁ * q) ^ 2) *
            ((q + e) / q) ∧
          (Nat.card G : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
            ((Module.finrank ℂ (basis.representation α₂).vector : ℚ) *
                (Module.finrank ℂ (basis.representation α₂).vector + ε₂) /
              (Module.finrank ℂ (basis.representation α₂).vector + e * ε₂ * q) ^ 2) *
            ((q - e) / q) ∧
          ∃ (δ : ℤ) (χ : basis.index) (ψ : ℕ → basis.index),
            (δ = 1 ∨ δ = -1) ∧ χ ≠ principal ∧
            (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ψ i ≠ principal ∧ ψ i ≠ χ) ∧
            Set.InjOn ψ (Finset.Icc 1 ((ℓ - 1) / 2)) ∧
            coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal =
              insert principal (insert χ ((Finset.Icc 1 ((ℓ - 1) / 2)).image ψ)) ∧
            (∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal,
              ∀ g : G, starRingEnd ℂ ((basis.representation θ).character g) =
                (basis.representation θ).character g) ∧
            (χ = α₁ ∨ χ = α₂ ∨ χ = α₃) ∧
            1 < Module.finrank ℂ (basis.representation χ).vector ∧
            Odd (Module.finrank ℂ (basis.representation χ).vector) ∧
            (∀ i ∈ Finset.Icc 1 ((ℓ - 1) / 2),
              (Module.finrank ℂ (basis.representation (ψ i)).vector : ℤ) =
                (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ ∧
              0 < Module.finrank ℂ (basis.representation (ψ i)).vector ∧
              Even (Module.finrank ℂ (basis.representation (ψ i)).vector)) ∧
            (∀ z : G, ℓ ∣ orderOf z → (basis.representation χ).character z = δ) ∧
            (∀ x₁ x₂ z : G, ¬ ℓ ∣ orderOf x₁ → ¬ ℓ ∣ orderOf x₂ → ℓ ∣ orderOf z →
              ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal,
                (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
                  (basis.representation θ).character z / (basis.representation θ).character 1 =
                ((basis.representation χ).character 1 - (basis.representation χ).character x₁) *
                  ((basis.representation χ).character 1 -
                    (basis.representation χ).character x₂) /
                    ((basis.representation χ).character 1 *
                      ((basis.representation χ).character 1 + δ))) ∧
            (χ = α₁ → δ = -ε₁) ∧ (χ = α₂ → δ = ε₂) ∧ (χ = α₃ → δ = -ε₃) := by
  intro q e s₀ V D W H K c d M
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨hℓq, hWcyc, hWℓ, ⟨P, hPW⟩, hKH, hinvH, hcentw, -, -⟩ :=
    perfect_trivial_core_prime_torus_gives_actual_principal_block_family n hn S fS t ht hnonab
      hcentral hnc p f hp hpodd hf hq hmodel hN hY ℓ hℓ hℓp hℓ7
  have hWcyc : IsCyclic W := hWcyc
  have hWℓ : Nat.card W = ℓ := hWℓ
  have hPW : (P : Subgroup G) = W := hPW
  have hKH : K.relIndex H = 2 := hKH
  have hinvH : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ := hinvH
  have hcentw : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K ∧
      Subgroup.normalizer (Subgroup.zpowers w : Set G) = H := hcentw
  obtain ⟨hC, -, -, hWodd, -, ⟨hsup, hdisj, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hsup : V ⊔ W = D := hsup
  have hdisj : Disjoint V W := hdisj
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hDcard, -, -, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have he : e = 1 ∨ e = -1 := by
    change (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨ (if q % 4 = 1 then (1 : ℤ) else -1) = -1
    split_ifs <;> simp
  have hqodd : Odd q := hpodd.pow
  have h2ℓ : 2 * (ℓ : ℤ) = q + e := by
    have hev : Even ((q : ℤ) + e) := by
      obtain ⟨k, hk⟩ := hqodd
      rcases he with h | h <;> rw [h]
      · exact ⟨(k : ℤ) + 1, by rw [hk]; push_cast; ring⟩
      · exact ⟨(k : ℤ), by rw [hk]; push_cast; ring⟩
    rw [hℓq]
    exact (Int.mul_ediv_cancel' (even_iff_two_dvd.mp hev))
  have hd : (d : ℤ) = 2 * ((q : ℤ) + e) := by
    change ((Nat.card (Subgroup.centralizer (V : Set G)) : ℕ) : ℤ) = _
    rw [hDcard, hWℓ, ← h2ℓ]
    push_cast
    ring
  have hord : ∀ w ∈ W, w ≠ 1 → orderOf w = ℓ := by
    intro w hw hw1
    have hdvd : orderOf w ∣ ℓ := hWℓ ▸ Subgroup.orderOf_dvd_natCard W hw
    rcases hℓp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hgen : ∀ w ∈ W, w ≠ 1 → Subgroup.zpowers w = W := by
    intro w hw hw1
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
      (by rw [Nat.card_zpowers, hord w hw hw1, hWℓ])
  refine ⟨hℓq, hWcyc, hWℓ, ⟨P, hPW⟩, hC, hd, hKH, hinvH, fun w hw hw1 => ⟨(hcentw w hw hw1).1,
    fun g => ?_⟩, ?_⟩
  ·
    constructor
    · intro hg
      have hgi : g⁻¹ ∈ H := H.inv_mem hg
      by_cases hgK : g⁻¹ ∈ K
      · left
        have h := (Subgroup.mem_centralizer_iff.mp hgK w hw).symm
        calc g⁻¹ * w * g = g⁻¹ * w * g⁻¹⁻¹ := by rw [inv_inv]
          _ = w * g⁻¹ * g⁻¹⁻¹ := by rw [h]
          _ = w := by group
      · right
        have h := hinvH g⁻¹ hgi hgK w hw
        rwa [inv_inv] at h
    · intro hg
      rw [← (hcentw w hw hw1).2]
      have hmem : g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
        change Subgroup.zpowers (g⁻¹ * w * g⁻¹⁻¹) = _
        rw [inv_inv]
        rcases hg with h | h
        · rw [h]
        · rw [h, Subgroup.zpowers_inv]
      have h := Subgroup.inv_mem _ hmem
      rwa [inv_inv] at h
  intro basis principal hprincipal ideal₂ _ _ idealℓ _ _ u hu
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨F, hfield, hfinite, ρ, hFcard, hρ, hLρ, -, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal₂ basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  obtain ⟨hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ₂, ν₂, hfam, hdeg, -, hOFall⟩ := hrest
  have hOF := hOFall S fS hcent
  have heF : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = e := by rw [hFcard]
  have hq3 : 3 ≤ Nat.card F := by rw [hFcard]; omega
  have hqoddF : Odd (Nat.card F) := by rw [hFcard]; exact hqodd
  have he1 : Nat.card F % 4 = 1 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 :=
    fun h => by simp [h]
  have he3 : Nat.card F % 4 = 3 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 :=
    fun h => by simp [show ¬ Nat.card F % 4 = 1 by omega]
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have hqM : 2 ^ padicValNat 2 (Nat.card F ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [hFcard, h]
    rfl
  obtain ⟨hf₁, hf₂, hf₃, ho₁, ho₂, ho₃, hsigns, hsum2, hprod, -, -⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal₂ principal hprincipal
      localBasis localPrincipal (Nat.card F) hq3 hqoddF hqM _ he1 he3 _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ₂ ν₂ hfam hdeg
  obtain ⟨hrot, -, -, -⟩ := actual_principal_rotation_values_and_congruences hG hn ht2 hnonab
    basis ideal₂ principal hprincipal localBasis localPrincipal (Nat.card F) hq3 hqoddF _ he1 he3
    _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ₂ ν₂ hfam hdeg fS hcent
  obtain ⟨-, hδ₁, hδ₂, hδ₃, -, hnd, -, -, -, -, -, hB, -, hodd2, hsec, -⟩ := hfam
  obtain ⟨-, -, -, -, -, -, -, -, -⟩ := hdeg
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index),
      c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hnodup : [principal, χ₁, χ₂, χ₃].Nodup :=
    hnd.sublist (List.sublist_append_left [principal, χ₁, χ₂, χ₃] [χ₄])
  have hodd₂ : ∀ θ : basis.index,
      (θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal ∧
        Odd (Module.finrank ℂ (basis.representation θ).vector)) ↔
      θ = principal ∨ θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃ := by
    intro θ
    constructor
    · rintro ⟨hθB, hθo⟩
      exact (hodd2 θ hθB).mp hθo
    · intro h
      have hθB : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal := by
        rcases h with rfl | rfl | rfl | rfl <;> exact hmem _ (by simp)
      exact ⟨hθB, (hodd2 θ hθB).mpr h⟩
  have hf₁' : 1 < Module.finrank ℂ (basis.representation χ₁).vector := by exact_mod_cast hf₁
  have hf₂' : 1 < Module.finrank ℂ (basis.representation χ₂).vector := by exact_mod_cast hf₂
  have hf₃' : 1 < Module.finrank ℂ (basis.representation χ₃).vector := by exact_mod_cast hf₃
  have ho₁' : Odd (Module.finrank ℂ (basis.representation χ₁).vector) := by
    obtain ⟨k, hk⟩ := ho₁
    exact ⟨k.toNat, by omega⟩
  have ho₂' : Odd (Module.finrank ℂ (basis.representation χ₂).vector) := by
    obtain ⟨k, hk⟩ := ho₂
    exact ⟨k.toNat, by omega⟩
  have ho₃' : Odd (Module.finrank ℂ (basis.representation χ₃).vector) := by
    obtain ⟨k, hk⟩ := ho₃
    exact ⟨k.toNat, by omega⟩
  have hprod' : Module.finrank ℂ (basis.representation χ₁).vector *
      Module.finrank ℂ (basis.representation χ₂).vector =
      q ^ 2 * Module.finrank ℂ (basis.representation χ₃).vector := by
    have h : ((Module.finrank ℂ (basis.representation χ₁).vector *
        Module.finrank ℂ (basis.representation χ₂).vector : ℕ) : ℤ) =
        ((q ^ 2 * Module.finrank ℂ (basis.representation χ₃).vector : ℕ) : ℤ) := by
      push_cast
      rw [hprod, hFcard]
    exact_mod_cast h
  obtain ⟨h₁t, h₂t, h₃t, -⟩ := hsec 1 (by rw [orderOf_one]; decide)
  simp only [OneMemClass.coe_one, mul_one, hφ1, hFcard] at h₁t h₂t h₃t
  have hWD : W ≤ D := hsup ▸ le_sup_right
  have hvalw : ∀ w ∈ W, w ≠ 1 →
      (basis.representation χ₁).character (t * w) = -δ₁ ∧
      (basis.representation χ₂).character (t * w) = δ₂ ∧
      (basis.representation χ₃).character (t * w) = -δ₃ := by
    intro w hw hw1
    have hwt : w * t = t * w := (Subgroup.mem_centralizer_iff.mp (hWD hw) t htV).symm
    have hwC : w ∈ C t := Subgroup.mem_centralizer_singleton_iff.mpr hwt
    set w' : C t := ⟨w, hwC⟩ with hw'def
    have hw'ℓ : w' ^ ℓ = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hord w hw hw1]
      exact pow_orderOf_eq_one w)
    have hw'o : orderOf w' = ℓ := by rw [← Subgroup.orderOf_coe]; exact hord w hw hw1
    have hℓodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
    have hw'odd : Odd (orderOf w') := by rw [hw'o]; exact hℓodd
    have hw'Y : w' ∈ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) := by
      obtain ⟨k, hk⟩ := hℓodd
      have h := Subgroup.sq_mem_of_index_two hY (w' ^ (k + 1))
      rwa [← pow_mul, show (k + 1) * 2 = ℓ + 1 by omega, pow_succ, hw'ℓ, one_mul] at h
    have hκL : kappa t w' ∈ CFSG.generalizedFitting (Gamma t) := by
      rw [Subgroup.mem_comap, Subgroup.mem_comap, barKappa_nu] at hw'Y
      exact hw'Y
    have hκ1 : kappa t w' ≠ 1 := by
      intro h
      have hmem : w' ∈ NZ t := (QuotientGroup.eq_one_iff (N := NZ t) w').mp h
      have hZ : w' ∈ Z t := by
        have h' : NZ t = Z t := by
          change N t ⊔ Z t = Z t
          rw [hN, bot_sup_eq]
        rwa [h'] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hZ
      have hw2 : w ^ 2 = 1 := by
        have h1 : ((tInC t ^ k : C t) : G) = w := congrArg Subtype.val hk
        rw [← h1, Subgroup.coe_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
          zpow_natCast]
        change (t ^ 2) ^ k = 1
        rw [← ht2, pow_orderOf_eq_one, one_zpow]
      have h2 := orderOf_dvd_of_pow_eq_one hw2
      rw [hord w hw hw1] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hκℓ : kappa t w' ^ ℓ = 1 := by rw [← map_pow, hw'ℓ, map_one]
    have hfix := PrimeTorusAlignment.card_fixed_layer_element_eq_mod ρ hρ hLρ (by omega) hκL hκ1
      hκℓ
    have hφw : ((Nat.card {x : CFSG.ComponentClassification.CatalogueSchreierLinearTwo.Omega F //
        ((ρ (kappa t w') :
          CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F) :
          Equiv.Perm (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.Omega F)) x = x} :
          ℕ) : ℂ) - 1 = -(e : ℂ) := by
      rw [hfix, hFcard]
      have h := PrimeTorusAlignment.succ_mod_eq_one_sub he (by omega) h2ℓ
      have h' : (((q + 1) % ℓ : ℕ) : ℂ) = ((1 - e : ℤ) : ℂ) := by rw [← h]; norm_cast
      change (((q + 1) % ℓ : ℕ) : ℂ) - 1 = -(e : ℂ)
      rw [h']
      push_cast
      ring
    obtain ⟨h₁w, h₂w, h₃w, -⟩ := hsec w' hw'odd
    beta_reduce at h₁w h₂w
    rw [hφw, heF] at h₁w h₂w
    have hee : (e : ℂ) * e = 1 := by
      rcases he with h | h <;> rw [h] <;> norm_num
    refine ⟨?_, ?_, h₃w⟩
    · change (basis.representation χ₁).character (t * w) = _ at h₁w
      rw [h₁w]
      linear_combination (-(δ₁ : ℂ)) * hee
    · change (basis.representation χ₂).character (t * w) = _ at h₂w
      rw [h₂w]
      linear_combination (δ₂ : ℂ) * hee
  have hPu : (P : Subgroup G) = Subgroup.zpowers u := hPW.trans hu.symm
  have hPcard : Nat.card P = ℓ := by rw [hPW]; exact hWℓ
  have hPidx : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2 := by
    change (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 2
    rw [hPW]
    exact hKH
  obtain ⟨δ, χ, ψ, hδ, hχ, hψ, hinj, hBℓ, hreal, hχmem, hF1, hFodd, hψdeg, -, hvals, hconj,
      hsum⟩ :=
    prime_inversion_family_odd_member_from_three_odd_principal_two_characters basis ideal₂
      principal hprincipal χ₁ χ₂ χ₃ hnodup hodd₂ hf₁' hf₂' hf₃' δ₁ δ₂ δ₃ hsum2 idealℓ ℓ hℓ7 P u
      hPu hPcard hPidx
  have hsing : ∀ z : G, ℓ ∣ orderOf z → (basis.representation χ).character z = δ := by
    intro z hz
    obtain ⟨j, hj, y, hy, hyreg, hzc⟩ := hconj z hz
    obtain ⟨g, hg⟩ := isConj_iff.mp hzc
    have h1 := (hvals j hj y hy hyreg).1
    rw [← hg] at h1
    simpa only [FiniteComplexRepresentation.character, Representation.char_conj] using h1
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra! hall
    have hbot : W = ⊥ := (Subgroup.eq_bot_iff_forall W).mpr hall
    rw [hbot, Subgroup.card_bot] at hWℓ
    omega
  have hwt : w * t = t * w := (Subgroup.mem_centralizer_iff.mp (hWD hwW) t htV).symm
  have htw : ℓ ∣ orderOf (t * w) := by
    have hcomm : Commute t w := hwt.symm
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [ht2, hord w hwW hw1]
      exact (Nat.coprime_primes Nat.prime_two hℓp).mpr (by omega))]
    exact Dvd.dvd.mul_left (by rw [hord w hwW hw1]) _
  have hχtw := hsing (t * w) htw
  obtain ⟨h₁w, h₂w, h₃w⟩ := hvalw w hwW hw1
  have hFc : ∀ θ : basis.index, (basis.representation θ).character 1 =
      (Module.finrank ℂ (basis.representation θ).vector : ℂ) := fun θ =>
    (basis_character_one basis θ).1
  refine ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, hnodup, hδ₁, hδ₂, hδ₃, hodd₂, ⟨ho₁', ho₂', ho₃'⟩,
    ⟨hf₁', hf₂', hf₃'⟩, hsigns, hsum2, hprod', ?_, ?_, ?_, hvalw, ?_, ?_⟩
  · rw [h₁t]
  · rw [h₂t]
  · rw [h₃t]
  · intro v hv0 hv1
    exact (hrot v hv0 hv1).2.2
  · obtain ⟨hne₁, hne₂, hG₁, hG₂⟩ := hOF
    rw [heF, hFcard] at hne₁ hne₂ hG₁ hG₂
    have hdD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = d := by
      change _ = Nat.card (Subgroup.centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G))
      rw [centralizer_zpowers_sup_zpowers]
    rw [hdD] at hG₁ hG₂
    refine ⟨hne₁, hne₂, hG₁, hG₂, δ, χ, ψ, hδ, hχ, hψ, hinj, hBℓ, hreal, hχmem, hF1, hFodd, hψdeg,
      hsing, hsum, ?_, ?_, ?_⟩
    · rintro rfl
      have h : (δ : ℂ) = -(δ₁ : ℂ) := by rw [← hχtw, h₁w]
      exact_mod_cast h
    · rintro rfl
      have h : (δ : ℂ) = (δ₂ : ℂ) := by rw [← hχtw, h₂w]
      exact_mod_cast h
    · rintro rfl
      have h : (δ : ℂ) = -(δ₃ : ℂ) := by rw [← hχtw, h₃w]
      exact_mod_cast h

end CFSG.Semidihedral.Principal
