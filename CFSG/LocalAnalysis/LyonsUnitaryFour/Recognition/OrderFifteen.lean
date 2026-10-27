module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ActualData
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.Classification

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G]

theorem lyons_configurations_U_V_rational_degree_twelve_and_order [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {B : Finset basis.index}
    {principal : basis.index} {row : basis.index → LyonsRow} {f : basis.index → ℤ} {P : ℚ}
    (S : Sylow 2 G) (z : G) (hD : LyonsSignedDegreeData B row f principal (Nat.card G) P)
    (hUV : B.val.map row = lyonsConfiguration .U ∨ B.val.map row = lyonsConfiguration .V)
    (hP : P * (Nat.card G * (Nat.card (Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) : ℚ) ^ 2) =
      128 * (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℚ) ^ 3)
    (hdeg : ∀ χ ∈ B, ((f χ).natAbs : ℂ) = (basis.representation χ).character 1)
    (hrat : ∀ χ ∈ B, (∀ ψ ∈ B, row ψ = row χ → ψ = χ) → (row χ).rotate = row χ →
      ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) :
    (∃ χ ∈ B, (basis.representation χ).character 1 = 12 ∧
      ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
    Nat.card G * Nat.card (Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) ^ 2 =
      195 * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3 := by
  classical
  obtain ⟨hP195, χ, hχ, hrow, habs, huniq⟩ := lyons_signedDegree_UV_endpoint hD hUV
  refine ⟨⟨χ, hχ, ?_, hrat χ hχ huniq (by rw [hrow]; rfl)⟩, ?_⟩
  · have h12 : (f χ).natAbs = 12 := by
      have h := Int.natCast_natAbs (f χ)
      rw [habs] at h
      exact_mod_cast h
    rw [← hdeg χ hχ, h12]
    norm_num
  · rw [hP195] at hP
    have h : (Nat.card G : ℚ) * (Nat.card (Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) : ℚ) ^ 2 = 195 * (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℚ) ^ 3 := by
      linarith
    exact_mod_cast h

theorem lyons_order_fifteen_rational_degree_twelve_and_order_of_data [Fintype G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (basis : FiniteIrreducibleCharacterBasis G) (B : Finset basis.index)
    (principal : basis.index)
    (hdata : ∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      ∃ (row : basis.index → LyonsRow) (f : basis.index → ℤ) (P : ℚ),
        LyonsSignedDegreeData B row f principal (Nat.card G) P ∧
        B.val.map row ∈ lyonsConfigurations ∧
        P * (Nat.card G * (Nat.card (Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G)) : ℚ) ^ 2) =
          128 * (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℚ) ^ 3 ∧
        (∀ χ ∈ B, ((f χ).natAbs : ℂ) = (basis.representation χ).character 1) ∧
        (∀ χ ∈ B, (∀ ψ ∈ B, row ψ = row χ → ψ = χ) → (row χ).rotate = row χ →
          ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q)) :
    (∃ χ ∈ B, (basis.representation χ).character 1 = 12 ∧
      ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
    (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      Nat.card G * Nat.card (Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G)) ^ 2 =
        195 * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3) ∧
    Nat.card G ∣ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 12 ∣ Nat.card G := by
  classical
  obtain ⟨hcard, -, -, hZcard, -⟩ := lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have key : ∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      (∃ χ ∈ B, (basis.representation χ).character 1 = 12 ∧
        ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
      Nat.card G * Nat.card (Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G)) ^ 2 =
        195 * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3 := by
    intro z hz hz1
    obtain ⟨row, f, P, hD, hmem, hP, hdeg, hrat⟩ := hdata z hz hz1
    exact lyons_configurations_U_V_rational_degree_twelve_and_order basis S z hD
      (lyons_signedDegree_U_or_V hD hmem) hP hdeg hrat
  have : Nontrivial (Subgroup.center (S : Subgroup G)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZcard]
    norm_num
  obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center (S : Subgroup G))
  obtain ⟨⟨χ, hχ, hχ12, hχrat⟩, -⟩ := key ((w : (S : Subgroup G)) : G) ⟨w, w.property, rfl⟩
    fun h => hw (Subtype.ext (Subtype.ext h))
  have hfin : Module.finrank ℂ (basis.representation χ).vector = 12 := by
    have h := Representation.char_one (basis.representation χ).representation
    rw [show (basis.representation χ).representation.character 1 = 12 from hχ12] at h
    exact_mod_cast h.symm
  obtain ⟨hdvd, hp⟩ := card_dvd_of_simple_rational_degree_twelve basis χ hfin hχrat S hcard
  exact ⟨⟨χ, hχ, hχ12, hχrat⟩, fun z hz hz1 => (key z hz hz1).2, hdvd, hp⟩

theorem lyons_order_fifteen_rational_degree_twelve_and_order [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character 1 = 12 ∧
        ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
    (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      Nat.card G * Nat.card (Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G)) ^ 2 =
        195 * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3) ∧
    Nat.card G ∣ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 12 ∣ Nat.card G :=
  lyons_order_fifteen_rational_degree_twelve_and_order_of_data hnonab hT S U hSU basis _ principal
    fun _ hz hz1 => lyons_order_fifteen_actual_data hnonab hT S U hSU hd basis ideal principal
      hprincipal hz hz1

theorem lyons_order_fifteen_order_identity_and_bound [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15) :
    (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      Nat.card G * Nat.card (Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G)) ^ 2 =
        195 * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3) ∧
    Nat.card G ∣ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 12 ∣ Nat.card G := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  let := hmax
  let := hchar
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  exact (lyons_order_fifteen_rational_degree_twelve_and_order hnonab hT S U hSU hd basis ideal
    principal hprincipal).2

theorem lyons_order_fifteen_centralizers_and_strong_embedding [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15) :
    (∀ e ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) ∧
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (Subgroup.normalizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) ∧
    Nat.card G = 195 * Nat.card (Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) := by
  obtain ⟨hcubic, hdvd, -⟩ := lyons_order_fifteen_order_identity_and_bound hnonab hT S U hSU hd
  obtain ⟨-, -, -, hZcard, -⟩ := lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have : Nontrivial (Subgroup.center (S : Subgroup G)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZcard]
    norm_num
  obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center (S : Subgroup G))
  set z : G := ((w : (S : Subgroup G)) : G)
  have hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype :=
    ⟨w, w.property, rfl⟩
  have hz1 : z ≠ 1 := fun h => hw (Subtype.ext (Subtype.ext h))
  obtain ⟨hcent, hemb⟩ := lyons_numerical_order_identity_forces_strong_embedding_of_dvd hnonab hT
    S U hSU hzZ hz1 (hcubic z hzZ hz1) hdvd
  refine ⟨hcent, hemb, ?_⟩
  have h := hcubic z hzZ hz1
  rw [hcent z hzZ hz1] at h
  have hpos : 0 < Nat.card (Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right (pow_pos hpos 2) ?_
  rw [h]
  ring

end CFSG.LyonsUnitaryFour
