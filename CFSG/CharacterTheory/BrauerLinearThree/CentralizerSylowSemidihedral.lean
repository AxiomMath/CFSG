module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowBasic
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerStructure
public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitField
public import CFSG.CharacterTheory.Semidihedral.Subgroups

public section

namespace CFSG.BrauerLinearThree

open Polynomial Matrix CFSG.DesarguesianPlanes CFSG.Open

section NonsplitTorus

variable {F : Type} [Field F] [Finite F]

theorem irreducible_X_sq_sub_C_neg_one (hq : Nat.card F % 4 = 3) :
    Irreducible (X ^ 2 - C (-1 : F)) := by
  have : Fintype F := Fintype.ofFinite F
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  have hsq : IsSquare (-1 : F) := ⟨b, by rw [← hb, sq]⟩
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card] at hsq
  exact hsq hq

theorem exists_nonsplit_element (hq : Nat.card F % 4 = 3) {m : ℕ}
    (hdvd : 2 ^ (m + 1) ∣ Nat.card F ^ 2 - 1) :
    ∃ A : GL (Fin 2) F, orderOf A = 2 ^ (m + 1) ∧ A ^ 2 ^ m = -1 ∧
      diagGL 1 (-1) * A * (diagGL 1 (-1))⁻¹ = A ^ Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hfdef⟩ : ∃ f : F[X], f = X ^ 2 - C (-1 : F) := ⟨_, rfl⟩
  have : Fact (Irreducible f) := ⟨hfdef ▸ irreducible_X_sq_sub_C_neg_one hq⟩
  let K := AdjoinRoot f
  have hf : f ≠ 0 := hfdef ▸ X_pow_sub_C_ne_zero two_pos _
  have hdeg : f.natDegree = 2 := hfdef ▸ natDegree_X_pow_sub_C
  let b : Module.Basis (Fin 2) F K := (AdjoinRoot.powerBasis hf).basis.reindex (finCongr hdeg)
  have hb : ∀ i : Fin 2, b i = AdjoinRoot.root f ^ (i : ℕ) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rfl
  have : Finite K := CFSG.Wreathed.CentralSL2.finite_of_basis F K b
  have hcard : Nat.card Kˣ = Nat.card F ^ 2 - 1 := by
    rw [Nat.card_units, CFSG.Wreathed.CentralSL2.card_extension F K b]
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd_natCard (α := Kˣ) (hcard ▸ hdvd)
  set i := AdjoinRoot.root f with hi
  have hi2 : i ^ 2 = -1 := by
    have h : AdjoinRoot.mk f (X ^ 2 - C (-1)) = 0 := by rw [← hfdef]; exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_neg, map_one, ← hi] at h
    linear_combination h
  have hiq : i ^ Nat.card F = -i := by
    have h4 : Nat.card F = 2 * (2 * (Nat.card F / 4) + 1) + 1 := by omega
    rw [h4, pow_succ i, pow_mul i, hi2, (odd_two_mul_add_one _).neg_one_pow, neg_one_mul]
  have hS : CFSG.Wreathed.CentralSL2.frobMatrix F K b =
      ((diagGL 1 (-1) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have h0 : FiniteField.frobeniusAlgHom F K (b 0) = b 0 := by
      rw [CFSG.Wreathed.CentralSL2.frobeniusAlgHom_apply', hb]
      simp
    have h1 : FiniteField.frobeniusAlgHom F K (b 1) = -b 1 := by
      rw [CFSG.Wreathed.CentralSL2.frobeniusAlgHom_apply', hb]
      simpa using hiq
    ext r s
    rw [CFSG.Wreathed.CentralSL2.frobMatrix, LinearMap.toMatrix_apply]
    fin_cases s
    · change (b.repr (FiniteField.frobeniusAlgHom F K (b 0))) r = _
      rw [h0, Module.Basis.repr_self]
      fin_cases r <;> simp [diagGL]
    · change (b.repr (FiniteField.frobeniusAlgHom F K (b 1))) r = _
      rw [h1, map_neg, Module.Basis.repr_self]
      fin_cases r <;> simp [diagGL]
  set M := CFSG.Wreathed.CentralSL2.mulGL F K b with hM
  have hMinj : Function.Injective M := by
    intro x y hxy
    have h := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hxy
    simp only [hM, CFSG.Wreathed.CentralSL2.mulGL_val] at h
    exact Units.ext (CFSG.Wreathed.CentralSL2.mulMatrix_injective F K b h)
  have hζ2 : ζ ^ 2 ^ m = -1 := by
    apply units_eq_neg_one_of_orderOf_eq_two
    rw [orderOf_pow_of_dvd (by positivity) ⟨2, by rw [hζ, pow_succ]⟩, hζ, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨M ζ, by rw [orderOf_injective M hMinj, hζ], ?_, ?_⟩
  · rw [← map_pow, hζ2]
    apply Units.ext
    rw [hM, CFSG.Wreathed.CentralSL2.mulGL_val, Units.val_neg, Units.val_one, Units.val_neg,
      Units.val_one, CFSG.Wreathed.CentralSL2.mulMatrix, map_neg, map_one]
  · apply Units.ext
    rw [diagGL_one_neg_one_inv, Units.val_mul, Units.val_mul, ← hS, ← map_pow, hM,
      CFSG.Wreathed.CentralSL2.mulGL_val, CFSG.Wreathed.CentralSL2.mulGL_val,
      CFSG.Wreathed.CentralSL2.frobMatrix_mul_mulMatrix, Matrix.mul_assoc,
      CFSG.Wreathed.CentralSL2.frobMatrix_mul_self, Matrix.mul_one, Units.val_pow_eq_pow_val]

end NonsplitTorus

variable {G : Type*} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include hZ hZodd h2 hJ in
theorem exists_semidihedral_sylow (hq : Nat.card F % 4 = 3) {m : ℕ}
    (hm : (Nat.card F + 1).factorization 2 = m) :
    2 ≤ m ∧ ∃ h : G, J * h = h * J ∧ orderOf h = 2 ^ (m + 1) ∧ h ^ 2 ^ m = J ∧
      invJ₁ φ * h * (invJ₁ φ)⁻¹ = h ^ (2 ^ m - 1) ∧
      Subgroup.zpowers h ⊔ Subgroup.zpowers (invJ₁ φ) ≤ Subgroup.centralizer ({J} : Set G) ∧
      Nat.card (Subgroup.zpowers h ⊔ Subgroup.zpowers (invJ₁ φ) : Subgroup G) = 2 ^ (m + 2) ∧
      (∃ S : Sylow 2 (Subgroup.centralizer ({J} : Set G)),
        (S : Subgroup (Subgroup.centralizer ({J} : Set G))).map
            (Subgroup.centralizer ({J} : Set G)).subtype =
          Subgroup.zpowers h ⊔ Subgroup.zpowers (invJ₁ φ)) ∧
      ∃ e : SemidihedralGroup (m + 2) ≃*
          (Subgroup.zpowers h ⊔ Subgroup.zpowers (invJ₁ φ) : Subgroup G),
        (e (CFSG.Semidihedral.r (m + 2)) : G) = h ∧
        (e (CFSG.Semidihedral.s (m + 2)) : G) = invJ₁ φ ∧
        (e (CFSG.Semidihedral.r (m + 2) ^ 2 ^ m) : G) = J ∧
        (e (CFSG.Semidihedral.z (m + 2)) : G) = J := by
  subst hm
  obtain ⟨hm2, ⟨j, hj⟩, hdvd, w, hw, hcard⟩ := semidihedral_arith hq
  obtain ⟨A, hAord, hA2, hAconj⟩ := exists_nonsplit_element hq hdvd
  have hAq : A ^ Nat.card F = A ^ (2 ^ (Nat.card F + 1).factorization 2 - 1) := by
    conv_lhs => rw [hj]
    rw [pow_add, pow_mul, ← hAord, pow_orderOf_eq_one, one_pow, one_mul]
  set m := (Nat.card F + 1).factorization 2 with hm
  set h := linearCentralizerHom φ A with hh
  have hhJ : h ^ 2 ^ m = J := by
    rw [hh, ← map_pow, hA2, linearCentralizerHom_neg_one φ hZ hZodd h2 hJ]
  have hJ1 : J ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hJ
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
  have hez : (e (CFSG.Semidihedral.r (m + 2) ^ 2 ^ m) : G) = J := by
    rw [map_pow, Subgroup.coe_pow, he₀, hhJ]
  refine ⟨hm2, h, linearCentralizerHom_commute φ A, hord, hhJ, hconj, hle, hP,
    exists_sylow_map_subtype_eq hle hP hw hC, e, he₀, he₁, hez, ?_⟩
  rw [CFSG.Semidihedral.z, CFSG.Semidihedral.half, show m + 2 - 2 = m by omega, hez]

end CFSG.BrauerLinearThree
