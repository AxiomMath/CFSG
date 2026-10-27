module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionFamily
public import CFSG.CharacterTheory.Wreathed.CompatibleBoundaryCountSupport

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

variable {A : Type*} [Group A] [Fintype A] (basis : FiniteIrreducibleCharacterBasis A)

noncomputable def conjugateLabel (φ : basis.index) : basis.index :=
  Classical.choose (exists_conj_label basis φ)

theorem conjugateLabel_character (φ : basis.index) (g : A) :
    (basis.representation (conjugateLabel basis φ)).character g =
      starRingEnd ℂ ((basis.representation φ).character g) :=
  Classical.choose_spec (exists_conj_label basis φ) g

theorem conjugateLabel_character_eq_inv (φ : basis.index) (g : A) :
    (basis.representation (conjugateLabel basis φ)).character g =
      (basis.representation φ).character g⁻¹ := by
  rw [conjugateLabel_character, finite_character_conjugate_inverse]

theorem conjugateLabel_conjugateLabel (φ : basis.index) :
    conjugateLabel basis (conjugateLabel basis φ) = φ :=
  basis.distinct (funext fun g => by simp only [conjugateLabel_character, Complex.conj_conj])

theorem conjugateLabel_injective : Function.Injective (conjugateLabel basis) := by
  intro φ ψ h
  rw [← conjugateLabel_conjugateLabel basis φ, h, conjugateLabel_conjugateLabel]

theorem conjugateLabel_principal (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    conjugateLabel basis principal = principal :=
  basis.distinct (funext fun g => by
    simp only [conjugateLabel_character, hprincipal, Pi.one_apply, map_one])

theorem univ_eq_insert_conj_transversal (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {T : Finset basis.index}
    (hT0 : principal ∉ T) (hT1 : ∀ φ ∈ T, conjugateLabel basis φ ∉ T)
    (hT2 : ∀ φ, φ ≠ principal → φ ∈ T ∨ conjugateLabel basis φ ∈ T) :
    Disjoint T (T.image (conjugateLabel basis)) ∧ principal ∉ T ∪ T.image (conjugateLabel basis) ∧
      Finset.univ = insert principal (T ∪ T.image (conjugateLabel basis)) := by
  have hσp := conjugateLabel_principal basis principal hprincipal
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro φ hφ hφ'
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hφ'
    exact hT1 ψ hψ hφ
  · rw [Finset.mem_union, not_or]
    refine ⟨hT0, fun h => ?_⟩
    obtain ⟨ψ, hψ, hψp⟩ := Finset.mem_image.mp h
    have hψ' : ψ = principal := by rw [← conjugateLabel_conjugateLabel basis ψ, hψp, hσp]
    exact hT0 (hψ' ▸ hψ)
  · ext φ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_image, true_iff]
    by_cases hφ : φ = principal
    · exact Or.inl hφ
    · right
      rcases hT2 φ hφ with h | h
      · exact Or.inl h
      · exact Or.inr ⟨conjugateLabel basis φ, h, conjugateLabel_conjugateLabel basis φ⟩

theorem sum_conj_transversal (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {T : Finset basis.index}
    (hT0 : principal ∉ T) (hT1 : ∀ φ ∈ T, conjugateLabel basis φ ∉ T)
    (hT2 : ∀ φ, φ ≠ principal → φ ∈ T ∨ conjugateLabel basis φ ∈ T) (F : basis.index → ℂ) :
    ∑ φ ∈ T, (F φ + F (conjugateLabel basis φ)) = ∑ φ, F φ - F principal := by
  obtain ⟨hdisj, hp, huniv⟩ :=
    univ_eq_insert_conj_transversal basis principal hprincipal hT0 hT1 hT2
  rw [huniv, Finset.sum_insert hp, Finset.sum_union hdisj, Finset.sum_add_distrib,
    Finset.sum_image fun x _ y _ h => conjugateLabel_injective basis h]
  ring

section Abelian

variable [IsMulCommutative A]

theorem label_character_one_of_comm (φ : basis.index) :
    (basis.representation φ).character 1 = 1 := by
  obtain ⟨μ, hμ⟩ := CFSG.Wreathed.CompatibleFamilies.exists_hom_of_isMulCommutative basis φ
  rw [← hμ, map_one, Units.val_one]

theorem label_character_mul_of_comm (φ : basis.index) (x y : A) :
    (basis.representation φ).character (x * y) =
      (basis.representation φ).character x * (basis.representation φ).character y := by
  obtain ⟨μ, hμ⟩ := CFSG.Wreathed.CompatibleFamilies.exists_hom_of_isMulCommutative basis φ
  rw [← hμ, ← hμ, ← hμ, map_mul, Units.val_mul]

theorem label_character_pow_of_comm (φ : basis.index) (x : A) (k : ℕ) :
    (basis.representation φ).character (x ^ k) = (basis.representation φ).character x ^ k := by
  obtain ⟨μ, hμ⟩ := CFSG.Wreathed.CompatibleFamilies.exists_hom_of_isMulCommutative basis φ
  rw [← hμ, ← hμ, map_pow, Units.val_pow_eq_pow_val]

theorem label_character_mul_inv_of_comm (φ : basis.index) (x : A) :
    (basis.representation φ).character x * (basis.representation φ).character x⁻¹ = 1 := by
  rw [← label_character_mul_of_comm, mul_inv_cancel, label_character_one_of_comm]

theorem sum_label_character_eq_zero_of_ne_one {z : A} (hz : z ≠ 1) :
    ∑ φ, (basis.representation φ).character z = 0 := by
  set f : A → ℂ := fun y => if y = 1 then (Nat.card A : ℂ) else 0 with hf
  have hclass : ∀ g c : A, f (c * g * c⁻¹) = f g := by
    intro g c
    simp only [hf]
    congr 1
    apply propext
    constructor
    · intro h
      have h' := congrArg (fun w => c⁻¹ * w * c) h
      simpa [mul_assoc] using h'
    · rintro rfl
      simp
  have hrec := finiteIrreducibleCharacterBasis_reconstruction basis f hclass z
  have hpair : ∀ φ, characterPairing f (basis.representation φ).character = 1 := by
    intro φ
    unfold characterPairing
    rw [Finset.sum_eq_single 1]
    · simp only [hf, ↓reduceIte, inv_one, label_character_one_of_comm, mul_one]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    · intro y _ hy
      simp [hf, hy]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [hpair, one_mul] at hrec
  rw [← hrec]
  simp [hf, hz]

theorem eq_principal_of_conjugateLabel_eq (hodd : Nat.card A % 2 = 1) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {φ : basis.index}
    (hφ : conjugateLabel basis φ = φ) : φ = principal := by
  apply basis.distinct
  show (basis.representation φ).character = (basis.representation principal).character
  rw [hprincipal]
  funext z
  rw [Pi.one_apply]
  have hreal : starRingEnd ℂ ((basis.representation φ).character z) =
      (basis.representation φ).character z := by
    rw [← conjugateLabel_character, hφ]
  have hpow : (basis.representation φ).character z ^ Nat.card A = 1 := by
    rw [← label_character_pow_of_comm, pow_card_eq_one', label_character_one_of_comm]
  have hre := Complex.conj_eq_iff_re.mp hreal
  have hnorm : ‖(basis.representation φ).character z‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'
  rw [← hre, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rcases (abs_eq zero_le_one).mp hnorm with h | h
  · rw [← hre, h, Complex.ofReal_one]
  · exfalso
    rw [← hre, h, Complex.ofReal_neg, Complex.ofReal_one,
      Odd.neg_one_pow (Nat.odd_iff.mpr hodd)] at hpow
    norm_num at hpow

theorem exists_conj_transversal (hodd : Nat.card A % 2 = 1) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ T : Finset basis.index, principal ∉ T ∧ (∀ φ ∈ T, conjugateLabel basis φ ∉ T) ∧
      (∀ φ, φ ≠ principal → φ ∈ T ∨ conjugateLabel basis φ ∈ T) ∧ 2 * T.card + 1 = Nat.card A := by
  let rk : basis.index → ℕ := fun φ => (Fintype.equivFin basis.index φ : ℕ)
  have hrk : Function.Injective rk := fun φ ψ h =>
    (Fintype.equivFin basis.index).injective (Fin.ext h)
  let T := Finset.univ.filter (fun φ => φ ≠ principal ∧ rk φ < rk (conjugateLabel basis φ))
  have hmem : ∀ φ, φ ∈ T ↔ φ ≠ principal ∧ rk φ < rk (conjugateLabel basis φ) := by
    intro φ
    simp [T]
  have hσp := conjugateLabel_principal basis principal hprincipal
  have h0 : principal ∉ T := fun h => ((hmem _).mp h).1 rfl
  have h1 : ∀ φ ∈ T, conjugateLabel basis φ ∉ T := by
    intro φ hφ hσφ
    have ha := ((hmem _).mp hφ).2
    have hb := ((hmem _).mp hσφ).2
    rw [conjugateLabel_conjugateLabel] at hb
    omega
  have h2 : ∀ φ, φ ≠ principal → φ ∈ T ∨ conjugateLabel basis φ ∈ T := by
    intro φ hφ
    have hrkne : rk φ ≠ rk (conjugateLabel basis φ) := fun h =>
      hφ (eq_principal_of_conjugateLabel_eq basis hodd principal hprincipal (hrk h).symm)
    have hσφ : conjugateLabel basis φ ≠ principal := fun h =>
      hφ (by rw [← conjugateLabel_conjugateLabel basis φ, h, hσp])
    rcases Nat.lt_or_gt_of_ne hrkne with h | h
    · exact Or.inl ((hmem _).mpr ⟨hφ, h⟩)
    · right
      refine (hmem _).mpr ⟨hσφ, ?_⟩
      rw [conjugateLabel_conjugateLabel]
      exact h
  refine ⟨T, h0, h1, h2, ?_⟩
  obtain ⟨hdisj, hp, huniv⟩ := univ_eq_insert_conj_transversal basis principal hprincipal h0 h1 h2
  have hcard := congrArg Finset.card huniv
  rw [Finset.card_univ, CFSG.Wreathed.CompatibleFamilies.card_index_of_isMulCommutative basis,
    Finset.card_insert_of_notMem hp, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (conjugateLabel_injective basis)] at hcard
  omega

end Abelian

end CFSG.CyclicBlocks
