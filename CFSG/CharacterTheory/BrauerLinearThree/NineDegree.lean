module

public import CFSG.CharacterTheory.BrauerLinearThree.NineLocal
public import CFSG.CharacterTheory.Semidihedral.IndexTwoSL2Degree

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0)

omit [Finite F] in
@[expose] def squareUnits : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range

omit [Finite F] in
theorem mem_squareUnits {a : Fˣ} : a ∈ squareUnits (F := F) ↔ ∃ c : Fˣ, c ^ 2 = a :=
  Iff.rfl

omit [Finite F] in
include h2 in
theorem neg_one_not_mem_squareUnits (hq : Nat.card F % 4 = 3) : (-1 : Fˣ) ∉ squareUnits := by
  rintro ⟨c, hc⟩
  have hc' : c ^ 2 = -1 := hc
  have h4 : c ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc']
    simp
  have hdvd : orderOf c ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcard : orderOf c ∣ Nat.card F - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard c
  have hle : orderOf c ∣ 2 := by
    obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · rw [hck]; norm_num
    · rw [hck]; norm_num
    · rw [hck] at hcard; omega
  have hc2 : c ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hle
  rw [hc2] at hc'
  have := congrArg Units.val hc'
  simp only [Units.val_one, Units.val_neg] at this
  apply h2
  linear_combination this

include h2 in
theorem index_squareUnits (hq : Nat.card F % 4 = 3) : (squareUnits (F := F)).index = 2 := by
  have hneg := neg_one_not_mem_squareUnits h2 hq
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b => ?_⟩
  obtain ⟨ε, c, hε, rfl⟩ := exists_sign_mul_sq h2 hq b
  have hsq : c ^ 2 ∈ squareUnits (F := F) := ⟨c, rfl⟩
  rcases hε with rfl | rfl
  · right
    refine ⟨by rw [one_mul]; exact hsq, fun h => hneg ?_⟩
    have := (squareUnits (F := F)).mul_mem ((squareUnits (F := F)).inv_mem hsq) h
    rwa [one_mul, ← mul_assoc, inv_mul_cancel, one_mul] at this
  · left
    refine ⟨by rw [neg_one_mul, mul_neg_one, neg_neg]; exact hsq, fun h => hneg ?_⟩
    have := (squareUnits (F := F)).mul_mem h ((squareUnits (F := F)).inv_mem hsq)
    rwa [mul_inv_cancel_right] at this

section Quotient

variable {C : Type} [Group C] (ρ : GL (Fin 2) F →* C) (hρ : Function.Surjective ρ)
  (hker : ρ.ker = Z)

omit [Finite F] in
theorem det_scalar_two (c : Fˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) = c ^ 2 := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]

omit [Finite F] in
@[expose] def squareDetImage : Subgroup C :=
  ((squareUnits (F := F)).comap GeneralLinearGroup.det).map ρ

omit [Finite F] in
@[expose] def specialImage : Subgroup C := (ρ.comp (SpecialLinearGroup.toGL)).range

omit [Finite F] in
@[expose] def oddScalarImage : Subgroup C :=
  (ρ.comp ((GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).comp (powMonoidHom 2))).range

omit [Finite F] in
include hρ in
theorem squareDetImage_normal : (squareDetImage ρ).Normal :=
  ((inferInstance : (squareUnits (F := F)).Normal).comap _).map ρ hρ

include hZ hρ hker h2 in
theorem index_squareDetImage (hq : Nat.card F % 4 = 3) : (squareDetImage ρ).index = 2 := by
  have hle : ρ.ker ≤ (squareUnits (F := F)).comap GeneralLinearGroup.det := by
    rw [hker]
    intro A hA
    obtain ⟨c, rfl⟩ := hZ hA
    exact ⟨c, (det_scalar_two c).symm⟩
  rw [squareDetImage, Subgroup.index_map_eq _ hρ hle, Subgroup.index_comap_of_surjective _
    GeneralLinearGroup.det_surjective, index_squareUnits h2 hq]

include h2 in
theorem specialImage_sup_oddScalarImage (hq : Nat.card F % 4 = 3) :
    specialImage ρ ⊔ oddScalarImage ρ = squareDetImage ρ := by
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨B, rfl⟩
      exact ⟨SpecialLinearGroup.toGL B, ⟨1, by
        change (1 : Fˣ) ^ 2 = GeneralLinearGroup.det (SpecialLinearGroup.toGL B)
        rw [one_pow]
        exact (SpecialLinearGroup.coeToGL_det B).symm⟩, rfl⟩
    · rintro _ ⟨c, rfl⟩
      refine ⟨GeneralLinearGroup.scalar (Fin 2) (c ^ 2), ⟨c ^ 2, ?_⟩, rfl⟩
      change (c ^ 2) ^ 2 = GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (c ^ 2))
      rw [det_scalar_two]
  · rintro _ ⟨A, ⟨d, hd⟩, rfl⟩
    have hd' : d ^ 2 = GeneralLinearGroup.det A := hd
    obtain ⟨ε, c, hε, rfl⟩ := exists_sign_mul_sq h2 hq d
    have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> simp
    have hdet : GeneralLinearGroup.det (A * (GeneralLinearGroup.scalar (Fin 2) (c ^ 2))⁻¹) =
        1 := by
      rw [map_mul, map_inv, det_scalar_two, ← hd', mul_pow, hε2, one_mul, ← pow_mul,
        mul_inv_cancel]
    obtain ⟨B, hB⟩ : A * (GeneralLinearGroup.scalar (Fin 2) (c ^ 2))⁻¹ ∈
        (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hdet
    have hA : A = SpecialLinearGroup.toGL B * GeneralLinearGroup.scalar (Fin 2) (c ^ 2) := by
      rw [hB, inv_mul_cancel_right]
    rw [hA, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨B, rfl⟩)
      (Subgroup.mem_sup_right ⟨c, rfl⟩)

include hZ hZodd h2 hker in
theorem disjoint_specialImage_oddScalarImage (hq : Nat.card F % 4 = 3) :
    Disjoint (specialImage ρ) (oddScalarImage ρ) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨B, rfl⟩ ⟨c, hc⟩
  have hc' : ρ (GeneralLinearGroup.scalar (Fin 2) (c ^ 2)) = ρ (SpecialLinearGroup.toGL B) := hc
  have hmem : SpecialLinearGroup.toGL B * (GeneralLinearGroup.scalar (Fin 2) (c ^ 2))⁻¹ ∈ Z := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hc', mul_inv_cancel]
  obtain ⟨e, he⟩ := hZ hmem
  have hBe : SpecialLinearGroup.toGL B = GeneralLinearGroup.scalar (Fin 2) (e * c ^ 2) := by
    rw [map_mul, he, inv_mul_cancel_right]
  have he2 : (e * c ^ 2) ^ 2 = 1 := by
    rw [← det_scalar_two, ← hBe, SpecialLinearGroup.coeToGL_det]
  have hepow : e ^ Nat.card Z = 1 := by
    have h := pow_card_eq_one' (x := (⟨_, hmem⟩ : Z))
    have h' := congrArg (fun z : Z => (z : GL (Fin 2) F)) h
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
    rw [← he, ← map_pow] at h'
    have hinj : Function.Injective
        (GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
      intro a b hab
      have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hab
      exact Units.ext (by simpa using this)
    exact hinj (h'.trans (map_one _).symm)
  have hcpow : (c ^ 2) ^ ((Nat.card F - 1) / 2) = 1 := by
    have hodd := odd_card_F h2
    rw [← pow_mul, show 2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 by
      obtain ⟨k, hk⟩ := hodd; omega, ← Nat.card_units]
    exact pow_card_eq_one'
  set m := Nat.card Z * ((Nat.card F - 1) / 2) with hm
  have hmodd : Odd m := hZodd.mul (odd_half hq)
  have hem : (e * c ^ 2) ^ m = 1 := by
    rw [mul_pow, hm, pow_mul, hepow, one_pow, one_mul, mul_comm, pow_mul, hcpow, one_pow]
  have h1 : e * c ^ 2 = 1 := by
    have := pow_gcd_eq_one.mpr ⟨he2, hem⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hmodd), pow_one] at this
  have hB1 : SpecialLinearGroup.toGL B = 1 := by rw [hBe, h1, map_one]
  change (ρ.comp SpecialLinearGroup.toGL) B = 1
  rw [MonoidHom.comp_apply, hB1, map_one]

omit [Finite F] in
include hZ hZodd h2 hker in
theorem injective_comp_toGL :
    Function.Injective (ρ.comp (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →*
      GL (Fin 2) F)) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have hmem : SpecialLinearGroup.toGL B ∈ Z := by
    rw [← hker]
    exact hB
  have h := eq_one_of_mem_odd_of_det h2 hZ hZodd hmem
    (by rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact B.prop)
  exact SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm)

include h2 in
theorem pow_half_eq_one_of_mem_oddScalarImage {x : C} (hx : x ∈ oddScalarImage ρ) :
    x ^ ((Nat.card F - 1) / 2) = 1 := by
  obtain ⟨c, rfl⟩ := hx
  have hodd := odd_card_F h2
  have hc : (c ^ ((Nat.card F - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show (Nat.card F - 1) / 2 * 2 = Nat.card F - 1 by
      obtain ⟨k, hk⟩ := hodd; omega, ← Nat.card_units]
    exact pow_card_eq_one'
  rw [← map_pow]
  change ρ (GeneralLinearGroup.scalar (Fin 2) ((c ^ ((Nat.card F - 1) / 2)) ^ 2)) = 1
  rw [hc, map_one, map_one]

include h2 in
theorem odd_card_oddScalarImage [Finite C] (hq : Nat.card F % 4 = 3) :
    Odd (Nat.card (oddScalarImage ρ)) := by
  by_contra hcon
  rw [Nat.not_odd_iff_even] at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hcon)
  have hx2 : (x : C) * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, sq] at this
    exact congrArg Subtype.val this
  have h1 := eq_one_of_sq_of_pow_half hq hx2 (pow_half_eq_one_of_mem_oddScalarImage h2 ρ x.2)
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

open CFSG.Semidihedral.IndexTwoSL2Degree in
include hZ hZodd h2 hρ hker in
theorem not_dvd_of_four_dvd_of_mem_blocksIrr [Fintype C] (hq : Nat.card F % 4 = 3) (p f : ℕ)
    (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (χ : C → ℂ)
    (hχ : χ ∈ CFSG.BlocksIrr C) (n : ℕ) (hn : χ 1 = n) (h4 : 4 ∣ n) : ¬ p ∣ n := by
  have : Fintype F := Fintype.ofFinite F
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  have : (squareDetImage ρ).Normal := squareDetImage_normal ρ hρ
  have hcomm : ∀ j ∈ specialImage ρ, ∀ n ∈ oddScalarImage ρ, j * n = n * j := by
    rintro _ ⟨B, rfl⟩ _ ⟨c, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul]
    rw [GeneralLinearGroup.scalar_commute]
  have hNcomm : IsMulCommutative (oddScalarImage ρ) := ⟨⟨fun a b => by
    obtain ⟨c, hc⟩ := a.2
    obtain ⟨d, hd⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hc, ← hd, ← map_mul, ← map_mul, mul_comm c d]⟩⟩
  have hbot : IsMulCommutative (⊥ : Subgroup C) := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  obtain ⟨-, -, hdeg⟩ :=
    index_two_SL2_times_odd_abelian_by_abelian_group_has_no_four_characteristic_degree
      hp hpodd hf hF (squareDetImage ρ) (index_squareDetImage hZ h2 ρ hρ hker hq)
      (specialImage ρ) (oddScalarImage ρ) (specialImage_sup_oddScalarImage h2 ρ hq)
      (disjoint_specialImage_oddScalarImage hZ hZodd h2 ρ hker hq) hcomm
      ((MonoidHom.ofInjective (injective_comp_toGL hZ hZodd h2 ρ hker)).symm)
      (odd_card_oddScalarImage h2 ρ hq) (oddScalarImage ρ) ⊥ le_rfl bot_le
      (Subgroup.le_normalizer) disjoint_bot_right (sup_bot_eq _) hNcomm hbot
      (by rw [Subgroup.card_bot]; exact Nat.coprime_one_right _)
      (by rw [Subgroup.card_bot]; exact hp.not_dvd_one)
  exact (hdeg χ hχ n hn).1 h4

end Quotient

end CFSG.BrauerLinearThree
