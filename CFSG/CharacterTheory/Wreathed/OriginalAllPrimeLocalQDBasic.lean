module

public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover

public section

namespace CFSG.Wreathed.OriginalAllPrime.LocalQD

open CFSG.Semidihedral.ProjectiveSL2Cover

variable {F : Type} [Field F]

theorem mem_center_of_sq_eq_one (hF : ringChar F ≠ 2) {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hg : g ^ 2 = 1) : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← sq, hg])
  have hentry : ∀ i j, (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) i j = g i j := by
    intro i j
    rw [hinv]
  have hadj : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) F).adjugate) i j = g i j := by
    intro i j
    rw [← Matrix.SpecialLinearGroup.coe_inv]
    exact hentry i j
  simp only [Matrix.adjugate_fin_two] at hadj
  have h01 : g 0 1 = 0 := by
    have h := hadj 0 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h
    have h' : (2 : F) * g 0 1 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' h2
    · exact h''
  have h10 : g 1 0 = 0 := by
    have h := hadj 1 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h
    have h' : (2 : F) * g 1 0 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' h2
    · exact h''
  have h11 : g 1 1 = g 0 0 := by
    have h := hadj 0 0
    simpa only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] using h
  have hdet : g 0 0 ^ 2 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two, h01, h10, h11] at h
    linear_combination h
  refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨g 0 0, by simpa using hdet, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

theorem sq_eq_one_iff_mem_center (hF : ringChar F ≠ 2) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    g ^ 2 = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  refine ⟨mem_center_of_sq_eq_one hF, fun hg => ?_⟩
  rcases (mem_center_iff_eq_one_or_minusIdentity F g).mp hg with rfl | rfl
  · exact one_pow 2
  · exact minusIdentity_square F

theorem center_le_of_even_card [Finite F] (hF : ringChar F ≠ 2)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hB : Even (Nat.card B)) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 (even_iff_two_dvd.mp hB)
  have hb2 : (b : Matrix.SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one b
    rw [hb] at h
    exact congrArg Subtype.val h
  have hbc := mem_center_of_sq_eq_one hF hb2
  have hb1 : (b : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
    intro h
    have : b = 1 := Subtype.ext h
    rw [this, orderOf_one] at hb
    omega
  have hbm : (b : Matrix.SpecialLinearGroup (Fin 2) F) = minusIdentity F :=
    ((mem_center_iff_eq_one_or_minusIdentity F _).mp hbc).resolve_left hb1
  intro g hg
  rcases (mem_center_iff_eq_one_or_minusIdentity F g).mp hg with rfl | rfl
  · exact B.one_mem
  · rw [← hbm]
    exact b.2

theorem card_eq_card_map_mul_card_inf {G H : Type*} [Group G] [Group H] (f : G →* H)
    (B : Subgroup G) : Nat.card B = Nat.card (B.map f) * Nat.card (B ⊓ f.ker : Subgroup G) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.domRestrict B).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.domRestrict B)).toEquiv,
    MonoidHom.domRestrict_range] at h1
  rw [h1, MonoidHom.ker_domRestrict, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm]

theorem card_eq_two_mul_card_map [Finite F] (hF : ringChar F ≠ 2)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hB : Even (Nat.card B)) :
    Nat.card B = 2 * Nat.card (B.map (nativeQuotient F)) := by
  have hker : (nativeQuotient F).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [nativeQuotient_ker, center_eq_zpowers_minusIdentity]
  rw [card_eq_card_map_mul_card_inf (nativeQuotient F) B, hker,
    inf_eq_right.mpr (center_le_of_even_card hF hB), center_card F hF, mul_comm]

theorem ringChar_ne_two_of_card [Finite F] {p f : ℕ} (hpodd : Odd p)
    (hcard : Nat.card F = p ^ f) : ringChar F ≠ 2 := by
  intro h
  let : Fintype F := Fintype.ofFinite F
  have h2 := FiniteField.even_card_iff_char_two.mp h
  rw [← Nat.card_eq_fintype_card, hcard] at h2
  have hodd : Odd (p ^ f) := hpodd.pow
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr h2)

omit [Field F] in
theorem isOddPrimePower_card [Finite F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
  ⟨p, f, hp, hpodd, hf, hcard⟩

@[expose] def dihedralSign (z : ℕ) : DihedralGroup z →* ℤˣ where
  toFun g := match g with
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => -1
  map_one' := rfl
  map_mul' g h := by
    rcases g with i | i <;> rcases h with j | j <;> simp

theorem dihedralGroup_not_isPerfect (z : ℕ) : ¬ Group.IsPerfect (DihedralGroup z) := by
  intro h
  have hle := Abelianization.commutator_subset_ker (dihedralSign z)
  rw [h.commutator_eq_top, top_le_iff] at hle
  have hmem : (DihedralGroup.sr 0 : DihedralGroup z) ∈ (dihedralSign z).ker := by
    rw [hle]
    trivial
  have h1 : dihedralSign z (DihedralGroup.sr 0) = 1 := MonoidHom.mem_ker.mp hmem
  exact absurd h1 (by change (-1 : ℤˣ) ≠ 1; decide)

end CFSG.Wreathed.OriginalAllPrime.LocalQD
