module

public import CFSG.LieType.SeitzGeneration.HeisTorusCaseA
public import CFSG.LieType.SeitzGeneration.HeisTorusCaseB
public import CFSG.LieType.SeitzGeneration.HeisLinearRoot
public import CFSG.LieType.SeitzGeneration.HeisLinearMain

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem caseA_one_add_zeta [CharP F 2] {ζ : F} (hζ : IsPrimitiveRoot ζ 5) :
    (1 + ζ) ≠ 0 ∧ (1 + ζ) ^ 5 ≠ 1 ∧ (1 + ζ) ^ 2 ≠ 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
    simpa [Finset.sum_range_succ, add_assoc] using this
  have hne : 1 + ζ ≠ 0 := by
    intro h
    apply hζ1
    have : ζ = -1 := by linear_combination h
    rw [this]
    linear_combination -h2
  refine ⟨hne, ?_, ?_⟩
  · intro h
    have h' : ζ + ζ ^ 4 = 1 := by
      linear_combination h - h5 - (1 + 2 * ζ + 5 * ζ ^ 2 + 5 * ζ ^ 3 + 2 * ζ ^ 4) * h2
    have h3 : ζ ^ 2 * (1 + ζ) = 0 := by linear_combination hsum - h' - h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hζ0 (pow_eq_zero_iff (by norm_num) |>.1 h4)
    · exact hne h4
  · intro h
    have : ζ ^ 2 = 0 := by linear_combination h - ζ * h2
    exact hζ0 (pow_eq_zero_iff (by norm_num) |>.1 this)

theorem caseA_neg_zeta (h2 : (2 : F) ≠ 0) (hp : 5 ≤ p) (hpo : Odd p) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) : (-ζ) ≠ 0 ∧ (-ζ) ^ p ≠ 1 ∧ (-ζ) ^ 2 ≠ 1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  refine ⟨neg_ne_zero.2 hζ0, ?_, ?_⟩
  · rw [hpo.neg_pow, hζ.pow_eq_one]
    intro h
    apply h2
    linear_combination -h
  · rw [neg_sq]
    exact hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)

theorem exists_single_mem_torus [Fact p.Prime] (hp : 5 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)} (hT : ContainsDiagTorus K)
    (hTw : ContainsFourierTorus ζ K) :
    ∃ a b : Fin p, a ≠ b ∧ ∃ c : F, c ≠ 0 ∧
      ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + single a b c := by
  haveI : NeZero p := ⟨by omega⟩
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two (by omega)
  by_cases h2 : (2 : F) = 0
  · haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rcases (show p = 5 ∨ 7 ≤ p by
      rcases (show p = 5 ∨ p = 6 ∨ 7 ≤ p by omega) with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hpp) (by norm_num)
      · exact Or.inr h) with h5 | hp7
    · subst h5
      obtain ⟨hν0, hνp, hν2⟩ := caseA_one_add_zeta hζ
      obtain ⟨b, hb, c, hc, g, hg, hgm⟩ := exists_single_mem_caseA hp hζ hν0 hνp hν2 hT hTw
      exact ⟨0, b, hb.symm, c, hc, g, hg, hgm⟩
    · exact exists_single_mem_caseB hp7 hζ hT hTw
  · obtain ⟨hν0, hνp, hν2⟩ := caseA_neg_zeta h2 hp hodd hζ
    obtain ⟨b, hb, c, hc, g, hg, hgm⟩ := exists_single_mem_caseA hp hζ hν0 hνp hν2 hT hTw
    exact ⟨0, b, hb.symm, c, hc, g, hg, hgm⟩

theorem torusFourierGen_of_prime [Fact p.Prime] (hp : 5 ≤ p) : TorusFourierGen F p := by
  intro ζ hζ K hT hTw
  obtain ⟨a, b, hab, c, hc, g, hgK, hg⟩ := exists_single_mem_torus hp hζ hT hTw
  have hx : SpecialLinearGroup.transvection hab c ∈ K := by
    have : SpecialLinearGroup.transvection hab c = g := Subtype.ext (by
      rw [SpecialLinearGroup.transvection_coe, hg])
    rw [this]
    exact hgK
  refine eq_top_of_torus_shift_root (by omega) hT (fun g' hg' => hTw g' ?_) hab hc hx
  exact ⟨fun j => ζ ^ (j : ℕ), by rw [hg']; exact heisShiftMat_mul_heisFourierMat hζ.pow_eq_one⟩

theorem linearHeisenbergPlanes : LinearHeisenbergPlanes :=
  linearHeisenbergPlanes_of_torusFourierGen fun _ _ _ p hp hp5 _ => by
    haveI : Fact p.Prime := ⟨hp⟩
    exact torusFourierGen_of_prime hp5

open CFSG.Open CFSG.AGLEmbeddingD2 in
theorem seitzInnerLinearNonab_holds :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ 5 ≤ p ∧ IsLinearIndex d.1 ∧ ¬ CentralPrimeFree p d.1 :=
  seitzInnerLinearNonab linearHeisenbergPlanes

end CFSG.LieType.SeitzGeneration
