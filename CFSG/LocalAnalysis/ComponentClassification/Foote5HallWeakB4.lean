module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeak
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallEight
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_of_hallConclusion
    {D : Subgroup G} (hD : AschbacherTheorem3.IsDihedralTwoGroup D) (h8 : 8 ≤ Nat.card D)
    (hconc : ∃ S₀ T : Subgroup G, IsSylowOf 2 T ⊤ ∧ D ≤ S₀ ∧ S₀ ≤ T ∧
      Open.fusionStronglyClosed (S₀ : Set G) T ∧
      (S₀ = D ∨ (AschbacherTheorem3.IsSemidihedralTwoGroup S₀ ∧
        Nat.card S₀ = 2 * Nat.card D)))
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalClosure (D : Set G))) {E : Subgroup G}
    (hEP : E ≤ P) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, T, hT, hDS₀, hS₀T, hsc, hcase⟩ := hconc
  have hdih : AschbacherTheorem3.IsDihedralTwoGroup S₀ ∨
      AschbacherTheorem3.IsSemidihedralTwoGroup S₀ := by
    rcases hcase with rfl | ⟨h, -⟩
    · exact Or.inl hD
    · exact Or.inr h
  have hAut : IsPGroup 2 (MulAut S₀) := by
    rcases hcase with rfl | ⟨h, -⟩
    · exact FooteLit.F5.isPGroup_mulAut_of_dihedral hD h8
    · exact FooteLit.F5.isPGroup_mulAut_of_semidihedral h
  obtain ⟨T', hT'⟩ : ∃ T' : Sylow 2 G, (T' : Subgroup G) = T := by
    have h := hT.card_eq
    rw [Subgroup.card_top] at h
    exact ⟨Sylow.ofCard T h, Sylow.coe_ofCard _ _⟩
  have hB3 := Goldschmidt75.corollaryB3 T' (hT' ▸ hS₀T) (by rw [hT']; exact hsc)
    (fun n hn => FooteLit.F5.pow_mem_centralizer_of_isPGroup_mulAut hAut hn)
  obtain ⟨hle, hp, hmax⟩ := hB3
  obtain ⟨B, hB, hS₀B⟩ := FooteLit.exists_isSylowOf_ge_of_le hle hp
  have hBeq : B = S₀ := hmax B hB.le hB.isPGroup hS₀B
  rw [hBeq] at hB
  have hPM : P ≤ normalClosure (S₀ : Set G) :=
    hP.le.trans (normalClosure_mono (show (D : Set G) ⊆ S₀ from hDS₀))
  obtain ⟨k, -, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hB hPM hP.isPGroup
  have hEk : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ S₀ := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hk x (hEP hx)
  have hEk2 : ∀ y ∈ E.map (MulAut.conj k⁻¹).toMonoidHom, y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE x hx, map_one]
  have h4 := Foote5.card_le_four_of_dihedral_or_semidihedral hdih hEk hEk2
  rwa [card_map_of_injective (MulAut.conj k⁻¹).injective] at h4

theorem goldschmidtCorB4_of_weak
    (hW : ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G),
      AschbacherTheorem3.IsDihedralTwoGroup D → 16 ≤ Nat.card D →
      (∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
        ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) → HallWeakConclusion D) :
    GoldschmidtCorB4 := by
  intro G _ _ D hD hcl P hP E hEP hE
  obtain ⟨n, hn, ⟨e⟩⟩ := id hD
  have hcard : Nat.card D = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · have hD4 : Nat.card D = 4 := by rw [hcard]; rfl
    exact FooteLit.F5.card_le_four_of_fourgroup hD4
      (FooteLit.F5.mul_self_eq_one_of_dihedral_four hD hD4) hcl hP hEP hE
  · exact card_le_four_of_hallConclusion hD (by rw [hcard]; norm_num)
      (HallD8.hall_d8 (e : D ≃* DihedralGroup 4) hcl) hP hEP hE
  · have h16 : 16 ≤ Nat.card D := by
      rw [hcard]
      have : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact card_le_four_of_weak hD (by omega) (hW G D hD h16 hcl) hP hEP hE

end CFSG.ComponentClassification.Foote5.HallGen
