module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HEquiv
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4Four

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG CFSG.ABGLocalTools CFSG.ComponentClassification
  CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.FooteLit.F5
  CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G]

theorem sylow_conj_eq_inf_of_B3 [Finite G]
    {D S₀ T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hDS₀ : D ≤ S₀) (hS₀T : S₀ ≤ T)
    (hsc : Open.fusionStronglyClosed (S₀ : Set G) T)
    (hN : ∀ n ∈ normalizer (S₀ : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S₀ : Set G))
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalClosure (D : Set G))) :
    ∃ k : G, S₀ ⊓ normalClosure (D : Set G) = P.map (MulAut.conj k⁻¹).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Sylow 2 G, (T' : Subgroup G) = T := by
    have h := hT.card_eq
    rw [Subgroup.card_top] at h
    exact ⟨Sylow.ofCard T h, Sylow.coe_ofCard _ _⟩
  have hB3 := Goldschmidt75.corollaryB3 T' (hT' ▸ hS₀T) (by rw [hT']; exact hsc) hN
  obtain ⟨hle, hp, hmax⟩ := hB3
  obtain ⟨B, hB, hS₀B⟩ := exists_isSylowOf_ge_of_le hle hp
  have hBeq : B = S₀ := hmax B hB.le hB.isPGroup hS₀B
  rw [hBeq] at hB
  set N : Subgroup G := normalClosure (D : Set G) with hN'
  have hNnormal : N.Normal := normalClosure_normal
  have hPM : P ≤ normalClosure (S₀ : Set G) :=
    hP.le.trans (normalClosure_mono (show (D : Set G) ⊆ S₀ from hDS₀))
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hB hPM hP.isPGroup
  refine ⟨k, ?_⟩
  set Pk : Subgroup G := P.map (MulAut.conj k⁻¹).toMonoidHom with hPk
  have hkap : ∀ a : G, (MulAut.conj k⁻¹).toMonoidHom a = k⁻¹ * a * k := by intro a; simp
  have hPkS : Pk ≤ S₀ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hkap a]
    exact hk a ha
  have hPkN : Pk ≤ N := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hkap a]
    have := hNnormal.conj_mem a (hP.le ha) k⁻¹
    simpa using this
  have hPkcard : Nat.card Pk = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  have hPkSyl : IsSylowOf 2 Pk N := isSylowOf_of_card hPkN (by rw [hPkcard]; exact hP.card_eq)
  have hS₀p : IsPGroup 2 S₀ := hT.isPGroup.to_le hS₀T
  exact hPkSyl.eq_of_le (le_inf hPkS hPkN) inf_le_right (hS₀p.to_inf_left)

theorem isDihedral_or_isSemidihedral_of_strong [Finite G]
    {D : Subgroup G} (hD : IsDihedralTwoGroup D) (h8 : 8 ≤ Nat.card D)
    (hS : ∃ S₀ T : Subgroup G, IsSylowOf 2 T ⊤ ∧ D ≤ S₀ ∧ S₀ ≤ T ∧
      Open.fusionStronglyClosed (S₀ : Set G) T ∧
      (S₀ = D ∨ (IsSemidihedralTwoGroup S₀ ∧ Nat.card S₀ = 2 * Nat.card D)))
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalClosure (D : Set G))) :
    IsDihedralTwoGroup P ∨ IsSemidihedralTwoGroup P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, T, hT, hDS₀, hS₀T, hsc, hcase⟩ := hS
  have hAut : IsPGroup 2 (MulAut S₀) := by
    rcases hcase with rfl | ⟨h, -⟩
    · exact isPGroup_mulAut_of_dihedral hD h8
    · exact isPGroup_mulAut_of_semidihedral h
  obtain ⟨k, hk⟩ := sylow_conj_eq_inf_of_B3 hT hDS₀ hS₀T hsc
    (fun n hn => pow_mem_centralizer_of_isPGroup_mulAut hAut hn) hP
  set N : Subgroup G := normalClosure (D : Set G) with hN
  set Pk : Subgroup G := P.map (MulAut.conj k⁻¹).toMonoidHom with hPk
  have hPkS : Pk ≤ S₀ := hk ▸ inf_le_left
  have hDN : D ≤ N := fun d hd => subset_normalClosure hd
  have hDPk : D ≤ Pk := hk ▸ le_inf hDS₀ hDN
  have e : P ≃* Pk := mulEquivConj P k
  rcases hcase with rfl | ⟨hsd, hcard⟩
  · exact Or.inl (isDihedral_of_mulEquiv (e.trans (MulEquiv.subgroupCongr
      (le_antisymm hPkS hDPk))) hD)
  · have h1 : Nat.card D ∣ Nat.card Pk := Subgroup.card_dvd_of_le hDPk
    have h2 : Nat.card Pk ∣ Nat.card S₀ := Subgroup.card_dvd_of_le hPkS
    obtain ⟨c, hc⟩ := h1
    have hDpos : 0 < Nat.card D := Nat.card_pos
    have hc2 : c ∣ 2 := by
      rw [hc, hcard, mul_comm 2] at h2
      exact Nat.dvd_of_mul_dvd_mul_left hDpos h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with rfl | rfl
    · exact Or.inl (isDihedral_of_mulEquiv (e.trans (MulEquiv.subgroupCongr
        (Subgroup.eq_of_le_of_card_ge hDPk (by rw [hc]; simp)).symm)) hD)
    · exact Or.inr (isSemidihedral_of_mulEquiv (e.trans (MulEquiv.subgroupCongr
        (Subgroup.eq_of_le_of_card_ge hPkS (by rw [hc, hcard]; ring_nf; exact le_refl _))))
        hsd)

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
