module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510E

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def sec5p510_T {G : Type} [Group G] (t z : G) (R : Subgroup G) : Subgroup G :=
  Subgroup.closure (conjClassIn (centralizer ({z} : Set G)) t ∩ (R : Set G))

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {Q₁ Q₂ : Subgroup G} {a b : G}

theorem sec5p510_t_mem_conj (t z : G) : t ∈ conjClassIn (centralizer ({z} : Set G)) t :=
  ⟨1, one_mem _, by group⟩

theorem sec5p510_conj_mem_conj {x g : G} (hx : x ∈ conjClassIn (centralizer ({z} : Set G)) t)
    (hg : g ∈ centralizer ({z} : Set G)) :
    g * x * g⁻¹ ∈ conjClassIn (centralizer ({z} : Set G)) t := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨g * m, mul_mem hg hm, by group⟩

theorem sec5p510_ab_mem_conj (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A) :
    a ∈ conjClassIn (centralizer ({z} : Set G)) t ∧
      b ∈ conjClassIn (centralizer ({z} : Set G)) t := by
  obtain ⟨c, -, h1, h2, hcz⟩ := hab.cyc_z h
  have hcH : c ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * z = c * z * c⁻¹ * c := by group
      _ = z * c := by rw [hcz]
  refine ⟨⟨c, hcH, h1.symm⟩, ⟨c * c, mul_mem hcH hcH, ?_⟩⟩
  calc b = c * a * c⁻¹ := h2.symm
    _ = c * (c * t * c⁻¹) * c⁻¹ := by rw [h1]
    _ = (c * c) * t * (c * c)⁻¹ := by group

theorem sec5p510_a_mem_H (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A) :
    a ∈ centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact sec5p510_A_comm h (hab.a_mem_A h) (sec5p510_z_mem_A h)

theorem sec5p510_z_mem_E (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A) :
    z ∈ sec5p510_E t a b := by
  obtain ⟨ht, ha, hb⟩ := sec5p510_E_gens t a b
  rw [← hab.prod]
  exact mul_mem (mul_mem ht ha) hb

theorem sec5p510_E_eq_mul_z (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A)
    {x : G} (hx : x ∈ sec5p510_E t a b) :
    ∃ y : G, (y = 1 ∨ y = t ∨ y = a ∨ y = b) ∧ (x = y ∨ x = y * z) := by
  rcases (sec5p510_mem_E_iff h hab).mp hx with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact ⟨1, Or.inl rfl, Or.inl h1⟩
  · exact ⟨t, Or.inr (Or.inl rfl), Or.inl h1⟩
  · exact ⟨a, Or.inr (Or.inr (Or.inl rfl)), Or.inl h1⟩
  · exact ⟨b, Or.inr (Or.inr (Or.inr rfl)), Or.inl h1⟩
  · exact ⟨b, Or.inr (Or.inr (Or.inr rfl)), Or.inr (h1.trans (hab.bz h).symm)⟩
  · exact ⟨a, Or.inr (Or.inr (Or.inl rfl)), Or.inr (h1.trans (hab.az h).symm)⟩
  · exact ⟨t, Or.inr (Or.inl rfl), Or.inr (h1.trans (hab.ab_eq h))⟩
  · exact ⟨1, Or.inl rfl, Or.inr (by rw [h1, hab.prod, one_mul])⟩

theorem sec5p510_E_le_T (hy : Sec5B59Hyp) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) :
    sec5p510_E t a b ≤ sec5p510_T t z (sec5p510_R S Q₁ Q₂) := by
  obtain ⟨haR, hbR⟩ := sec5p510_ab_mem_R hy h4 h hQ hab
  obtain ⟨hac, hbc⟩ := sec5p510_ab_mem_conj h hab
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx <;> rw [hx]
  · exact Subgroup.subset_closure ⟨sec5p510_t_mem_conj t z, sec5p510_t_mem_R h.toSec5Ctx hQ⟩
  · exact Subgroup.subset_closure ⟨hac, haR⟩
  · exact Subgroup.subset_closure ⟨hbc, hbR⟩

theorem sec5p510_T_le_R (t z : G) (R : Subgroup G) : sec5p510_T t z R ≤ R :=
  (Subgroup.closure_le _).mpr Set.inter_subset_right

theorem sec5p510_T_cases (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6) (h4 : Asc82FactReflCentQ6)
    (hCS : S ⊓ centralizer (L : Set G) = zpowers t)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) :
    sec5p510_T t z (sec5p510_R S Q₁ Q₂) = sec5p510_E t a b ∨
      sec5p510_T t z (sec5p510_R S Q₁ Q₂) = sec5p510_R S Q₁ Q₂ := by
  have hET := sec5p510_E_le_T hy h4 h hQ hab
  have hTR := sec5p510_T_le_R t z (sec5p510_R S Q₁ Q₂)
  rcases sec5p510_R_cases hy hD h4 hCS h hQ hab with hRE | ⟨hR16, -⟩
  · left
    exact le_antisymm (hTR.trans hRE.le) hET
  · have hE8 := sec5p510_card_E h hab
    have hdvd1 := Subgroup.card_dvd_of_le hET
    have hdvd2 := Subgroup.card_dvd_of_le hTR
    rw [hE8] at hdvd1
    rw [hR16] at hdvd2
    have hpos : 0 < Nat.card ↥(sec5p510_T t z (sec5p510_R S Q₁ Q₂)) := Nat.card_pos
    obtain ⟨m, hm⟩ := hdvd1
    have hm_le : 8 * m ≤ 16 := by
      rw [← hm]
      exact Nat.le_of_dvd (by norm_num) hdvd2
    have hm0 : m ≠ 0 := by
      rintro rfl
      omega
    have hm2 : m = 1 ∨ m = 2 := by omega
    rcases hm2 with rfl | rfl
    · left
      exact (Subgroup.eq_of_le_of_card_ge hET (by omega)).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hTR (by omega)

theorem sec5p510_conj_mem_T (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A)
    {R : Subgroup G} {y g : G} (hy : y = 1 ∨ y = t ∨ y = a ∨ y = b)
    (hg : g ∈ centralizer ({z} : Set G)) (hR : g * y * g⁻¹ ∈ R) :
    g * y * g⁻¹ ∈ sec5p510_T t z R := by
  obtain ⟨hac, hbc⟩ := sec5p510_ab_mem_conj h hab
  rcases hy with rfl | hy
  · rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · have hyc : y ∈ conjClassIn (centralizer ({z} : Set G)) t := by
      rcases hy with rfl | rfl | rfl
      · exact sec5p510_t_mem_conj _ _
      · exact hac
      · exact hbc
    exact Subgroup.subset_closure ⟨sec5p510_conj_mem_conj hyc hg, hR⟩

theorem sec5p510_T_strong (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6)
    (h4 : Asc82FactReflCentQ6) (hCS : S ⊓ centralizer (L : Set G) = zpowers t)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) {x g : G}
    (hx : x ∈ sec5p510_T t z (sec5p510_R S Q₁ Q₂)) (hg : g ∈ centralizer ({z} : Set G))
    (hxR : g * x * g⁻¹ ∈ sec5p510_R S Q₁ Q₂) :
    g * x * g⁻¹ ∈ sec5p510_T t z (sec5p510_R S Q₁ Q₂) := by
  rcases sec5p510_T_cases hy hD h4 hCS h hQ hab with hTE | hTR
  swap
  · rw [hTR]
    exact hxR
  rw [hTE] at hx
  obtain ⟨y, hy', hxy⟩ := sec5p510_E_eq_mul_z h hab hx
  rcases hxy with rfl | rfl
  · exact sec5p510_conj_mem_T h hab hy' hg hxR
  · have hgz : g * z * g⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [this]
        _ = z := by group
    have hsplit : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * z := by
      calc g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * y * g⁻¹) * z := by rw [hgz]
    have hzR : z ∈ sec5p510_R S Q₁ Q₂ := sec5p510_z_mem_R h.toSec5Ctx hQ
    have hyR : g * y * g⁻¹ ∈ sec5p510_R S Q₁ Q₂ := by
      rw [hsplit] at hxR
      have := mul_mem hxR (inv_mem hzR)
      rwa [mul_inv_cancel_right] at this
    have hzT : z ∈ sec5p510_T t z (sec5p510_R S Q₁ Q₂) :=
      sec5p510_E_le_T hy h4 h hQ hab (sec5p510_z_mem_E h hab)
    rw [hsplit]
    exact mul_mem (sec5p510_conj_mem_T h hab hy' hg hyR) hzT

end CFSG.OddStandard.SmallF3.Omega
