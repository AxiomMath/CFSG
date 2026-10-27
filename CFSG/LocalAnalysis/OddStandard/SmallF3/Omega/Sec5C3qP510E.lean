module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510R
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Ab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def sec5p510_E {G : Type} [Group G] (t a b : G) : Subgroup G :=
  Subgroup.closure {t, a, b}

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {Q₁ Q₂ : Subgroup G} {a b : G}

theorem sec5p510_S_le_normalizer (hy : Sec5B59Hyp) (h : Sec5Ctx G t L S z) :
    S ≤ normalizer (L : Set G) := fun x hx =>
  sec4_mem_normalizer hy.h36 h.toSec5Setting.toSec3SettingLB x (h.sylow.1 hx)

theorem sec5p510_mem_R_of_wclass_one (hy : Sec5B59Hyp) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂) {x : G}
    (hx : x ∈ wclass φ 1) (hxz : x * z ∈ wclass φ 5) : x ∈ sec5p510_R S Q₁ Q₂ := by
  have hxA : x ∈ A := h.model.perm.wclass_subset 1 hx
  have hxS : x ∈ S := h.A_le hxA
  have hxN : x ∈ normalizer (L : Set G) := sec5p510_S_le_normalizer hy h.toSec5Ctx hxS
  have hx2 : x * x = 1 := sec5p510_A_sq h hxA
  have hxzc : x * z = z * x := sec5p510_A_comm h hxA (sec5p510_z_mem_A h)
  have ht1 : ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 1 α := by
    obtain ⟨v, hv, hvx⟩ := hx
    rw [← hvx]
    exact h.model.type_one v (Or.inl hv)
  have ht2 : ∃ α : ℤˣ, InducesTypeSome L (x * z) 6 (-1) 1 α := by
    obtain ⟨v, hv, hvx⟩ := hxz
    rw [← hvx]
    exact h.model.type_one v (Or.inr hv)
  exact ⟨hxS, h4 G L z h.toSec5Setting.isOm6Z2 h.pocket Q₁ Q₂ hQ.le₁ hQ.le₂ hQ.iso₁ hQ.iso₂
    hQ.comm hQ.card hQ.center hQ.not_central x hxN hx2 hxzc ht1 ht2⟩

theorem sec5p510_ab_mem_R (hy : Sec5B59Hyp) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) :
    a ∈ sec5p510_R S Q₁ Q₂ ∧ b ∈ sec5p510_R S Q₁ Q₂ := by
  refine ⟨sec5p510_mem_R_of_wclass_one hy h4 h hQ hab.mem₁ ?_,
    sec5p510_mem_R_of_wclass_one hy h4 h hQ hab.mem₂ ?_⟩
  · rw [hab.az h]
    exact hab.tb_mem h
  · rw [hab.bz h]
    exact hab.ta_mem h

theorem sec5p510_E_gens (t a b : G) :
    t ∈ sec5p510_E t a b ∧ a ∈ sec5p510_E t a b ∧ b ∈ sec5p510_E t a b :=
  ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp)⟩

theorem sec5p510_E_eq_image (h : Sec510Ctx G t L S z r ρ B A φ) {i j : Fin 6}
    (hi : φ (Pi.single i 1) = a) (hj : φ (Pi.single j 1) = b) :
    (sec5p510_E t a b : Set G) = φ '' ((sec5p510_Vs i j : Finset (Fin 6 → ZMod 2)) : Set _) := by
  have hmul := h.model.perm.map_add
  have h0 := h.model.perm.map_zero
  have h1 := sec5p510_phi_one h
  obtain ⟨ht, ha, hb⟩ := sec5p510_E_gens t a b
  ext x
  constructor
  · intro hx
    refine Subgroup.closure_induction
      (p := fun x _ => x ∈ φ '' ((sec5p510_Vs i j : Finset (Fin 6 → ZMod 2)) : Set _))
      ?_ ?_ ?_ ?_ hx
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · exact ⟨1, by simp [sec5p510_Vs], by rw [h1, hx]⟩
      · exact ⟨Pi.single i 1, by simp [sec5p510_Vs], by rw [hi, hx]⟩
      · exact ⟨Pi.single j 1, by simp [sec5p510_Vs], by rw [hj, hx]⟩
    · exact ⟨0, by simp [sec5p510_Vs], h0⟩
    · rintro x y _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
      exact ⟨v + w, sec5p510_Vs_add hv hw, hmul v w⟩
    · rintro x _ ⟨v, hv, rfl⟩
      refine ⟨v, hv, ?_⟩
      have hsq : φ v * φ v = 1 := by rw [← hmul, sec5p510_vec_add_self, h0]
      exact (inv_eq_of_mul_eq_one_right hsq).symm
  · rintro ⟨v, hv, rfl⟩
    show φ v ∈ sec5p510_E t a b
    simp only [Finset.mem_coe, sec5p510_Vs, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0]
      exact one_mem _
    · rw [h1]
      exact ht
    · rw [hi]
      exact ha
    · rw [hj]
      exact hb
    · rw [hmul, h1, hi]
      exact mul_mem ht ha
    · rw [hmul, h1, hj]
      exact mul_mem ht hb
    · rw [hmul, hi, hj]
      exact mul_mem ha hb
    · rw [hmul, hmul, h1, hi, hj]
      exact mul_mem (mul_mem ht ha) hb

theorem sec5p510_mem_E_iff (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A)
    {x : G} : x ∈ sec5p510_E t a b ↔
      x = 1 ∨ x = t ∨ x = a ∨ x = b ∨ x = t * a ∨ x = t * b ∨ x = a * b ∨ x = t * a * b := by
  obtain ⟨i, j, hij, hi, hj⟩ := sec5p510_ab_coords hab
  have himg := sec5p510_E_eq_image h hi hj
  have hmul := h.model.perm.map_add
  have h0 := h.model.perm.map_zero
  have h1 := sec5p510_phi_one h
  obtain ⟨ht, ha, hb⟩ := sec5p510_E_gens t a b
  constructor
  · intro hx
    have hx' : x ∈ (sec5p510_E t a b : Set G) := hx
    rw [himg] at hx'
    obtain ⟨v, hv, rfl⟩ := hx'
    simp only [Finset.mem_coe, sec5p510_Vs, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hj)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hmul, h1, hi])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hmul, h1, hj]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hmul, hi, hj])))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by rw [hmul, hmul, h1, hi, hj])))))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact ht
    · exact ha
    · exact hb
    · exact mul_mem ht ha
    · exact mul_mem ht hb
    · exact mul_mem ha hb
    · exact mul_mem (mul_mem ht ha) hb

theorem sec5p510_E_inter_delta (h : Sec510Ctx G t L S z r ρ B A φ)
    (hab : Sec510Ab t z a b φ A) {x : G} (hxE : x ∈ sec5p510_E t a b)
    (hxΔ : x ∈ wclass φ 6 ∪ wclass φ 1) : x = t ∨ x = a ∨ x = b := by
  obtain ⟨i, j, hij, hi, hj⟩ := sec5p510_ab_coords hab
  have himg := sec5p510_E_eq_image h hi hj
  have h1 := sec5p510_phi_one h
  have hx' : x ∈ (sec5p510_E t a b : Set G) := hxE
  rw [himg] at hx'
  obtain ⟨v, hv, rfl⟩ := hx'
  have hvw : vecWeight v = 6 ∨ vecWeight v = 1 := by
    rcases hxΔ with ⟨w, hw, hwv⟩ | ⟨w, hw, hwv⟩
    · have hwv' := h.model.perm.injective hwv
      rw [hwv'] at hw
      exact Or.inl hw
    · have hwv' := h.model.perm.injective hwv
      rw [hwv'] at hw
      exact Or.inr hw
  rcases sec5p510_Vs_delta (Finset.mem_coe.mp hv) hvw with rfl | rfl | rfl
  · exact Or.inl h1
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hj)

theorem sec5p510_card_E (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A) :
    Nat.card (sec5p510_E t a b) = 8 := by
  obtain ⟨i, j, hij, hi, hj⟩ := sec5p510_ab_coords hab
  have himg := sec5p510_E_eq_image h hi hj
  have hcard : Nat.card (sec5p510_E t a b) = (sec5p510_E t a b : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, himg, Set.ncard_image_of_injective _ h.model.perm.injective, Set.ncard_coe_finset,
    sec5p510_Vs_card hij]

theorem sec5p510_E_le_A (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A) :
    sec5p510_E t a b ≤ A := by
  refine (Subgroup.closure_le A).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx <;> rw [hx]
  · exact sec5p510_t_mem_A h
  · exact hab.a_mem_A h
  · exact hab.b_mem_A h

theorem sec5p510_E_le_R (hy : Sec5B59Hyp) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) : sec5p510_E t a b ≤ sec5p510_R S Q₁ Q₂ := by
  obtain ⟨haR, hbR⟩ := sec5p510_ab_mem_R hy h4 h hQ hab
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx <;> rw [hx]
  · exact sec5p510_t_mem_R h.toSec5Ctx hQ
  · exact haR
  · exact hbR

theorem sec5p510_R_cases (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6) (h4 : Asc82FactReflCentQ6)
    (hCS : S ⊓ centralizer (L : Set G) = zpowers t)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) :
    sec5p510_R S Q₁ Q₂ = sec5p510_E t a b ∨
      (Nat.card ↥(sec5p510_R S Q₁ Q₂) = 16 ∧
        (sec5p510_E t a b).relIndex (sec5p510_R S Q₁ Q₂) = 2) := by
  have hle := sec5p510_E_le_R hy h4 h hQ hab
  have hE := sec5p510_card_E h hab
  have hdvd := Subgroup.card_dvd_of_le hle
  have hR16 := sec5p510_R_card_dvd hy hD h.toSec5Ctx hQ hCS
  rw [hE] at hdvd
  obtain ⟨m, hm⟩ := hdvd
  rw [hm] at hR16
  have hpos : 0 < Nat.card ↥(sec5p510_R S Q₁ Q₂) := Nat.card_pos
  have hm_le : 8 * m ≤ 16 := Nat.le_of_dvd (by norm_num) hR16
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hm2 : m = 1 ∨ m = 2 := by omega
  rcases hm2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  · right
    refine ⟨by omega, ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := sec5p510_E t a b) (K := sec5p510_R S Q₁ Q₂)
    rw [inf_of_le_left hle, hE] at h1
    omega

end CFSG.OddStandard.SmallF3.Omega
