module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionH
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionD

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

section Klein

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem e4_z_comm (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    Commute (e 4) (zOf e) :=
  zOf_central hone hlet (e 4) (e4_mem_H hlet)

theorem Esub_comm_gen (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    ∀ x ∈ Esub e, Commute x (e 4) ∧ Commute x (zOf e) := by
  have hab := e4_z_comm hone hlet
  intro x hx
  unfold Esub at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Commute.refl _, hab⟩
    · exact ⟨hab.symm, Commute.refl _⟩
  | one => exact ⟨Commute.one_left _, Commute.one_left _⟩
  | mul x y _ _ hx hy => exact ⟨hx.1.mul_left hy.1, hx.2.mul_left hy.2⟩
  | inv x _ hx => exact ⟨hx.1.inv_left, hx.2.inv_left⟩

theorem Esub_comm (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    ∀ x ∈ Esub e, ∀ y ∈ Esub e, Commute x y := by
  intro x hx y hy
  have hx' := Esub_comm_gen hone hlet x hx
  unfold Esub at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact hx'.1
    · exact hx'.2
  | one => exact Commute.one_right _
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂
  | inv y _ h => exact h.inv_right

theorem Esub_sq (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    ∀ x ∈ Esub e, x * x = 1 := by
  intro x hx
  unfold Esub at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact e4_sq hlet
    · exact zOf_mul_self hone hlet
  | one => exact one_mul 1
  | mul x y hxm hym h1 h2 =>
    have hc : Commute x y := Esub_comm hone hlet x hxm y hym
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc.eq]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  | inv x _ h =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [h, inv_one]

theorem Esub_eq_sup (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    Esub e = Subgroup.zpowers (e 4) ⊔ Subgroup.zpowers (zOf e) := by
  apply le_antisymm
  · unfold Esub
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)

theorem zpowers_e4_inf_z (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) [Finite G] :
    Subgroup.zpowers (e 4) ⊓ Subgroup.zpowers (zOf e) = ⊥ := by
  have hA : Nat.card ↥(Subgroup.zpowers (e 4)) = 2 := by
    rw [Nat.card_zpowers, orderOf_e4 hone hlet]
  have hdvd : Nat.card ↥(Subgroup.zpowers (e 4) ⊓ Subgroup.zpowers (zOf e)) ∣ 2 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(Subgroup.zpowers (e 4) ⊓ Subgroup.zpowers (zOf e)) ≠ 2 := by
    intro h
    have heq : Subgroup.zpowers (e 4) ⊓ Subgroup.zpowers (zOf e) = Subgroup.zpowers (e 4) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA, h])
    have he4 : e 4 ∈ Subgroup.zpowers (e 4) ⊓ Subgroup.zpowers (zOf e) := by
      rw [heq]
      exact Subgroup.mem_zpowers (e 4)
    have hz : Subgroup.zpowers (zOf e) ≤ H₁ ⊓ H₂ :=
      Subgroup.zpowers_le.mpr (zOf_mem_inf hlet)
    have he4K : e 4 ∈ H₁ ⊓ H₂ := hz he4.2
    exact e4_not_mem_K hone hlet (Subgroup.mem_sup_left he4K.1)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd h hne

theorem Esub_card (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) [Finite G] :
    Nat.card ↥(Esub e) = 4 := by
  have hc : e 4 * zOf e = zOf e * e 4 := e4_z_comm hone hlet
  have hA : Subgroup.zpowers (e 4) ≤ Subgroup.normalizer (Subgroup.zpowers (zOf e) : Set G) := by
    refine Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_le ?_)
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : e 4 * zOf e * (e 4)⁻¹ = zOf e := mul_inv_eq_iff_eq_mul.mpr hc
    rw [← conj_zpow, h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hprod := card_sup_mul_card_inf (Subgroup.zpowers (e 4)) (Subgroup.zpowers (zOf e)) hA
  rw [zpowers_e4_inf_z hone hlet, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_e4 hone hlet, orderOf_zOf hone hlet, ← Esub_eq_sup hone hlet] at hprod
  omega

theorem card_centralizer_involution [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) (a : G) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 576 := by
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  obtain ⟨c, hc⟩ := conj_zOf_of_orderOf hO a hord
  have hcz : Subgroup.centralizer ({zOf e} : Set G) = H := by
    ext x
    rw [Subgroup.mem_centralizer_iff, mem_H_iff_zOf hone hlet]
    simp only [Set.mem_singleton_iff, forall_eq]
  rw [← hc, card_centralizer_conj, hcz, hF.card_H]

theorem card_centralizer_inf_dvd_nine [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) (S : Subgroup G) (hS : Nat.card ↥S ∣ 3 ^ 10)
    (a : G) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ S) ∣ 9 := by
  have h1 : Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ S) ∣ 576 := by
    rw [← card_centralizer_involution hone hlet hF hO a ha2 ha1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ S) ∣ 3 ^ 10 :=
    dvd_trans (Subgroup.card_dvd_of_le inf_le_right) hS
  have h3 := Nat.dvd_gcd h1 h2
  norm_num at h3
  exact h3

end Klein

end CFSG.GH74.QTGen4.Recog.G23.P7
