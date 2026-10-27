module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316D

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G] [Finite G]

lemma fzl_card_eq_64 (n : ℕ) (hle : n ≤ 64) (hgt : 16 < n) (hmod : n % 3 = 1)
    (hdiv : n ∣ 64) : n = 64 := by
  interval_cases n <;> norm_num at *

lemma fzl_card_eq_32 (n : ℕ) (hle : n ≤ 64) (hgt : 16 < n) (hne : n ≠ 64)
    (hdiv : n ∣ 64) : n = 32 := by
  interval_cases n <;> norm_num at *

lemma fzl_card_cases (n : ℕ) (hle : n ≤ 64) (hge : 16 ≤ n) (hmod : n % 3 = 1)
    (hdiv : n ∣ 64) : n = 16 ∨ n = 64 := by
  interval_cases n <;> norm_num at *

lemma fzl_inv_conj_mem {rho : G} (hrho3 : rho ^ 3 = 1) {E : Subgroup G}
    (hrE : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E) : ∀ e ∈ E, rho⁻¹ * e * rho ∈ E := by
  intro e he
  have hρ : rho⁻¹ = rho ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hrho3]
  have hρ2 : (rho ^ 2)⁻¹ = rho := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hrho3]
  have key : rho * (rho * e * rho⁻¹) * rho⁻¹ = rho⁻¹ * e * rho := by
    have hA : rho * (rho * e * rho⁻¹) * rho⁻¹ = rho ^ 2 * e * (rho ^ 2)⁻¹ := by
      simp only [pow_two, mul_inv_rev]; group
    rw [hA, hρ2, hρ]
  rw [← key]
  exact hrE _ (hrE e he)

lemma fzl_rho_mem_sup_closure {P E : Subgroup G} {rho y : G}
    (hrho3 : rho ^ 3 = 1) (hcardP : Nat.card P = 64) (hcardE : Nat.card E = 16)
    (hEP : E ≤ P) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEcent : ∀ e ∈ E, ∀ p ∈ P, p * e = e * p)
    (hrP : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P) (hrE : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E)
    (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1)
    (hna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    {y : G} (hyP : y ∈ P) (hyE : y ∉ E)
    (hyN : rho * y * rho⁻¹ ∈ E ⊔ Subgroup.closure ({y} : Set G)) : False := by
  set N : Subgroup G := E ⊔ Subgroup.closure ({y} : Set G) with hN
  have hEN : E ≤ N := le_sup_left
  have hyN' : y ∈ N := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hNP : N ≤ P := by
    rw [hN]
    refine sup_le hEP ?_
    rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hyP
  have hNin : ∀ n ∈ N, rho * n * rho⁻¹ ∈ N := by
    intro n hn
    have hle : N.map (MulAut.conj rho) ≤ N := by
      rw [hN, Subgroup.map_sup, MonoidHom.map_closure]
      refine sup_le ?_ ?_
      · rintro z ⟨e, he, rfl⟩
        exact hEN (hrE e he)
      · rw [Subgroup.closure_le]
        rintro z ⟨w, hw, rfl⟩
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hyN
    exact hle ⟨n, hn, rfl⟩
  have hNmod : Nat.card N % 3 = 1 :=
    fzl_card_mod3_of_fpf hrho3 hNin (fun n hn hfix => hfpf n (hNP hn) hfix)
  have hN16 : 16 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hEN
    rwa [hcardE] at this
  have hNdiv : Nat.card N ∣ 64 := by
    have := Subgroup.card_dvd_of_le hNP
    rwa [hcardP] at this
  have hNne : N ≠ E := by
    intro h
    exact hyE (h ▸ hyN')
  have hNle : Nat.card N ≤ 64 := Nat.le_of_dvd (by norm_num) hNdiv
  have hNgt : 16 < Nat.card N := by
    have hle : 16 ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos hN16
    have hne : Nat.card N ≠ 16 := by
      intro h
      exact hNne (Subgroup.eq_of_le_of_card_ge (H := E) (K := N) hEN (by omega)).symm
    omega
  have hN64 : Nat.card N = 64 := fzl_card_eq_64 _ hNle hNgt hNmod hNdiv
  have hNPeq : N = P := Subgroup.eq_of_le_of_card_ge hNP (by omega)
  have hMcomm : IsMulCommutative N := by
    rw [hN]
    have heq : E ⊔ Subgroup.closure ({y} : Set G) = Subgroup.closure ((E : Set G) ∪ {y}) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq]
    rw [heq]
    apply Subgroup.isMulCommutative_closure
    intro a ha b hb _
    simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
    rcases ha with haE | ha_eq
    · rcases hb with hbE | hb_eq
      · exact hEcomm a haE b hbE
      · rw [hb_eq]; exact (hEcent a haE y hyP).symm
    · rw [ha_eq]
      rcases hb with hbE | hb_eq
      · exact hEcent b hbE y hyP
      · rw [hb_eq]
  obtain ⟨a, haP, b, hbP, hab⟩ := hna
  haveI : IsMulCommutative P := hNPeq ▸ hMcomm
  exact hab (Subgroup.mul_comm_of_mem_isMulCommutative P haP hbP)

lemma fzl_mem_of_coset {P E : Subgroup G} {rho y : G}
    (hrho3 : rho ^ 3 = 1) (hcardP : Nat.card P = 64) (hcardE : Nat.card E = 16)
    (hEP : E ≤ P) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEcent : ∀ e ∈ E, ∀ p ∈ P, p * e = e * p)
    (hrP : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P) (hrE : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E)
    (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1)
    (hna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    {y : G} (hyP : y ∈ P) (hy : y⁻¹ * (rho * y * rho⁻¹) ∈ E) : y ∈ E := by
  by_contra hyE
  have hyN : rho * y * rho⁻¹ ∈ E ⊔ Subgroup.closure ({y} : Set G) := by
    have h1 : y ∈ E ⊔ Subgroup.closure ({y} : Set G) :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have h2 : y⁻¹ * (rho * y * rho⁻¹) ∈ E ⊔ Subgroup.closure ({y} : Set G) :=
      Subgroup.mem_sup_left hy
    have : rho * y * rho⁻¹ = y * (y⁻¹ * (rho * y * rho⁻¹)) := by group
    rw [this]
    exact Subgroup.mul_mem _ h1 h2
  exact fzl_rho_mem_sup_closure (y := y) hrho3 hcardP hcardE hEP hEcomm hEcent hrP hrE hfpf hna
    hyP hyE hyN

end CFSG.OddStandard.SmallF3.FritzII
