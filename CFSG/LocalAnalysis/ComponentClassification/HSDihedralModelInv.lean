module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelKlein
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsRank
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralDihedral

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.Model

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem exists_pow_order_four {G : Type} [Group G] {x : G} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1)
    (hx2 : x ^ 2 ≠ 1) : ∃ j : ℕ, (x ^ j) ^ 2 ≠ 1 ∧ (x ^ j) ^ 4 = 1 := by
  classical
  set e := Nat.find hx
  have he : x ^ 2 ^ e = 1 := Nat.find_spec hx
  have he2 : 2 ≤ e := by
    by_contra h
    push Not at h
    interval_cases hk : e
    · rw [pow_zero, pow_one] at he
      exact hx2 (by rw [he, one_pow])
    · rw [pow_one] at he
      exact hx2 he
  refine ⟨2 ^ (e - 2), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ]
    exact Nat.find_min hx (by omega)
  · rw [← pow_mul, show 4 = 2 ^ 2 by norm_num, ← pow_add, show e - 2 + 2 = e by omega, he]

theorem card_centralizer_le_two
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) {σ : PGammaL2 F}
    (hσ1 : σ.right = 1) (hσL : σ ∉ pGammaL2PSLRange F) (hσ2 : σ ^ 2 = 1) :
    Nat.card ↥((T : Subgroup (PSL2 F)).map (incl F) ⊓ centralizer ({σ} : Set (PGammaL2 F))) ≤
      2 := by
  classical
  set D₀ := (T : Subgroup (PSL2 F)).map (incl F)
  set C := D₀ ⊓ centralizer ({σ} : Set (PGammaL2 F))
  have hD₀L : ∀ d ∈ D₀, d ∈ pGammaL2PSLRange F := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  have hD₀r : ∀ d ∈ D₀, d.right = 1 := by
    rintro _ ⟨t, -, rfl⟩
    rfl
  have hD₀2 : IsPGroup 2 D₀ := T.isPGroup'.map (incl F)
  have hσne : σ ≠ 1 := fun h => hσL (h ▸ one_mem _)
  by_contra hlt
  push Not at hlt
  by_cases hA : ∃ ρ ∈ C, ρ ^ 2 ≠ 1
  · obtain ⟨ρ, hρC, hρ2⟩ := hA
    obtain ⟨hρD, hρσ⟩ := mem_inf.mp hρC
    rw [mem_centralizer_singleton_iff] at hρσ
    have hρ2' : ∃ n : ℕ, ρ ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hD₀2 ⟨ρ, hρD⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    obtain ⟨j, hj2, hj4⟩ := exists_pow_order_four hρ2' hρ2
    set ρ' := ρ ^ j
    have hρ'D : ρ' ∈ D₀ := pow_mem hρD j
    have hρ'σ : ρ' * σ = σ * ρ' := ((show Commute ρ σ from hρσ).pow_left j)
    set a := ρ' ^ 2
    have haσ : a * σ = σ * a := ((show Commute ρ' σ from hρ'σ).pow_left 2)
    have ha2 : a ^ 2 = 1 := by rw [← pow_mul]; exact hj4
    have haD : a ∈ D₀ := pow_mem hρ'D 2
    have hle : zpowers a ⊔ zpowers σ ≤ (fieldProj F).ker :=
      sup_le (zpowers_le.mpr (hD₀r a haD)) (zpowers_le.mpr hσ1)
    have hmem := klein_centralizer hodd (fun e he => hle he)
      (card_E4 ha2 hσ2 haσ hj2 hσne (fun h => hσL (h ▸ hD₀L a haD)))
      (elem_E4 ha2 hσ2 haσ).sq_eq_one (hD₀r ρ' hρ'D)
      (fun e he => commute_of_mem_sup (by rw [← pow_succ, ← pow_succ']) hρ'σ he)
    exact hj2 ((elem_E4 ha2 hσ2 haσ).sq_eq_one ρ' hmem)
  · push Not at hA
    have hne : ∃ a ∈ C, a ≠ 1 := by
      by_contra h
      push Not at h
      have := card_le_of_forall_mem_finset C {1} fun x hx => by simp [h x hx]
      simp at this
      omega
    obtain ⟨a, haC, ha1⟩ := hne
    have hne2 : ∃ b ∈ C, b ≠ 1 ∧ b ≠ a := by
      by_contra h
      push Not at h
      have := card_le_of_forall_mem_finset C {1, a} fun x hx => by
        by_cases hx1 : x = 1
        · simp [hx1]
        · simp [h x hx hx1]
      have := this.trans (Finset.card_le_two)
      omega
    obtain ⟨b, hbC, hb1, hba⟩ := hne2
    have ha2 := hA a haC
    have hb2 := hA b hbC
    have hab : a * b = b * a := by
      have h := hA _ (mul_mem haC hbC)
      have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ha2])
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hb2])
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_two, h])).symm
        _ = b * a := by rw [mul_inv_rev, hainv, hbinv]
    have haD := (mem_inf.mp haC).1
    have hbD := (mem_inf.mp hbC).1
    have hle : zpowers a ⊔ zpowers b ≤ D₀ := sup_le (zpowers_le.mpr haD) (zpowers_le.mpr hbD)
    have hσE := klein_centralizer hodd (fun e he => hD₀r e (hle he))
      (card_E4 ha2 hb2 hab ha1 hb1 hba) (elem_E4 ha2 hb2 hab).sq_eq_one hσ1
      (fun e he => commute_of_mem_sup
        (mem_centralizer_singleton_iff.mp (mem_inf.mp haC).2).symm
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hbC).2).symm he)
    exact hσL (hD₀L σ (hle hσE))

end CFSG.ComponentClassification.HSDihedral.Model
