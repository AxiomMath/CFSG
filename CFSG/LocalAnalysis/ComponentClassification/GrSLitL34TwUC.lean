module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwKleinB
public import Certificates.Certificate33209

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four

private def noSwapA (L : Subgroup (Equiv.Perm (Fin 42))) : Subgroup WrE where
  carrier := {x | x.e = false ∧ x.a ∈ L}
  one_mem' := ⟨rfl, L.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, WrE.mul_def, hy.1]
    simp only [Bool.false_eq_true, ↓reduceIte, hx.1, Bool.xor_false, true_and]
    exact L.mul_mem hx.2 hy.2
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, WrE.inv_def, hx.1]
    simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    exact L.inv_mem hx.2

private def V : Set (Fin 4 × Fin 4 × Bool) := {(0, 0, false), (1, 1, false)}

private theorem V_zero : ((0 : Fin 4), (0 : Fin 4), false) ∈ V := by simp [V]

private theorem V_mul : ∀ c ∈ V, ∀ d ∈ V, qmulC c d ∈ V := by
  intro c hc d hd
  simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd ⊢
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> decide

private theorem V_inv : ∀ c ∈ V, ∀ d, qmulC c d = (0, 0, false) → d ∈ V := by
  intro c hc d hd
  simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
  rcases hc with rfl | rfl <;> revert d <;> decide


theorem codeSet_ne_UC {X : Subgroup WrE} (hXP : X ≤ Pw) (hN : N0w ≤ X) (hX : GoodX X) :
    codeSet X ≠ UC := by
  intro hUC
  obtain ⟨t, htP, hcost, htt, hgt', hzt', hcomm56, htg⟩ := Certificates.certificate33209
  have hg2 : g₅ * g₅ = 1 := sq_g5
  have hg62 : g₆ * g₆ = 1 := sq_g6
  have hzz : (g₅ * g₆) * (g₅ * g₆) = 1 := by
    calc (g₅ * g₆) * (g₅ * g₆) = g₅ * (g₆ * g₅) * g₆ := by group
      _ = g₅ * (g₅ * g₆) * g₆ := by rw [← hcomm56]
      _ = (g₅ * g₅) * (g₆ * g₆) := by group
      _ = 1 := by rw [hg2, hg62, one_mul]
  have hgz' : g₅ * (g₅ * g₆) = (g₅ * g₆) * g₅ := by
    rw [mul_assoc, ← hcomm56]
  have ht1 : t ≠ 1 := fun h => by
    rw [h, cosRA_one] at hcost
    exact absurd hcost (by decide)
  have hg1 : g₅ ≠ 1 := fun h => by
    have := cosRA_g5
    rw [h, cosRA_one] at this
    exact absurd this (by decide)
  have hzP : g₅ * g₆ ∈ RA := RA.mul_mem g₅_mem_RA g₆_mem_RA
  obtain ⟨A, hA⟩ : ∃ A : WrE, A = ⟨g₅, g₅, false⟩ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : WrE, B = ⟨g₅, t, false⟩ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : WrE, C = ⟨t, g₅, false⟩ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : WrE, D = ⟨g₅ * g₆, g₅ * g₆, false⟩ := ⟨_, rfl⟩
  have hAP : A ∈ Pw := hA ▸ (⟨g₅_mem_RA, g₅_mem_RA⟩ : (⟨g₅, g₅, false⟩ : WrE) ∈ Pw)
  have hBP : B ∈ Pw := hB ▸ (⟨g₅_mem_RA, htP⟩ : (⟨g₅, t, false⟩ : WrE) ∈ Pw)
  have hCP : C ∈ Pw := hC ▸ (⟨htP, g₅_mem_RA⟩ : (⟨t, g₅, false⟩ : WrE) ∈ Pw)
  have hDP : D ∈ Pw := hD ▸ (⟨hzP, hzP⟩ : (⟨g₅ * g₆, g₅ * g₆, false⟩ : WrE) ∈ Pw)
  have hcA : cc A = (1, 1, false) := by
    rw [hA]; show (cosRA g₅, cosRA g₅, false) = _; rw [cosRA_g5]
  have hcB : cc B = (1, 1, false) := by
    rw [hB]; show (cosRA g₅, cosRA t, false) = _; rw [cosRA_g5, hcost]
  have hcC : cc C = (1, 1, false) := by
    rw [hC]; show (cosRA t, cosRA g₅, false) = _; rw [cosRA_g5, hcost]
  have hcD : cc D = (3, 3, false) := by
    rw [hD]; show (cosRA (g₅ * g₆), cosRA (g₅ * g₆), false) = _; rw [cosRA_g56]
  have hmemX : ∀ y : WrE, y ∈ Pw → cc y ∈ UC → y ∈ X := fun y hy hc =>
    (mem_iff_cc hXP hN y).2 ⟨hy, hUC ▸ hc⟩
  have hAX : A ∈ X := hmemX A hAP (by rw [hcA]; exact Or.inl ⟨rfl, rfl⟩)
  have hBX : B ∈ X := hmemX B hBP (by rw [hcB]; exact Or.inl ⟨rfl, rfl⟩)
  have hCX : C ∈ X := hmemX C hCP (by rw [hcC]; exact Or.inl ⟨rfl, rfl⟩)
  have hDX : D ∈ X := hmemX D hDP (by rw [hcD]; exact Or.inl ⟨rfl, rfl⟩)
  have hvP : (⟨1, g₅ * g₆, true⟩ : WrE) ∈ Pw := s1_mem_Pw
  have hvX : (⟨1, g₅ * g₆, true⟩ : WrE) ∈ X :=
    hmemX _ hvP (by rw [cc_s1]; exact Or.inr ⟨rfl, by decide⟩)
  have hvv : (⟨1, g₅ * g₆, true⟩ : WrE) * ⟨1, g₅ * g₆, true⟩ = D := by
    rw [hD, swap_sq, mul_one, one_mul]
  have hv4 : (⟨1, g₅ * g₆, true⟩ : WrE) ^ 4 = 1 :=
    pow_four_swap _ _ (by rw [mul_one]; exact hzz) (by rw [one_mul]; exact hzz)
  have hmin : ∀ h ∈ X, h.e = true → orderOf (⟨1, g₅ * g₆, true⟩ : WrE) ≤ orderOf h :=
    fun h hh he => (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hv4)).trans
      (four_le_orderOf he (hX.h13 h hh he))
  have hA2 : A * A = 1 := by rw [hA]; exact mk_sq _ _ hg2 hg2
  have hB2 : B * B = 1 := by rw [hB]; exact mk_sq _ _ hg2 htt
  have hC2 : C * C = 1 := by rw [hC]; exact mk_sq _ _ htt hg2
  have hD2 : D * D = 1 := by rw [hD]; exact mk_sq _ _ hzz hzz
  have hAB : A * B = B * A := by rw [hA, hB]; exact mk_comm _ _ _ _ rfl hgt'
  have hAC : A * C = C * A := by rw [hA, hC]; exact mk_comm _ _ _ _ hgt' rfl
  have hBC : B * C = C * B := by rw [hB, hC]; exact mk_comm _ _ _ _ hgt' hgt'.symm
  have hAD : A * D = D * A := by rw [hA, hD]; exact mk_comm _ _ _ _ hgz' hgz'
  have hBD : B * D = D * B := by rw [hB, hD]; exact mk_comm _ _ _ _ hgz' hzt'.symm
  have hCD : C * D = D * C := by rw [hC, hD]; exact mk_comm _ _ _ _ hzt'.symm hgz'
  have hA1 : A ≠ 1 := fun h => hg1 (by rw [hA] at h; exact congrArg WrE.a h)
  have hBA : B ∉ zpowers A := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers hA2 h with h | h
    · exact hg1 (by rw [hB] at h; exact congrArg WrE.a h)
    · exact htg (by rw [hA, hB] at h; exact congrArg WrE.b h)
  have hQ : zpowers B ⊔ zpowers A ≤ noSwapA (zpowers g₅) :=
    sup_le (zpowers_le.2 (by rw [hB]; exact ⟨rfl, mem_zpowers g₅⟩))
      (zpowers_le.2 (by rw [hA]; exact ⟨rfl, mem_zpowers g₅⟩))
  have hCQ : C ∉ zpowers B ⊔ zpowers A := fun h => by
    have := (hQ h).2
    rw [hC] at this
    rcases eq_one_or_eq_of_mem_zpowers hg2 this with h | h
    · exact ht1 h
    · exact htg h
  have hE8 := isEightGroup_of_three hA2 hB2 hC2 hAB hAC hBC hA1 hBA hCQ
  let PV := preimg V V_zero V_mul V_inv
  have hF : zpowers C ⊔ (zpowers B ⊔ zpowers A) ≤ PV :=
    sup_le (zpowers_le.2 (by
        refine mem_preimg.2 ⟨hCP, ?_⟩
        rw [hcC]; simp [V]))
      (sup_le (zpowers_le.2 (by
          refine mem_preimg.2 ⟨hBP, ?_⟩
          rw [hcB]; simp [V]))
        (zpowers_le.2 (by
          refine mem_preimg.2 ⟨hAP, ?_⟩
          rw [hcA]; simp [V])))
  have hDF : D ∉ zpowers C ⊔ (zpowers B ⊔ zpowers A) := fun h => by
    have := (mem_preimg.1 (hF h)).2
    rw [hcD] at this
    simp [V] at this
  refine hX.h22 _ hvX rfl hmin ⟨zpowers C ⊔ (zpowers B ⊔ zpowers A), ?_, hE8, D, ?_, hD2, ?_, hDF⟩
  · rw [hvv]
    exact sup_le (zpowers_le.2 (mem_inf.2 ⟨hCX, mem_centralizer_singleton_iff.2 hCD⟩))
      (sup_le (zpowers_le.2 (mem_inf.2 ⟨hBX, mem_centralizer_singleton_iff.2 hBD⟩))
        (zpowers_le.2 (mem_inf.2 ⟨hAX, mem_centralizer_singleton_iff.2 hAD⟩)))
  · rw [hvv]
    exact mem_inf.2 ⟨hDX, mem_centralizer_singleton_iff.2 rfl⟩
  · have hle : zpowers C ⊔ (zpowers B ⊔ zpowers A) ≤ centralizer ({D} : Set WrE) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hCD))
        (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hBD))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 hAD)))
    intro e he
    exact (mem_centralizer_singleton_iff.1 (hle he)).symm

end CFSG.ComponentClassification.GrSLit.L34Tw
