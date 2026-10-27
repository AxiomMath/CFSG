module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cTInterp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cTCount
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Finset

section Finrank

variable {F L : Type} [Field F] [Field L] [Algebra F L]

theorem funRep_monoFun_zero (g : SLm F) (k : ℕ) :
    funRep F L g (monoFun F L k 0) = fun v =>
      (algebraMap F L (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 0) * algebraMap F L (v 0) +
        algebraMap F L (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 1) * algebraMap F L (v 1)) ^ k := by
  funext v
  simp [funRep, monoFun]

theorem funRep_monoFun_zero_expand (g : SLm F) (k : ℕ) :
    funRep F L g (monoFun F L k 0) = ∑ m ∈ range (k + 1),
      ((k.choose m : L) * (algebraMap F L (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 0) ^ m *
        algebraMap F L (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 1) ^ (k - m))) •
        monoFun F L m (k - m) := by
  rw [funRep_monoFun_zero]
  funext v
  rw [Finset.sum_apply, add_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.smul_apply, monoFun, smul_eq_mul, mul_pow]
  ring

theorem exists_SL_row (b : F) : ∃ g : SLm F, ((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧
    ((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 1 = b := by
  let M : SLm F := ⟨!![1, -b; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨M, ?_⟩
  have h : ((M⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) F) := Matrix.SpecialLinearGroup.coe_inv M
  rw [h]
  simp [M, Matrix.adjugate_fin_two]

variable (p n : ℕ)

def monoIdx (A : ℕ) : Finset ℕ := (range (p ^ n)).filter (fun m => ¬ p ∣ Nat.choose A m)

variable {p n}

theorem mem_monoIdx {A m : ℕ} : m ∈ monoIdx p n A ↔ m < p ^ n ∧ ¬ p ∣ Nat.choose A m := by
  simp [monoIdx]

theorem le_of_mem_monoIdx {A m : ℕ} (hm : m ∈ monoIdx p n A) : m ≤ A := by
  by_contra h
  rw [mem_monoIdx, Nat.choose_eq_zero_of_lt (not_le.mp h)] at hm
  exact hm.2 (dvd_zero p)

theorem steinbergSub_le_span [CharP L p] (A : ℕ) (hA : A < p ^ n) :
    steinbergSub F L A ≤
      Submodule.span L (Set.range fun m : monoIdx p n A => monoFun F L m (A - m)) := by
  unfold steinbergSub
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, rfl⟩
  show funRep F L g (monoFun F L A 0) ∈
    (Submodule.span L (Set.range fun m : monoIdx p n A => monoFun F L m (A - m)) : Set _)
  rw [SetLike.mem_coe, funRep_monoFun_zero_expand]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hdvd : p ∣ Nat.choose A m
  · have h0 : ((A.choose m : ℕ) : L) = 0 := (CharP.cast_eq_zero_iff L p _).mpr hdvd
    rw [h0, zero_mul, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨m, ?_⟩, rfl⟩)
    exact mem_monoIdx.mpr ⟨lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hm)) hA, hdvd⟩

theorem monoFun_mem_steinbergSub [CharP L p] [Fintype F] (hF : Fintype.card F = p ^ n) (A : ℕ)
    (hA : A < p ^ n) {m : ℕ} (hm : m ∈ monoIdx p n A) :
    monoFun F L m (A - m) ∈ steinbergSub F L A := by
  have hmA : m ≤ A := le_of_mem_monoIdx hm
  have hnd : ¬ p ∣ Nat.choose A m := (mem_monoIdx.mp hm).2
  obtain ⟨lam, hlam⟩ := exists_interp (F := F) (L := L) (k := A - m) (by rw [hF]; omega)
  choose g hg0 hg1 using fun b : F => exists_SL_row b
  have key : ∑ b : F, lam b • funRep F L (g b) (monoFun F L A 0) =
      ((A.choose m : ℕ) : L) • monoFun F L m (A - m) := by
    have e1 : ∀ b : F, lam b • funRep F L (g b) (monoFun F L A 0) =
        ∑ m' ∈ range (A + 1), (lam b * ((A.choose m' : L) * (algebraMap F L b) ^ (A - m'))) •
          monoFun F L m' (A - m') := by
      intro b
      rw [funRep_monoFun_zero_expand, hg0 b, hg1 b, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [smul_smul]
      simp
    simp_rw [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ m' ∈ range (A + 1), ∑ b : F, (lam b * ((A.choose m' : L) *
        (algebraMap F L b) ^ (A - m'))) • monoFun F L m' (A - m') =
        ((A.choose m' : L) * (if A - m' = A - m then 1 else 0)) • monoFun F L m' (A - m') := by
      intro m' hm'
      rw [← Finset.sum_smul]
      congr 1
      rw [← hlam (A - m') (by rw [hF]; omega), Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_congr rfl e2, Finset.sum_eq_single m]
    · simp
    · intro m' hm' hne
      have : A - m' ≠ A - m := by
        have := mem_range.mp hm'
        omega
      simp [this]
    · intro hnm
      exact absurd (mem_range.mpr (by omega)) hnm
  have hne : ((A.choose m : ℕ) : L) ≠ 0 := by
    intro h
    exact hnd ((CharP.cast_eq_zero_iff L p _).mp h)
  have : monoFun F L m (A - m) = ((A.choose m : ℕ) : L)⁻¹ • ∑ b : F, lam b • funRep F L (g b) (monoFun F L A 0) := by
    rw [key, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨g b, rfl⟩

theorem linearIndependent_monoFun [Fintype F] (hF : Fintype.card F = p ^ n) (A : ℕ) :
    LinearIndependent L (fun m : monoIdx p n A => monoFun F L m (A - m)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m₀
  obtain ⟨lam, hlam⟩ := exists_interp (F := F) (L := L) (k := m₀)
    (by rw [hF]; exact (mem_monoIdx.mp m₀.2).1)
  have hev : ∀ b : F, ∑ m : monoIdx p n A, c m * (algebraMap F L b) ^ (m : ℕ) = 0 := by
    intro b
    have := congrFun hc ![b, 1]
    simpa [monoFun, Finset.sum_apply] using this
  have h2 : ∑ b : F, lam b * (∑ m : monoIdx p n A, c m * (algebraMap F L b) ^ (m : ℕ)) = c m₀ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e : ∀ m : monoIdx p n A, ∑ b : F, lam b * (c m * (algebraMap F L b) ^ (m : ℕ)) =
        c m * (if (m : ℕ) = m₀ then 1 else 0) := by
      intro m
      rw [← hlam m (by rw [hF]; exact (mem_monoIdx.mp m.2).1), Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp_rw [e]
    rw [Finset.sum_eq_single m₀]
    · simp
    · intro m _ hne
      have hne' : (m : ℕ) ≠ m₀ := fun h => hne (Subtype.ext h)
      simp [hne']
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← h2]
  exact Finset.sum_eq_zero fun b _ => by rw [hev b, mul_zero]

end Finrank

theorem steinberg_finrank_holds : SteinbergFinrankStmt := by
  intro p n F L _ _ _ _ hp _ hF A hA
  have := Fact.mk hp
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : CharP F p := charP_of_card_eq_prime_pow hF'
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  have hspan : steinbergSub F L A =
      Submodule.span L (Set.range fun m : monoIdx p n A => monoFun F L m (A - m)) :=
    le_antisymm (steinbergSub_le_span A hA)
      (Submodule.span_le.mpr (by
        rintro _ ⟨m, rfl⟩
        exact monoFun_mem_steinbergSub hF' A hA m.2))
  rw [hspan, finrank_span_eq_card (linearIndependent_monoFun hF' A), Fintype.card_coe]
  exact card_filter_not_dvd_choose hp n A hA

end CFSG.GH74.GLS.Stage4.Rest
