module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseCatalog
public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Equiv Subgroup CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

namespace A8Datum

@[expose] def t₁ : alternatingGroup (Fin 8) :=
  ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def t₂ : alternatingGroup (Fin 8) :=
  ⟨swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def t₃ : alternatingGroup (Fin 8) :=
  ⟨swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def mulω : alternatingGroup (Fin 8) :=
  ⟨List.formPerm [1, 2, 4, 3, 6, 7, 5], Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem datum : E8Datum t₁ t₂ t₃ mulω where
  ne_one := by decide
  sq := by decide
  comm₁₂ := (by decide : t₁ * t₂ = t₂ * t₁)
  comm₁₃ := (by decide : t₁ * t₃ = t₃ * t₁)
  conj₁ := by decide
  conj₂ := by decide
  conj₃ := by decide

end A8Datum

theorem kgA8CoverElem_proved : KGA8CoverElem := by
  intro K _ _ _ ⟨e⟩
  set φ : K →* alternatingGroup (Fin 8) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center K := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff x).mp (e.injective (by rw [map_one]; exact hx))
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, s₁, s₂, s₃, c₁₂, c₁₃, c₂₃⟩ :=
    A8Datum.datum.exists_lift hφ hker
  set u : Fin 3 → K := ![b₁, b₂, b₃] with hu
  have hprod : ∀ v : Fin 3 → Fin 2, (List.ofFn fun i => u i ^ (v i : ℕ)).prod =
      b₁ ^ (v 0 : ℕ) * b₂ ^ (v 1 : ℕ) * b₃ ^ (v 2 : ℕ) := fun v => by
    simp [u, List.ofFn_succ, mul_assoc]
  have hsq : ∀ i, u i ^ 2 = 1 := fun i => by fin_cases i <;> simpa [u]
  have hcomm : ∀ i j, Commute (u i) (u j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [u, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two] <;>
      first
        | exact Commute.refl _ | exact c₁₂ | exact c₁₂.symm | exact c₁₃ | exact c₁₃.symm
        | exact c₂₃ | exact c₂₃.symm
  obtain ⟨ψ, hψi, -⟩ := exists_prodHom u hsq hcomm
    (fun v hv hv1 => by
      rw [hprod] at hv1
      have himg := congrArg φ hv1
      simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃] at himg
      refine A8Datum.datum.prod_ne_one (v 0) (v 1) (v 2) (fun h => hv ?_) himg
      simp only [Prod.mk.injEq] at h
      funext i
      fin_cases i
      exacts [h.1, h.2.1, h.2.2])
  refine ⟨ψ.range, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    rw [← map_mul, ← sq, pi_pow_two_eq_one, map_one]
  · have hcard : Nat.card ψ.range = 2 ^ 3 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv]
      simp [Nat.card_eq_fintype_card]
    rw [hcard]
    norm_num

end CFSG.EvenSporadicStandard.HSStd.PumpT
