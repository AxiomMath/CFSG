module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTCoverElem

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Equiv Subgroup CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift

theorem three_le_pRank_of_e8Datum {J X : Type*} [Group J] [Finite J] [Group X] {φ : J →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J) {a₁ a₂ a₃ n : X}
    (h : E8Datum a₁ a₂ a₃ n) : 3 ≤ CFSG.pRank 2 J := by
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, s₁, s₂, s₃, c₁₂, c₁₃, c₂₃⟩ := h.exists_lift hφ hker
  set u : Fin 3 → J := ![b₁, b₂, b₃] with hu
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
  refine le_pRank_two_of_independent u hsq hcomm fun v hv hv1 => ?_
  rw [hprod] at hv1
  have himg := congrArg φ hv1
  simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃] at himg
  refine h.prod_ne_one (v 0) (v 1) (v 2) (fun h0 => hv ?_) himg
  simp only [Prod.mk.injEq] at h0
  funext i
  fin_cases i
  exacts [h0.1, h0.2.1, h0.2.2]

theorem three_le_pRank_of_e8Datum_quotient {J X : Type*} [Group J] [Finite J] [Group X]
    (e : J ⧸ Subgroup.center J ≃* X) {a₁ a₂ a₃ n : X} (h : E8Datum a₁ a₂ a₃ n) :
    3 ≤ CFSG.pRank 2 J := by
  refine three_le_pRank_of_e8Datum (φ := e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ h
  intro x hx
  have h1 : e (QuotientGroup.mk' (Subgroup.center J) x) = 1 := hx
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

namespace A8Datum

noncomputable def embed {n : ℕ} (hn : 8 ≤ n) :
    alternatingGroup (Fin 8) →* alternatingGroup (Fin n) :=
  ((Perm.viaEmbeddingHom (Fin.castLEEmb hn)).comp (alternatingGroup (Fin 8)).subtype).codRestrict
    _ fun σ => by
      rw [Perm.mem_alternatingGroup, MonoidHom.comp_apply, Perm.viaEmbeddingHom_apply,
        Perm.viaEmbedding, Perm.sign_extendDomain]
      exact σ.2

theorem embed_injective {n : ℕ} (hn : 8 ≤ n) : Function.Injective (embed hn) := by
  intro σ τ h
  exact Subtype.ext (Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn) (congrArg Subtype.val h))

end A8Datum

theorem three_le_pRank_alt_cover {J : Type*} [Group J] [Finite J] {n : ℕ} (hn : 8 ≤ n)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin n)) : 3 ≤ CFSG.pRank 2 J :=
  three_le_pRank_of_e8Datum_quotient e
    (A8Datum.datum.map (A8Datum.embed hn) (A8Datum.embed_injective hn))

end CFSG.EvenSporadicStandard.HSStd.PumpT
