module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S105S
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Idx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_class_T [Finite G] (h37 : Asc82Lemma37) (h103 : Asc82Lemma103) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hST : S ≤ T) (hidx : S.relIndex T = 2) :
    conjClassIn T t = {t, t * z} := by
  have hzt : z * t = t * z :=
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hctx.mem_S)
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hnorm : T ≤ normalizer (S : Set G) := sec11_le_normalizer_of_relIndex_two hST hidx
  have h103' : omega1 (centerIn S) = zpowers z ⊔ zpowers t := h103 G t L S z hctx.toSec10Z
  have ht_omega : t ∈ omega1 (centerIn S) := by
    rw [h103']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hcases : ∀ σ ∈ T, σ * t * σ⁻¹ = t ∨ σ * t * σ⁻¹ = t * z := by
    intro σ hσT
    have hconj : σ * t * σ⁻¹ ∈ zpowers z ⊔ zpowers t := by
      have h := sec10_conj_mem_omega1 (hnorm (T.inv_mem hσT)) ht_omega
      rw [h103'] at h
      simpa using h
    have hx2 : orderOf (σ * t * σ⁻¹) = 2 := by
      have h1 : orderOf ((MulAut.conj σ) t) = orderOf t := MulEquiv.orderOf_eq _ _
      have h2 : (MulAut.conj σ) t = σ * t * σ⁻¹ := by rw [MulAut.conj_apply]
      rw [h2] at h1
      exact h1.trans hctx.involution
    rcases sec10_two_elem_cases hzt hz2 hctx.involution hconj hx2 with h | h | h
    · exfalso
      exact sec10_not_conj_z h37 hctx σ (by rw [← h]; group)
    · exact Or.inl h
    · exact Or.inr h
  have hclass_sub : conjClassIn T t ⊆ {t, t * z} := by
    rintro y ⟨σ, hσT, rfl⟩
    rcases hcases σ hσT with h | h
    · simp [h]
    · simp [h]
  have hmem_t : t ∈ conjClassIn T t := ⟨1, T.one_mem, by simp⟩
  have hmem_tz : t * z ∈ conjClassIn T t := by
    have hnotTS : ¬ T ≤ S := by
      intro hle
      have h1 : S.relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hle
      rw [hidx] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨τ, hτT, hτS⟩ := SetLike.not_le_iff_exists.mp hnotTS
    have hτC : τ ∉ centralizer ({t} : Set G) := by
      intro hτc
      let Q : Subgroup G := T ⊓ centralizer ({t} : Set G)
      have hQ2 : IsPGroup 2 Q := hT2.to_le (inf_le_left : Q ≤ T)
      have hQS : Q = S :=
        hctx.sylow.eq_of_le (inf_le_right : Q ≤ centralizer ({t} : Set G)) hQ2
          (le_inf hST hctx.sylow.1)
      exact hτS (hQS ▸ (⟨hτT, hτc⟩ : τ ∈ Q))
    have hxne : τ * t * τ⁻¹ ≠ t := by
      intro h
      apply hτC
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc τ * t = (τ * t * τ⁻¹) * τ := by group
        _ = t * τ := by rw [h]
    rcases hcases τ hτT with h | h
    · exact absurd h hxne
    · exact ⟨τ, hτT, h.symm⟩
  refine Set.ext fun y => ⟨fun hy => hclass_sub hy, fun hy => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact hmem_t
  · exact hmem_tz

end CFSG.OddStandard.SmallF3.Omega
