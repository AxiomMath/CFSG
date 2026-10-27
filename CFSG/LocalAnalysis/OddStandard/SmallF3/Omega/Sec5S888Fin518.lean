module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L5b3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888W1c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma518b_of (h514 : Asc82Lemma514) (h515c : Asc82Lemma515c)
    (h516a : Asc82Lemma516a) (h517 : Asc82Lemma517) (hpar : Asc82Lemma518Parity)
    (h52a : Asc82Lemma52a) (h37 : Asc82Lemma37) (hF3 : Asc82FactOm6CentD)
    (hF6 : Asc82FactOm6NRank) : Asc82Lemma518b := by
  intro G _ _ t L S z r B A K₁ K₂ h c n U hU hab hn
  by_contra hn3
  have hn4 : 4 ≤ n := by omega
  have h16 : 16 ≤ (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G))
      (Qsub K₁ K₂ h)).relIndex U := by
    rw [hn]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
  obtain ⟨e, he, heQ, hfix⟩ := exists_delta_of_ctx h514 h517 hpar c hU hab h16
  obtain ⟨S', r', B', A', P₁, P₂, h', hc', hΓ⟩ := h515c G t L S z r B A K₁ K₂ h c e he
  have hQ : Qsub P₁ P₂ h' = Qsub K₁ K₂ h := sec5_qsub_eq_of_gamma_eq hΓ
  have hCN : ∀ u ∈ U, ∀ x ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G))
      (Qsub K₁ K₂ h), u * x * u⁻¹ ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G))
        (Qsub K₁ K₂ h) := fun u hu x hx => centralizerMod_conj_mem h514 c (hU hu) hx
  have hQC := qsub_le_centralizerMod h514 c
  have hCleN : centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) ≤
      normalizer (Qsub K₁ K₂ h : Set G) := fun x hx => hx.1
  have hUC : U ⊔ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) ≤
      normalizer (Qsub K₁ K₂ h : Set G) := sup_le hU hCleN
  have hU'ab : IsElemAbelianModSub
      (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h))
      ((U ⊔ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) ⊓
        centralizer ({e} : Set G)) :=
    (isElemAbelianModSub_sup hCN hab).mono inf_le_left
  have hle : (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)).relIndex U ≤
      (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)).relIndex
        ((U ⊔ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) ⊓
          centralizer ({e} : Set G)) := by
    refine relIndex_le_of_forall_mul ?_
    intro u hu
    obtain ⟨r₀, hr₀, hfix_u⟩ := hfix u hu
    refine ⟨u * r₀, ⟨mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (hQC hr₀)),
      ?_⟩, r₀⁻¹, inv_mem (hQC hr₀), by group⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix_u)
  have hU'N : (U ⊔ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) ⊓
      centralizer ({e} : Set G) ≤
        normalizer (Qsub P₁ P₂ h' : Set G) ⊓ centralizer ({e} : Set G) := by
    rw [hQ]
    exact inf_le_inf_right _ hUC
  have h8 := lemma54_ctx h514 h516a h52a h37 hF3 hF6 hc' hU'N (by rw [hQ]; exact hU'ab)
  rw [hQ] at h8
  omega

end CFSG.OddStandard.SmallF3.Omega
