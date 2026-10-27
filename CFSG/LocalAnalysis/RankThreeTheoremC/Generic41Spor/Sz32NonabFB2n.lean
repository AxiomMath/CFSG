module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB2r

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y}

private theorem nf5_conj_comp {K : Subgroup Y} (hK : IsComponentOf K ⊤) (g : Y) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).2 hK

private theorem nf5_mem_normalizer_iff {H : Subgroup Y} {g : Y} :
    g ∈ Subgroup.normalizer (H : Set Y) ↔ H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem nf5_comp_normalized (h : NF5 F Γ B R₀ x)
    (hZ : ∀ L : Subgroup Y, IsComponentOf L ⊤ → Subgroup.center ↥L = ⊥) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) {f : Y} (hf : f ∈ F) : f ∈ Subgroup.normalizer (K : Set Y) := by
  by_contra hn
  have hf25 : f ^ 25 = 1 := h.exp f hf
  have hf13 : f = (f * f) ^ 13 := by
    rw [← pow_two, ← pow_mul, show 2 * 13 = 25 + 1 by norm_num, pow_succ, hf25, one_mul]
  have hc2 : IsComponentOf (K.map (MulAut.conj f).toMonoidHom) ⊤ := nf5_conj_comp hK f
  have hc3 : IsComponentOf ((K.map (MulAut.conj f).toMonoidHom).map
      (MulAut.conj f).toMonoidHom) ⊤ := nf5_conj_comp hc2 f
  have h12 : K ≠ K.map (MulAut.conj f).toMonoidHom := fun e =>
    hn (nf5_mem_normalizer_iff.2 e.symm)
  have hsq : ∀ H : Subgroup Y, H.map (MulAut.conj (f * f)).toMonoidHom =
      (H.map (MulAut.conj f).toMonoidHom).map (MulAut.conj f).toMonoidHom := by
    intro H
    have hcomp : (MulAut.conj (f * f)).toMonoidHom =
        (MulAut.conj f).toMonoidHom.comp (MulAut.conj f).toMonoidHom := by
      ext y
      simp [MulAut.conj_apply, mul_assoc, mul_inv_rev]
    rw [Subgroup.map_map, hcomp]
  have h13 : K ≠ (K.map (MulAut.conj f).toMonoidHom).map (MulAut.conj f).toMonoidHom := by
    intro e
    have hff : f * f ∈ Subgroup.normalizer (K : Set Y) :=
      nf5_mem_normalizer_iff.2 ((hsq K).trans e.symm)
    have hpow : (f * f) ^ 13 ∈ Subgroup.normalizer (K : Set Y) := pow_mem hff 13
    rw [← hf13] at hpow
    exact hn hpow
  have hinj : Function.Injective (MulAut.conj f).toMonoidHom := (MulAut.conj f).injective
  have h23 : K.map (MulAut.conj f).toMonoidHom ≠
      (K.map (MulAut.conj f).toMonoidHom).map (MulAut.conj f).toMonoidHom := fun e =>
    h12 (Subgroup.map_injective hinj e.symm).symm
  exact nf5_rank_three h hZ hK hc2 hc3 h12 h13 h23

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
