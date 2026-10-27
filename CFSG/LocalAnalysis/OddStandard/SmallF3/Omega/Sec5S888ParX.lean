module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515Q
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem par_exists_ctx (h514 : Asc82Lemma514) (h515b : Asc82Lemma515b)
    (h515c : Asc82Lemma515c) (hF2 : Asc82FactPocketsTwo)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {a b : G} (ha : a ∈ Kfam5 K₁ K₂ h 2)
    (hb : b ∈ Kfam5 K₁ K₂ h 3) (ha2 : a * a = z) (hb2 : b * b = z) :
    ∃ (S'' : Subgroup G) (r'' : G) (B'' A'' P₁ P₂ : Subgroup G) (h'' : G),
      Sec5HCtx G (a * b) (layerC5 (a * b)) S'' z r'' B'' A'' P₁ P₂ h'' ∧
        ((P₁ = K₁ ∧ P₂ = K₂) ∨ (P₁ = K₂ ∧ P₂ = K₁)) := by
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  obtain ⟨-, hsq, hne1, hnez⟩ := par_t_props hq h23 ha hb ha2 hb2
  have hd2 : orderOf (a * b) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
  have hdsup : a * b ∈ Kfam5 K₁ K₂ h 2 ⊔ Kfam5 K₁ K₂ h 3 := Subgroup.mul_mem_sup ha hb
  have hdΔ : a * b ∈ Delta5 z (Gamma5 K₁ K₂ h) :=
    sec5_mem_delta_of_pair h514 c h23 hd2 hnez hdsup
  obtain ⟨S'', r'', B'', A'', P₁, P₂, h'', c'', -⟩ :=
    h515c G t L S z r B A K₁ K₂ h c (a * b) hdΔ
  have hP := sec5_pockets_eq h514 hF2 h515b c (i := 2) (j := 3) (l := 0) (m := 1) h23
    (by decide) (by decide) (by decide) (by decide) (by decide) hd2 hnez hdsup c''
  refine ⟨S'', r'', B'', A'', P₁, P₂, h'', c'', ?_⟩
  simpa [Kfam5] using hP

end CFSG.OddStandard.SmallF3.Omega
