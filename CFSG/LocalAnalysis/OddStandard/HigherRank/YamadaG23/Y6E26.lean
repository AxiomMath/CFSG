module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26E
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LInst

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6_fact62 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h1 : Sec2.Lemma26Pres2) (h2 : Sec2.Lemma26HS) (h3 : Sec2.Lemma27G23)
    (hQ : HRG23 (↥L ⧸ Subgroup.center ↥L)) :
    Sec2.IsHSType ↥(S3 c.s) := by
  obtain ⟨P, hP⟩ := y6e_exists_sylow c.toCtx5 hH
  obtain ⟨φ, hφ⟩ := y6e_sylow_equiv (y6e_S3_le_X c.toCtx5 hH) P hP
  have hExt := y6e_isExt26 c hH hF
  obtain ⟨e, u, v, w, r, s, hpres, hcl⟩ := h1 _ hExt P
  have hpres' := y6e_isPres26_equiv φ hpres
  cases e with
  | false => exact h2 _ (φ u) (φ v) (φ w) (φ r) (φ s) hpres'
  | true =>
    exfalso
    have hsec := h3 ↥(S3 c.s) (φ u) (φ v) (φ w) (φ r) (φ s) hpres'
    have hcl' : Subgroup.closure {φ u, φ v, φ w} = (M3 c.s).subgroupOf (S3 c.s) := by
      refine y6e_closure_eq (le_sup_right : M3 c.s ≤ S3 c.s) (y6e_S3_le_X c.toCtx5 hH) P φ hφ
        u v w ?_
      rw [hcl]
      exact y6e_pcore_eq (le_sup_right : M3 c.s ≤ normIn L c.s.fr.F ⊔ M3 c.s)
        (y6e_M3_pgroup c.toCtx5 hH) (y6e_secProp c.toCtx5 hH)
    obtain ⟨eM⟩ := y6e_M3_equiv c hH hF
    have hF8 : Nat.card ↥c.s.fr.F = 8 := by
      have h := (y54_F_isE3 hH).2
      norm_num at h
      exact h
    have hω : omega1 (Subgroup.closure {φ u, φ v, φ w}) = c.s.fr.F.subgroupOf (S3 c.s) :=
      y6e_omega1_eq (S := S3 c.s) (le_sup_right : c.s.fr.F ≤ M3 c.s)
        (le_sup_right : M3 c.s ≤ S3 c.s) eM (y54_F_sq hH) hF8 hcl'
    rw [hω] at hsec
    exact y6e_false_of_hsec c.toCtx5 hH hF hQ hsec

end CFSG.OddStandard.HigherRank.YamadaG23
