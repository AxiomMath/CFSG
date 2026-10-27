module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PSmall
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Arrow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Om6M

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_caseC [Finite G] (h35 : Asc82Lemma35) (h36 : Asc82Lemma36) (hsh : Asc82Shapes)
    (hM : Asc82Tab6M) (hF : Asc82AutFacts) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {v y b : G}
    {V W Y Vb R I J : Subgroup G} (c : Sec63PCtx v y b V W Y Vb R I J)
    (hJv : CFSG.conjugate J v = J) (hWJ : W ≠ J) : False := by
  have hWle : W ≤ J := by simpa [hJv] using c.hWJ
  have hvN : v ∈ normalizer (J : Set G) := sec63P_conjugate_eq_iff.mp hJv
  have hJg : ∀ g ∈ R, CFSG.conjugate J g = J := by
    intro g hg
    by_contra hne
    have hgV : g ∈ V := (c.hRle hg).1
    have hgb : g ∈ centralizer ({b} : Set G) := (c.hRle hg).2
    have hJgc : IsComponentIn (CFSG.conjugate J g) (centralizer ({b} : Set G)) :=
      c.hJc.conjugate hgb
    have hWg : W ≤ CFSG.conjugate J g := by
      intro w hw
      rw [sec63P_mem_conjugate_iff]
      have hwg : w * g = g * w := c.hWc.commute_of_ne c.hVc c.hWne w hw g hgV
      have heq : g * w * g⁻¹ = w := by rw [← hwg]; group
      rw [heq]
      exact hWle hw
    apply c.hWc.not_le_centralizer
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro w' hw'
    exact (c.hJc.commute_of_ne hJgc (Ne.symm hne) w (hWle hw) w' (hWg hw')).symm
  have hRnorm : R ≤ normalizer (J : Set G) :=
    fun g hg => sec63P_conjugate_eq_iff.mp (hJg g hg)
  have hRcentW : R ≤ centralizer (W : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact c.hWc.commute_of_ne c.hVc c.hWne w hw g ((c.hRle hg).1)
  have hRN : R ≤ normalizer (J : Set G) ⊓ centralizer (W : Set G) :=
    fun g hg => ⟨hRnorm hg, hRcentW hg⟩
  have hcomm : ⁅J, zpowers v⁆ = J := by
    rcases sec63P_commutator_dichotomy c.hJc.isQuasisimple hvN with h | h
    · exact h
    · exfalso
      have hJ2 : J ≤ centralizer ({v} : Set G) ⊓ centralizer ({b} : Set G) :=
        le_inf h c.hJc.1
      have hJc2 : IsComponentIn J (centralizer ({v} : Set G) ⊓ centralizer ({b} : Set G)) :=
        c.hJc.mono hJ2 inf_le_right
      have hW2 : W ≤ centralizer ({v} : Set G) ⊓ centralizer ({b} : Set G) :=
        le_inf c.hWc.1 (hWle.trans c.hJc.1)
      have hWc2 : IsComponentIn W (centralizer ({v} : Set G) ⊓ centralizer ({b} : Set G)) :=
        c.hWc.mono hW2 inf_le_left
      exact hWJ (IsComponentIn.eq_of_le hWc2 hJc2 hWle)
  have harrow : WalterArrow W J :=
    ⟨v, b, c.hv, c.hb, c.hvb, c.hWc, c.hJc, hWle, hcomm⟩
  have hstep := sec63_step hsh hS harrow c.hWF
  have hbadW : Bad63 W v := ⟨c.hv, c.hWc, c.hWF, V, c.hWne.symm, c.hVc, c.hVF⟩
  have hW29 : IsL29 W := by
    rcases sec63_bad_shape h36 hS hbadW with h | h
    · exact h
    · exact (hstep.2.2.2 (Or.inl h)).elim
  have hJshape : IsL281 J ∨ IsOmega5 J ∨ IsOmega6Plus J ∨ IsOmega6Minus J := hstep.2.1 hW29
  have hJs : IsOmega6Plus J ∨ IsOmega5 J ∨ IsL281 J := by
    rcases hJshape with h | h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact (sec63_not_omega6Minus h35 hM hF hS c.hv c.hWc c.hVc c.hVF c.hWne.symm c.hb
        c.hJc c.hJF hWle h).elim
  have hHle : R ⊓ centralizer (J : Set G) ≤
      V ⊓ centralizer ({b} : Set G) ⊓ centralizer (Vb : Set G) := by
    intro g hg
    have hgR : g ∈ R := hg.1
    have hgCJ : g ∈ centralizer (J : Set G) := hg.2
    have hgV : g ∈ V := (c.hRle hgR).1
    have hgb : g ∈ centralizer ({b} : Set G) := (c.hRle hgR).2
    have hgY : g ∈ Y := c.hVY hgV
    have hgK : J ≤ centralizer ({g} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hgCJ j hj
    have hkey : Vb ≤ centralizer ({g} : Set G) :=
      sec63P_key1 c c.hJc c.hJF hgY hgb hgK
    refine ⟨⟨hgV, hgb⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.mp (hkey hd)
  have hbound2 : Nat.card ↥(R ⊓ centralizer (J : Set G)) ≤ 2 :=
    c.hbound (R ⊓ centralizer (J : Set G)) (c.hR2.to_le inf_le_left) hHle
  rcases sec63_arrow_cases hF hHyp c.hv c.hb hvN c.hWc c.hJc hWle c.hWF hJs c.hR2 hRN with
    hrel | ⟨-, -, hQ⟩
  ·
    have h4 : 4 ≤ Nat.card ↥(R ⊓ centralizer (J : Set G)) :=
      sec63P_card_inf_ge_four c.hR8 hrel
    omega
  · exact (sec63P_not_quot_z4 c.hRgen) hQ

end CFSG.OddStandard.SmallF3.Omega
