module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreSec
public import CFSG.ClassicalInvolution.AschTight.S19MFactM2
public import CFSG.ClassicalInvolution.AschTight.S19FCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.Assembly.LowTwoRank

section FactM2


theorem factM2Gen {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Type} [Group E] [Finite E]
    {Ω : Set (Subgroup E)} {t : StatedLieTag} {k e' : ℕ} (ht : S1911.IsT6Tag t k)
    (M : Ih8Model p e Ω t k e') (hne : Ω.Nonempty) {x : E} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ L ∈ Ω, IsUniqueInvolution L x := by
  have hadm := M.admissible
  have : Finite (modelUniv t k p e' Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (ih8_isFundTag_mf M.isFundTag) hadm
  have hker : Odd (Nat.card M.ψ.ker) :=
    S19M.odd_natCard_ker M.ker_le_center (S19M.factM3 p e' Fact.out hp2 t k ht hadm)
  obtain ⟨y, hy, hy1, rfl⟩ := S19M.exists_involution_lift M.surj hker hx hx1
  obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hne
  obtain ⟨c₀, hc₀⟩ := S19M.exists_isUniqueInvolution_of_mem_fund hp2 ht hadm (M.cls_sub hR₀)
  obtain ⟨g, hg⟩ := S19M.involutionsConj_modelUniv hp2 ht hadm c₀ y hc₀.sq hy hc₀.ne_one hy1
  have hc : IsUniqueInvolution (conjSub g R₀) y := by
    have h := hc₀.conj g
    rwa [hg] at h
  exact ⟨_, M.map_mem (M.cls_conj R₀ hR₀ g), S19M.isUniqueInvolution_map hker hc⟩

theorem factM1Gen {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Type} [Group E] [Finite E]
    {Ω : Set (Subgroup E)} {t : StatedLieTag} {k e' : ℕ}
    (ht : (t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) (M : Ih8Model p e Ω t k e')
    (φ : MulAut E) (hφ : φ * φ = 1) {L : Subgroup E} (hL : L ∈ Ω)
    (hφL : L.map φ.toMonoidHom = L)
    (hab : ∀ P : Subgroup E, IsPGroup 2 P → P ≤ L → (∀ x ∈ P, φ x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ x : E, φ = MulAut.conj x := by
  have he' : 1 ≤ e' := M.admissible.2.1
  have htag : t = .G2 ∨ t = .trialityD4 := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [Or.inl rfl, Or.inr rfl]
  obtain ⟨R, hRcls, rfl⟩ := (M.mem_iff L).mp hL
  have hRfund := M.cls_sub hRcls
  have hinj : Function.Injective M.ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact M.ker_le_center.trans
      (RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 htag k he').le
  refine S19F.exists_conj_of_transport M.ψ ⟨hinj, M.surj⟩ φ hφ hφL hab fun α hα hαR habα => ?_
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact S19F.factM1_g2 hp2 he' α hα hRfund hαR habα
  · exact S19F.factM1_d4 hp2 he' α hα hRfund hαR habα

end FactM2

section Simple


variable {p f e' : ℕ} [Fact p.Prime] {E : Type} [Group E] {Φ : Set (Subgroup E)}

theorem isSimpleGroup_of_ih8Model [Finite E] [Nontrivial E] (hp2 : p ≠ 2) {t : StatedLieTag}
    {k : ℕ} (ht : S1911.IsT6Tag t k) (M : Ih8Model p f Φ t k e')
    (hO : classicalInvolutionOddCore E = ⊥) : IsSimpleGroup E := by
  have hsurj := M.surj
  have hq := (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t k p e' Fact.out M.isFundTag
    M.admissible).1
  have hZ := S19M.factM3 p e' Fact.out hp2 t k ht M.admissible
  refine ⟨fun N hN => ?_⟩
  set M' := N.comap M.ψ with hM'
  have hMn : M'.Normal := hN.comap _
  have := hq.2
  have : (M'.map (QuotientGroup.mk' (Subgroup.center
      (modelUniv t k p e' Fact.out).K))).Normal :=
    hMn.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M'.map (QuotientGroup.mk' (Subgroup.center
      (modelUniv t k p e' Fact.out).K))) with h | h
  · left
    have hMZ : M' ≤ Subgroup.center _ := by
      intro x hx
      have : (QuotientGroup.mk' _ x : _ ⧸ Subgroup.center _) ∈ M'.map (QuotientGroup.mk' _) :=
        ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hNle : N ≤ (Subgroup.center _).map M.ψ := by
      intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, hMZ hy, rfl⟩
    have hodd : Odd (Nat.card N) :=
      hZ.of_dvd_nat ((Subgroup.card_dvd_of_le hNle).trans (Subgroup.card_map_dvd _ _))
    have : N ≤ classicalInvolutionOddCore E := le_sSup ⟨hN, hodd⟩
    rw [hO] at this
    exact le_bot_iff.mp this
  · right
    have hMtop : M' = ⊤ := by
      refine eq_top_of_perfect_of_sup_center hq.1 ?_
      rw [eq_top_iff]
      intro x _
      have hx : (QuotientGroup.mk' _ x : _ ⧸ Subgroup.center _) ∈ M'.map (QuotientGroup.mk' _) := by
        rw [h]
        trivial
      obtain ⟨y, hy, hyx⟩ := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hy hyx
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    have : x ∈ M' := hMtop ▸ Subgroup.mem_top x
    exact this

theorem isSimpleGroup_of_systemU {ι : Type} [Subsingleton ι] [Finite E] [Nontrivial E]
    (hp2 : p ≠ 2) (D : LieSystemDataU p f ι E Φ) (i : ι) (hconj : ConjInvariant Φ)
    {t : StatedLieTag} {k e : ℕ} (htag : S1911.IsT6Tag t k) (hft : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) (he : e = f ∨ (t = .trialityD4 ∧ 3 * e = f))
    (hc : D.kind i = compModel p e t k) (hO : classicalInvolutionOddCore E = ⊥) :
    IsSimpleGroup E :=
  isSimpleGroup_of_ih8Model hp2 htag (ih8ModelOfSystemU D i hconj hft hadm he hc) hO

end Simple

end CFSG.ClassicalInvolution.Q3.Q3T6
