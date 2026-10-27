module

public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3DStand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Q3.Disc3
open scoped MatrixGroups

structure TransSect3 {X : Type} [Group X] (Φ : Set (Subgroup X)) : Prop where
  hyp : HypOmegaModU (.sl2 3 1) Φ
  oddCore : classicalInvolutionOddCore X = ⊥
  gen : omegaGen Φ = ⊤
  trans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J

section Datum


variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem card_eq_one_of_transitive3 [Finite X] (D : OmegaLieU p f Φ)
    (hΦ : HypOmegaModU (.sl2 p f) Φ) (hgen : omegaGen Φ = ⊤)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (hne : Φ.Nonempty) :
    D.card = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨i₀, hKi₀⟩ := D.exists_comp_of_mem hK
  have hall : ∀ L ∈ Φ, L ≤ D.comp i₀ := by
    intro L hL
    obtain ⟨g, rfl⟩ := htrans K hK L hL
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := D.mem_comp_conj (g := g) (hgen ▸ Subgroup.mem_top g) (hKi₀ hx)
    simpa [mul_assoc] using this
  have hsub : ∀ j : Fin D.card, j = i₀ := by
    intro j
    by_contra hji
    obtain ⟨R, -, hRΦ⟩ := D.meets j
    obtain ⟨z, hz⟩ := hΦ.classical _ hRΦ
    obtain ⟨x, hx, y, hy, hxy⟩ := hz.exists_noncomm
    have hxj : x ∈ D.comp j := Subgroup.map_le_range _ _ hx
    exact hxy (D.comp_commute hji x hxj y (hall _ hRΦ hy))
  have hle : D.card ≤ 1 :=
    Fin.subsingleton_iff_le_one.mp ⟨fun a b => (hsub a).trans (hsub b).symm⟩
  have hpos : 0 < D.card := i₀.pos
  omega

theorem hom_surjective_of_gen3 (D : OmegaLieU p f Φ) (hcard : D.card = 1)
    (hgen : omegaGen Φ = ⊤) (i : Fin D.card) : Function.Surjective (D.hom i) := by
  refine MonoidHom.range_eq_top.mp ?_
  have h1 : (⨆ j, D.comp j) = D.comp i :=
    le_antisymm
      (iSup_le fun j => by
        rw [show j = i from Fin.ext (by have := i.2; have := j.2; omega)])
      (le_iSup D.comp i)
  rw [D.iSup_comp] at h1
  show D.comp i = ⊤
  exact h1.symm.trans hgen

theorem exists_omegaLieU_sect [Finite X] {n : ℕ} (hn : CITBelowT (.sl2 p f) n)
    (hlt : Nat.card X < n) (hΦ : HypOmegaModU (.sl2 p f) Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (hne : Φ.Nonempty) :
    ∃ D : OmegaLieU p f Φ, D.card = 1 := by
  obtain ⟨D⟩ := exists_omegaLieU hn hΦ hne hO hlt
  exact ⟨D, card_eq_one_of_transitive3 D hΦ hgen htrans hne⟩

noncomputable def toIh8ModelSect (D : OmegaLieU p f Φ) (hΦ : HypOmegaModU (.sl2 p f) Φ)
    (hgen : omegaGen Φ = ⊤) (hcard : D.card = 1) (i : Fin D.card)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ} (ht : Generic.IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t k p e)
    (he : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) (hc : D.kind i = compModel p e t k) :
    Ih8Model p f Φ t k e where
  isFundTag := ht
  admissible := hadm
  exp_eq := he
  ψ := castHom hc (D.hom i)
  ker_le_center := castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)
  surj := by
    have h := hom_surjective_of_gen3 D hcard hgen i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [range_castHom]
    exact h
  cls := {R | R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D ∧
    R.map (castHom hc (D.hom i)) ∈ Φ}
  cls_sub := fun _ hR => hR.1
  mem_iff := by
    intro L
    constructor
    · intro hL
      obtain ⟨R, hR, rfl⟩ := (D.mem_iff_exists_cls hcard i).mp hL
      obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR.1
      exact ⟨R', ⟨hR', by rw [hRR]; exact hR.2⟩, hRR.symm⟩
    · rintro ⟨R, hR, rfl⟩
      exact hR.2
  cls_conj := by
    intro R hR g
    refine ⟨Asc77.OmegaLie.fund_conj hR.1 g, ?_⟩
    have := map_conj_eq_conjSub_map (castHom hc (D.hom i)) g R
    change Subgroup.map (castHom hc (D.hom i)) (conjSub g R) ∈ Φ
    rw [show Subgroup.map (castHom hc (D.hom i)) (conjSub g R) =
      conjSub (castHom hc (D.hom i) g) (R.map (castHom hc (D.hom i))) from this]
    exact hΦ.conjInvariant _ _ hR.2

theorem top_notMem_of_transitive3 {K K' : Subgroup X}
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (hK : K ∈ Φ) (hK' : K' ∈ Φ)
    (hne : K' ≠ K) : (⊤ : Subgroup X) ∉ Φ := by
  intro htop
  have h1 : ∀ L ∈ Φ, L = ⊤ := by
    intro L hL
    obtain ⟨g, hg⟩ := htrans ⊤ htop L hL
    rw [← hg]
    ext x
    rw [mem_conjSub_iff]
    simp
  exact hne ((h1 K' hK').trans (h1 K hK).symm)

end Datum

end CFSG.ClassicalInvolution.Q3.Q3T7
