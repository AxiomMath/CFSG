module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Shape
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericPrimeThreeL28Lemma43S (G : Type) [Group G] [Finite G] : Prop :=
  GenericL28At G fun p P M x J => L28Prop34S p P J x → L28PointLemma43 p P M x

@[expose] def GL83Generic4_9BNonabS (G : Type) [Group G] [Finite G] : Prop :=
  GenericL28At G fun p P M x J => L28Prop34S p P J x → ∀ U : Subgroup G, L28InV p P x U →
    (∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M) → L28PointFAbelian p M U

theorem GL83GenericPrimeThreeL28.of_partsS (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hS1 : KFactL28Three) (hS2 : KFactL28FieldSignalizer) (hS3 : KFactL28BorelCore)
    (h34 : GL83GenericPrimeThreeL28Prop34S G) (h42 : GL83GenericPrimeThreeL28Lemma42 G)
    (h43 : GL83GenericPrimeThreeL28Lemma43S G) (hNA : GL83Generic4_9BNonabS G) :
    GL83GenericPrimeThreeL28 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsL28Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have h34' := h34 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  obtain ⟨U, hV, h43'⟩ := h43 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ
    hψ hker hQ h34'
  have h42' := h42 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
    h34'.1 U hV
  have hAb := hNA 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
    h34' U hV h42'
  exact l28_false_of_config hS hU0 hD1 hInn hWC hS1 hS2 hS3 hp hM hgen hJ h34'.1 hV hAb h42' h43'

end CFSG.LocalAnalysis.RankThreeTheoremC
