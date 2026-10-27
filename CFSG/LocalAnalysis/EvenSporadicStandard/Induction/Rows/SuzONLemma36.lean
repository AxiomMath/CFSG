module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzLocalQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OutPerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowDataB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONLocalQ

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore CFSG.ONSchreier Cover

@[expose] def SuzAutFix : Prop :=
  ∀ (Y : Type) [Group Y], IsSporadic Y .Suz → ∀ (K : Subgroup Y) (u : Y),
    SuzPair Y ⊤ K u → AutFixFacts K 4 ∧
      ∀ A : Subgroup ↥(autFixing K), IsPGroup 2 A → ∀ x ∈ A, x * x = 1

@[expose] def SuzInvolutionPerfect : Prop :=
  ∀ (Y : Type) [Group Y], IsSporadic Y .Suz → ∀ (K : Subgroup Y) (u : Y),
    SuzPair Y ⊤ K u → u ∈ ⁅centralizer ({u} : Set Y), centralizer ({u} : Set Y)⁆

section Suz


@[expose] def SuzFixedNotLam : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (π : K →* ↥suzD), Function.Surjective π → π.ker ≤ center K →
    Odd (Nat.card π.ker) → Group.IsPerfect K → InvolutionFixesNotLam K 8

theorem suz_perfect_le {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .Suz) (hQ : SuzPair G L K u) :
    ∀ P : Subgroup G, P ≤ L ⊓ centralizer ({u} : Set G) → Group.IsPerfect ↥P → P ≤ K := by
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := suz_model hL hQ
  obtain ⟨M⟩ := suz_outModel
  exact M.perfect_le_of_fields hQ.1 hQ.2.2.1 (mem_centralizer_iff.2 hQ.2.2.2.1) Ψ hΨ hΨL hΨu
    hQ.2.2.2.2.1 (hQ.2.2.2.2.2.trans card_suzD.symm)

theorem suz_coverMap {H : Type} [Group H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Suz L) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hKperf : Group.IsPerfect ↥K)
    (hcard : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 20160) :
    ∃ π : ↥K →* ↥suzD, Function.Surjective π ∧ π.ker ≤ center ↥K ∧ Odd (Nat.card π.ker) := by
  have := hcov.finite (by decide : TauCeti.SporadicName.Suz ≠ .M)
  obtain ⟨π₀, hs, hc, ho⟩ := exists_oddCentralCover hcov.2.1 hKL
  have hTop := isSporadic_top hcov.2.2
  have hP := suzPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := suz_model hTop hP
  obtain ⟨e⟩ := suz_K_equiv hP Ψ hΨ hΨL hΨu
  have hker : (e.toMonoidHom.comp π₀).ker = π₀.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  refine ⟨e.toMonoidHom.comp π₀, e.surjective.comp hs, ?_, ?_⟩
  · rw [hker]
    exact hc
  · rw [hker]
    exact ho

theorem lemma36eDataQ_suz (haut : SuzAutFix) (hperf : SuzInvolutionPerfect)
    (hfix : SuzFixedNotLam) : Lemma36eDataQ .Suz SuzQ 2 4 where
  m_le := le_rfl
  data H _ _ L K u hcov hQ := by
    obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
    have hLperf : Group.IsPerfect ↥L := hcov.1.1
    have hTop := isSporadic_top hcov.2.2
    have hP := suzPair_quotient hcov hu hu2 hKL hKu hKperf hcard
    have F := suz_outFacts hTop hP
    have hpin := pinnedLocal_of_solomonLocal (solomonLocal_suz hTop hP)
      fun c hc => F.normalized c ⟨Subgroup.mem_top c, hc⟩
    have hloc := solomonLocalQ_of_pinned hcov hu hu2 hKL hKu hKperf hpin
    have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
      ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
    have hfacts := (haut _ hcov.2.2 _ _ hP).1
    obtain ⟨π, hπs, hπc, hπo⟩ := suz_coverMap hcov hu hu2 hKL hKu hKperf hcard
    refine ⟨hu2, hu, hKC, ?_, ?_, ?_, hloc.autCentralizer_two, ?_, ?_, ?_, Or.inr ?_⟩
    · exact characteristic_of_perfect_le hKC hKperf (perfect_le_of_quotient hu
        fun P hP1 hP2 => suz_perfect_le hTop hP P (fun x hx => ⟨Subgroup.mem_top x, hP1 hx⟩) hP2)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)
        (isQuasisimple_of_quotient (isPerfect_subgroupOf_of_le hKL hKperf) hpin.quasisimple)
    · exact autCentralizer_solvable_of_quotient hLperf hfacts.solvable
    · exact autCentralizer_elem_of_quotient hLperf hfacts.elem
    · exact autCentralizer_inner_of_quotient hLperf hfacts.inner
    · exact hfix ↥K π hπs hπc hπo hKperf
    · exact mem_commutator_of_quotient hcov.2.1 hu hu2 (hperf _ hcov.2.2 _ _ hP)

end Suz

section ON


@[expose] def ONK2FixedNotLam : Prop :=
  ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
    Nonempty ((K₂ ⧸ center K₂) ≃* (↥onL ⧸ center ↥onL)) → InvolutionFixesNotLam K₂ 4

theorem on_K_equiv {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .ONan) (hQ : ONPair G L K u) : Nonempty (↥K ≃* ↥onL) := by
  obtain ⟨hu, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := on_model hL hu hu2
  have hK₀ := on_K₀_eq hu hKL hKu hperf hcard Ψ hΨ hΨL hΨu
  exact ⟨(Subgroup.subgroupOfEquivOfLe hKL).symm.trans
    ((Subgroup.equivMapOfInjective _ Ψ hΨ).trans (MulEquiv.subgroupCongr hK₀))⟩

theorem on_coverMap {H : Type} [Group H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .ONan L) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hKperf : Group.IsPerfect ↥K)
    (hcard : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 80640) :
    ∃ π : ↥K →* ↥onL, Function.Surjective π ∧ π.ker ≤ center ↥K ∧ Odd (Nat.card π.ker) := by
  have := hcov.finite (by decide : TauCeti.SporadicName.ONan ≠ .M)
  obtain ⟨π₀, hs, hc, ho⟩ := exists_oddCentralCover hcov.2.1 hKL
  have hTop := isSporadic_top hcov.2.2
  have hP := onPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  obtain ⟨e⟩ := on_K_equiv hTop hP
  have hker : (e.toMonoidHom.comp π₀).ker = π₀.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  refine ⟨e.toMonoidHom.comp π₀, e.surjective.comp hs, ?_, ?_⟩
  · rw [hker]
    exact hc
  · rw [hker]
    exact ho

theorem lemma36eDataQ_on (hfix : ONK2FixedNotLam) : Lemma36eDataQ .ONan ONQ 2 2 where
  m_le := le_rfl
  data H _ _ L K u hcov hQ := by
    obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
    have hLperf : Group.IsPerfect ↥L := hcov.1.1
    have hTop := isSporadic_top hcov.2.2
    have hP := onPair_quotient hcov hu hu2 hKL hKu hKperf hcard
    have F := on_inFacts hTop hP
    have hpin := pinnedLocal_of_solomonLocal (solomonLocal_on hTop hP)
      fun c hc => F.normalized c ⟨Subgroup.mem_top c, hc⟩
    have hloc := solomonLocalQ_of_pinned hcov hu hu2 hKL hKu hKperf hpin
    have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
      ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
    have hfacts := on_autFixFacts hTop hP
    obtain ⟨π, hπs, hπc, hπo⟩ := on_coverMap hcov hu hu2 hKL hKu hKperf hcard
    refine ⟨hu2, hu, hKC, ?_, ?_, ?_, hloc.autCentralizer_two, ?_, ?_, ?_, Or.inl ?_⟩
    · exact characteristic_of_perfect_le hKC hKperf (perfect_le_of_quotient hu
        fun P hP1 hP2 => on_perfect_le hTop hP P (fun x hx => ⟨Subgroup.mem_top x, hP1 hx⟩) hP2)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)
        (isQuasisimple_of_quotient (isPerfect_subgroupOf_of_le hKL hKperf) hpin.quasisimple)
    · exact autCentralizer_solvable_of_quotient hLperf hfacts.solvable
    · exact autCentralizer_elem_of_quotient hLperf hfacts.elem
    · exact autCentralizer_inner_of_quotient hLperf hfacts.inner
    · obtain ⟨e⟩ := quotientCenterEquiv_of_centralCover π hπs hπc hKperf
      exact hfix ↥K hKperf ⟨e⟩
    · exact (inFacts_of_quotient hcov.2.1 hLperf hu hu2 hKL hKu hKperf F).u_mem

end ON

end CFSG.EvenSporadicStandard.Induction
