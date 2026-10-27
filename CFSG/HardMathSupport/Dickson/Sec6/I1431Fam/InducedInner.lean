module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Descend
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.HardMathSupport.Solomon.Proving.L2OrderUnique

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB

theorem S1431Cfg.false_of_induced_inner {P : Type} [Group P] [Finite P]
    {A : Subgroup (MulAut P)} {ψ : MulAut P} {J : Subgroup P} {q : ℕ} (c : S1431Cfg P A ψ J q)
    (hinn : ∀ η ∈ A, η ∉ Subgroup.zpowers ψ → ∀ h : η ∈ stabAut J,
      IsInnerAut (inducedBarHom J ⟨η, h⟩)) : False := by
  have hU := CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
  have hF := CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds
  have hψ3 : ψ ^ 3 = 1 := c.elemAbelian.2 ψ c.mem
  obtain ⟨η, hηA, hηψ⟩ := exists_mem_not_zpowers hψ3 c.card
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  obtain ⟨⟨h, hfld⟩, hnt⟩ := c.field η hηA hηψ
  have hα1 : inducedBarHom J ⟨η, h⟩ ≠ 1 := fun h1 => hnt ⟨h, h1⟩
  have hα3 := inducedBarHom_pow_three J h hη3
  have hQ : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent c.comp
  have hnot := not_isInnerAut_descend_of_fieldAut hU hF hQ hα3 hα1 hfld c.typeL2 c.not_dvd
    c.ne_eight
  obtain ⟨u, hu⟩ := hinn η hηA hηψ h
  exact hnot ⟨QuotientGroup.mk u, by rw [← hu, CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj]⟩

theorem isInnerAut_inducedBarHom_of_barX {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) {b : G} (hbX : b ∈ X) (h : MulAut.conj b ∈ stabAut J)
    {j₀ : G} (hj₀ : j₀ ∈ J)
    (hbj : ∀ j ∈ J, ∀ (h1 : b * j * b⁻¹ ∈ X) (h2 : j₀ * j * j₀⁻¹ ∈ X),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b * j * b⁻¹, h1⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨j₀ * j * j₀⁻¹, h2⟩) :
    IsInnerAut (inducedBarHom J ⟨MulAut.conj b, h⟩) := by
  have hsub : IsSubnormal J X := hJ.2.1
  have hJX : J ≤ X := hJ.1
  have key : ∀ u v : ↥J, (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (Subgroup.inclusion hJX u) =
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (Subgroup.inclusion hJX v) →
      (QuotientGroup.mk u : barOf 3 J) = QuotientGroup.mk v := by
    intro u v huv
    rw [QuotientGroup.eq]
    have h1 : Subgroup.inclusion hJX (u⁻¹ * v) ∈ GLAPPrimeCore 3 ↥X := by
      have h0 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (Subgroup.inclusion hJX (u⁻¹ * v)) = 1 := by
        rw [map_mul (Subgroup.inclusion hJX), map_inv (Subgroup.inclusion hJX), map_mul, map_inv,
          huv, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h0
    have h2 : ((u⁻¹ * v : ↥J) : G) ∈ GLAPPrimeCoreOf 3 X :=
      (mem_gLAPPrimeCoreOf_iff 3 X _).2 ⟨(u⁻¹ * v).2 |> hJX, h1⟩
    have h3 : ((u⁻¹ * v : ↥J) : G) ∈ GLAPPrimeCoreOf 3 J := by
      rw [glaPPrimeCoreOf_eq_inf_of_isSubnormal Nat.prime_three hsub]
      exact ⟨(u⁻¹ * v).2, h2⟩
    exact ((mem_gLAPPrimeCoreOf_iff 3 J _).1 h3).2
  refine ⟨QuotientGroup.mk ⟨j₀, hj₀⟩, ?_⟩
  ext y
  induction y using QuotientGroup.induction_on with
  | H j =>
    rw [inducedBarHom_mk]
    show (QuotientGroup.mk (⟨j₀, hj₀⟩ * j * ⟨j₀, hj₀⟩⁻¹) : barOf 3 J) =
      QuotientGroup.mk (restrictAut (MulAut.conj b) h j)
    exact key _ _ (hbj j j.2 _ _).symm

end CFSG.HardMathSupport.Dickson.Sec6.I1431
