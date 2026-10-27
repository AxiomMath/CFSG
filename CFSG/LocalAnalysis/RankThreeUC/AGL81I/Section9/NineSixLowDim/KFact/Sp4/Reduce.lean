module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Inner
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Lift
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Gen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

private abbrev liftClosure {q : ℕ} [Fact q.Prime] (p : ℕ)
    (E : Subgroup (MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q))))) :
    Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q)) :=
  ((Subgroup.closure (fixPPrime p E)).comap (QuotientGroup.mk' _)).map
    (CFSG.Open.StatedSp 2 (ZMod q)).subtype

private theorem fixSetSp_subset_liftClosure {q : ℕ} [Fact q.Prime] {p : ℕ}
    {E : Subgroup (MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q))))}
    {Ê : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))}
    (hfix : ∀ g ∈ Ê, g ≠ 1 → ∃ α ∈ E, α ≠ 1 ∧ ∀ x : CFSG.Open.StatedSp 2 (ZMod q),
        g * (x : GL (Fin 2 ⊕ Fin 2) (ZMod q)) = x * g →
          α (QuotientGroup.mk x) = QuotientGroup.mk x) :
    fixSetSp p Ê ⊆ liftClosure p E := by
  rintro z ⟨hz, hpz, g, hg, hne, hc⟩
  obtain ⟨α, hα, hα1, hαx⟩ := hfix g hg hne
  refine ⟨⟨z, hz⟩, Subgroup.subset_closure ⟨fun hdvd => hpz ?_, α, hα, hα1, hαx ⟨z, hz⟩ hc⟩, rfl⟩
  refine hdvd.trans ((orderOf_map_dvd (QuotientGroup.mk' _) _).trans ?_)
  rw [Subgroup.orderOf_mk]

theorem pPrimeGenAt_psp_four_of {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q)
    (h : ∀ E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q)), IsElemSp p E →
      Subgroup.closure (fixSetSp p E) = CFSG.Open.StatedSp 2 (ZMod q)) :
    PPrimeGenAt p (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q))) := by
  intro E hE hc
  have hinn : E ≤ (MulAut.conj : CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q)) →*
      MulAut _).range := fun α hα =>
    mem_range_conj_of_pow_eq_one hq2 hp hp2 hpq α (hE.2 α hα)
  obtain ⟨Ê, hÊ, hfix⟩ := exists_isElemSp_of_le_range_conj hq2 hp hp2 E hE hc hinn
  have hle : CFSG.Open.StatedSp 2 (ZMod q) ≤ liftClosure p E := by
    rw [← h Ê hÊ, Subgroup.closure_le]
    exact fixSetSp_subset_liftClosure hfix
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x', hx', hxx⟩ := hle x.2
  rw [Subtype.ext hxx] at hx'
  exact hx'

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
