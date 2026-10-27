module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSyl
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QDefs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

theorem famQuat_of_char_two {t : StatedLieTag}
    (ht : ∀ (X : Type) [Group X] (n p f : ℕ), Blueprint.LieModel X t n p f → p = 2) :
    FamQuat t :=
  fun X _ _ _ n p f _ hp2 hX => absurd (ht X n p f hX) hp2

theorem char_two_of_lieModel_twistedB2 (X : Type) [Group X] (n p f : ℕ)
    (h : Blueprint.LieModel X .twistedB2 n p f) : p = 2 := by
  rcases h with ⟨hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, -, hs⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact hs.1

theorem char_two_of_lieModel_twistedF4 (X : Type) [Group X] (n p f : ℕ)
    (h : Blueprint.LieModel X .twistedF4 n p f) : p = 2 := by
  rcases h with ⟨hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, -, hr⟩ | ⟨-, hc, -⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact hr.1.2.2.2.1
  · exact absurd hc (by decide)

theorem char_two_of_lieModel_Tits (X : Type) [Group X] (n p f : ℕ)
    (h : Blueprint.LieModel X .Tits n p f) : p = 2 := by
  rcases h with ⟨hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, -, hr⟩ | ⟨-, hc, -⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact hr.1.2.2.2.1
  · exact absurd hc (by decide)

theorem harris82Lemma51Quat_of_famQuat (hPSL : FamQuat .PSL) (hPSU : FamQuat .PSU)
    (hPSp : FamQuat .PSp) (hOdd : FamQuat .POmegaOdd) (hPlus : FamQuat .POmegaPlus)
    (hMinus : FamQuat .POmegaMinus) (hG2 : FamQuat .G2) (hF4 : FamQuat .F4)
    (hE6 : FamQuat .E6) (hE7 : FamQuat .E7) (hE8 : FamQuat .E8) (hTE6 : FamQuat .twistedE6)
    (hD4 : FamQuat .trialityD4) (hTG2 : FamQuat .twistedG2) : Harris82Lemma51Quat := by
  intro X _ _ _ τ n p f hp hp2 hX z hz R hRC hRsub hzR hRQ
  by_contra hq
  have hfam : FamQuat τ := by
    cases τ with
    | PSL => exact hPSL
    | PSU => exact hPSU
    | PSp => exact hPSp
    | POmegaOdd => exact hOdd
    | POmegaPlus => exact hPlus
    | POmegaMinus => exact hMinus
    | G2 => exact hG2
    | F4 => exact hF4
    | E6 => exact hE6
    | E7 => exact hE7
    | E8 => exact hE8
    | twistedE6 => exact hTE6
    | trialityD4 => exact hD4
    | twistedG2 => exact hTG2
    | twistedB2 => exact famQuat_of_char_two char_two_of_lieModel_twistedB2
    | twistedF4 => exact famQuat_of_char_two char_two_of_lieModel_twistedF4
    | Tits => exact famQuat_of_char_two char_two_of_lieModel_Tits
  have hzc : (⟨z, hzR⟩ : R) ∈ center R := mem_center_iff.mpr fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hRC g.2))
  have hzo : orderOf (⟨z, hzR⟩ : R) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  obtain ⟨S, hS8, hzS, ⟨u, hu, v, hv, huv⟩, huniq⟩ := exists_sylow_quat hRQ hzc hzo
  have hsolv : Group.IsSolvable (↥R ⧸ pPrimeCore 2 ↥R) := by
    rcases hRQ with hQ | hS
    · obtain ⟨e⟩ := hQ
      have := isSolvable_quat
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    · obtain ⟨e⟩ := hS
      have := isSolvable_sl23
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  refine hfam X n p f hp hp2 hX hq z hz (S.map R.subtype) ?_ ⟨⟨z, hzR⟩, hzS, rfl⟩
    ⟨u, mem_map_of_mem _ hu, v, mem_map_of_mem _ hv, fun h => huv (Subtype.ext h)⟩ ?_ ?_ ?_
  · rintro _ ⟨s, -, rfl⟩
    exact hRC s.2
  · rintro _ ⟨s, hs, rfl⟩ hss
    rcases huniq s hs (Subtype.ext hss) with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)
  · rw [card_map_of_injective R.subtype_injective, hS8]
  · rintro K hK hKe k hk _ ⟨s, -, rfl⟩
    exact commute_of_isComponent hRC hRsub hsolv hK hKe k hk s s.2

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
