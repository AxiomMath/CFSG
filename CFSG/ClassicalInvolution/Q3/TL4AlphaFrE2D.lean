module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdExact
public import CFSG.ClassicalInvolution.Q3.TL3T21

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan)

namespace AlphaFr.E2D

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem core_eq_of_isPGroup (hd : TightDatum R S t) (hR2 : IsPGroup 2 ↥R) :
    tightCore R = (S : Subgroup R).map R.subtype :=
  hd.sylow_core.2.2 (tightCore R) le_rfl (hR2.to_le (tightCore_le R)) hd.sylow_core.1

theorem isPGroup_mem (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J := by
  rintro _ ⟨g, rfl⟩
  exact ((isPGroup_of_inO2 hd hc.2.2 hO2).to_le (tightCore_le R)).map
    (MulAut.conj g).toMonoidHom

theorem card_mem (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), Nat.card ↥J = 2 ^ 3 := by
  obtain ⟨e⟩ : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := hc.1
  have h8 : Nat.card ↥(tightCore R) = 2 ^ 3 := by
    rw [core_eq_of_isPGroup hd (isPGroup_of_inO2 hd hc.2.2 hO2),
      Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  rintro _ ⟨g, rfl⟩
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans h8

omit [Finite Y] in
theorem pSpan_eq_top (hc : TightCls Y R S t) :
    pSpan (CoreAssembly.conjClass (tightCore R)) = ⊤ := by
  have h1 : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hc.2.1
  rw [eq_top_iff, ← h1]
  exact iSup_le fun g => le_pSpan ⟨g, rfl⟩

omit [Finite Y] in
theorem transitive : ∀ L ∈ CoreAssembly.conjClass (tightCore R),
    ∀ L' ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g L = L' := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨b * a⁻¹, ?_⟩
  show conjSub (b * a⁻¹) (conjSub a (tightCore R)) = conjSub b (tightCore R)
  rw [conjSub_mul, conjSub_inv_conjSub]

theorem exists_normal (hd : TightDatum R S t) (hO2 : TightInO2 t) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ u : Y, IsUniqueInvolution L u →
      ∃ Q : Subgroup Y, Q.Normal ∧ IsPGroup 2 ↥Q ∧ u ∈ Q := by
  rintro _ ⟨g, rfl⟩ u hu
  obtain ⟨P, hPn, hP2, htP⟩ := hO2
  refine ⟨P, hPn, hP2, ?_⟩
  have hgu : g * t * g⁻¹ = u := (hd.isUniqueInvolution_core.conj g).eq hu
  rw [← hgu]
  exact hPn.conj_mem t htP g

end AlphaFr.E2D

theorem SecIdE2.thmDConcl_of_below {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hD : TC.Thin.ThmDAbsBelow 3 n) (hn : Nat.card Y < n)
    (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t) :
    TC.Thin.ThmDConcl (CoreAssembly.conjClass (tightCore R)) :=
  hD Y hn _ hd.hypOmegaGen (AlphaFr.E2D.isPGroup_mem hd hc hO2)
    (AlphaFr.E2D.card_mem hd hc hO2) hd.aEmpty (AlphaFr.E2D.pSpan_eq_top hc)
    AlphaFr.E2D.transitive hc.2.2 (AlphaFr.E2D.exists_normal hd hO2)

theorem SecIdE2.thmDConcl_of {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hP : TightBelowRPlus 3 n) (hn : Nat.card Y < n)
    (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t) :
    TC.Thin.ThmDConcl (CoreAssembly.conjClass (tightCore R)) :=
  SecIdE2.thmDConcl_of_below hP.thmD.d2 hn hd hc hO2

end CFSG.ClassicalInvolution.Q3.TL4
