module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0Aut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Sp6Data

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

set_option linter.unusedSectionVars false


theorem tab_sp6Rep2_mem : tab sp6Rep2 ∈ co3X36 := by
  rw [tab_eq, ← sp6Q_originalSubgroup]
  have hlen : 1 < sp6InvReps.length := by simp [sp6InvReps, sp6InvRepWords]
  have h1 : sp6Rep2 = sp6InvReps[1] := List.getD_eq_getElem _ _ hlen
  rw [h1]
  exact (sp6InvReps_mem _ (List.getElem_mem hlen)).1

@[expose] noncomputable def r2H : ModSp0 := ⟨tab sp6Rep2, tab_sp6Rep2_mem⟩

@[expose] noncomputable def K0H : Subgroup ModSp0 := K0.comap co3X36.subtype

@[expose] def Sp0TFacts : Prop := Sp0Core.TFacts K0H r2H

theorem sp0_ident (R : Subgroup ModSp0) (t : ModSp0) (hC : CoreData (⊤ : Subgroup ModSp0) R t) :
    ∃ g : ModSp0, conjSub g R = K0H ∧ g * t * g⁻¹ = r2H := by
  have hinj : Function.Injective co3X36.subtype := Subtype.val_injective
  obtain ⟨eR⟩ := hC.q8
  have hd : Vtx.AmbientQuatDatum co3X36 (R.map co3X36.subtype) (t : Equiv.Perm (Fin 36)) := by
    refine ⟨?_, ⟨(R.equivMapOfInjective _ hinj).symm.trans eR⟩,
      Vtx.isUniqueInvolution_map _ hinj hC.inv, ?_⟩
    · rintro _ ⟨r, -, rfl⟩
      exact r.2
    · intro c hc hct
      have hm : (⟨c, hc⟩ : ModSp0) ∈ (⊤ : Subgroup ModSp0) ⊓
          Subgroup.centralizer ({t} : Set ModSp0) :=
        ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hct)⟩
      have e1 : conjSub c (R.map co3X36.subtype) = (conjSub (⟨c, hc⟩ : ModSp0) R).map co3X36.subtype :=
        conjSub_map co3X36.subtype ⟨c, hc⟩ R
      rw [e1]
      rcases hC.twins _ hm with h | h
      · left; rw [h]
      · right
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        have := h x hx y hy
        exact congrArg Subtype.val this
  obtain ⟨g, hg, hgK⟩ := ident_ambient hd
  have hs' : g * (t : Equiv.Perm (Fin 36)) * g⁻¹ = tab sp6Rep2 := by
    have h1 : g * (t : Equiv.Perm (Fin 36)) * g⁻¹ ∈ L0 () := by
      rw [← mem_K0_iff, ← hgK]
      exact conj_mem_conjSub ⟨t, hC.inv.mem, rfl⟩
    have h2 : g * (t : Equiv.Perm (Fin 36)) * g⁻¹ * (g * (t : Equiv.Perm (Fin 36)) * g⁻¹) = 1 := by
      have hsq : (t : Equiv.Perm (Fin 36)) * (t : Equiv.Perm (Fin 36)) = 1 := by
        have := congrArg Subtype.val hC.inv.sq
        simpa using this
      calc g * (t : Equiv.Perm (Fin 36)) * g⁻¹ * (g * (t : Equiv.Perm (Fin 36)) * g⁻¹)
          = g * ((t : Equiv.Perm (Fin 36)) * t) * g⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    rcases TwinE4Sp6.L0_inv _ h1 h2 with h3 | h3
    · exfalso
      apply hC.inv.ne_one
      apply Subtype.ext
      calc (t : Equiv.Perm (Fin 36)) = g⁻¹ * (g * (t : Equiv.Perm (Fin 36)) * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
    · exact h3
  refine ⟨⟨g, hg⟩, ?_, Subtype.ext hs'⟩
  ext y
  rw [mem_conjSub_iff]
  have h1 : y ∈ K0H ↔ (y : Equiv.Perm (Fin 36)) ∈ conjSub g (R.map co3X36.subtype) := by
    rw [hgK]; rfl
  rw [h1, mem_conjSub_iff]
  constructor
  · intro h
    refine ⟨_, h, rfl⟩
  · rintro ⟨r, hr, hre⟩
    have : r = (⟨g, hg⟩ : ModSp0)⁻¹ * y * ⟨g, hg⟩ := Subtype.ext (by simpa using hre)
    rw [← this]
    exact hr

theorem sp0_of_tfacts (hT : Sp0TFacts) : NoSandwichAt ModSp0 := by
  have hLie : CFSG.Blueprint.LieModel ModSp0 .PSp 3 2 1 :=
    Or.inl ⟨by decide, co3X36_classicalModel⟩
  have : Finite ModSp0 := inferInstance
  exact noSandwichAt_of_in (noSandwichIn_of_ident_tfacts hT
    (Sp0Aut.autInner_of_lieModel_PSp hLie) sp0_ident)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711
