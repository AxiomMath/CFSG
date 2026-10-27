module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutResidue3
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M23Std

theorem exists_wr_hom {X : Type} [Group X] (f : X →* Equiv.Perm (Fin 2 × Fin 6))
    (hf : Function.Injective f) (hW : ∀ g, f g ∈ wreathS6Z2) :
    ∃ f' : X →* Wr, Function.Injective f' := by
  have hmem : ∀ g, f g ∈ wrPerm.range := fun g => exists_wr_of_mem_wreathS6Z2 (hW g)
  refine ⟨(MonoidHom.ofInjective wrPerm_injective).symm.toMonoidHom.comp
    (f.codRestrict wrPerm.range hmem), ?_⟩
  intro g g' hgg
  have h1 := (MonoidHom.ofInjective wrPerm_injective).symm.injective hgg
  exact hf (congrArg Subtype.val h1)

theorem fin77aOuterResidue₃_a6a6 :
    Fin77aOuterSit fun X _ _ _ => ¬ (Nonempty (egaLayer X ≃*
      alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∧
      ∃ f : X →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2) := by
  intro G _ _ _ L z t T₁ F tb Q x L1 hS hz hC ⟨⟨e⟩, f, hf, hW⟩
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  obtain ⟨f', hf'⟩ := exists_wr_hom f hf hW
  have hz2 : (QuotientGroup.mk ⟨z, hz⟩ : Xbar L1) * QuotientGroup.mk ⟨z, hz⟩ = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk Sup.zX : Xbar L1)
    rwa [Sup.orderOf_zbar, sq] at this
  have hCcard : Nat.card (centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} :
      Set (Xbar L1))) = 1440 := by
    obtain ⟨φ⟩ := hC
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 6)),
      Fintype.card_perm, Fintype.card_fin]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    rw [h2]
    decide
  have hsit : WrSit (Xbar L1) (QuotientGroup.mk ⟨z, hz⟩) f' (egaLayer (Xbar L1)) :=
    ⟨hf', hz2, egaLayer_normal _, ⟨e⟩, hCcard⟩
  exact hS.false_of_outerWr hz hsit.outerWr_of_wrSit

end CFSG.EvenSporadicStandard.M22Std
