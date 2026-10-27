module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OneStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AltOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OutRows

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
open CFSG.ComponentClassification.SolMax.FiveCat

theorem Harada.card_centralizer_of_equiv {G : Type*} [Group G] {t : G}
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    Nat.card ↥(centralizer ({t} : Set G)) = 240 := by
  rw [Nat.card_congr ζ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)),
    Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)), Fintype.card_perm, Fintype.card_fin]
  rfl

theorem catHaradaAS_of_parts (hleaf : FivePumpLeaf) (hL216 : NoZ2S5L216) (hU34 : NoZ2S5U34)
    (hPSp : NoZ2S5PSp45) (hJ1 : NoZ2S5J1) (hJ2 : NoZ2S5J2) (hM12 : HaradaM12) :
    CatHaradaAS := by
  intro G _ _ S hSn hS hnab hcat hcent t ht hC
  obtain ⟨ζ⟩ := hC
  haveI := hSn
  have hder := derived_le_of_cent hSn hS hnab hcent ht ζ
  rcases fivePumpOutcome_one hleaf hSn hS hnab hcat hcent ht ζ with ⟨m, hm, hm7, ⟨θ⟩⟩ | hnon
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alt_arm_one hSn hcent ht hm hm7 θ hder
        (derived_equiv_alt_five ζ) (Harada.card_centralizer_of_equiv ζ))))))
  · rcases hnon with h | h | h | h | h | h | h | h | h | h
    · exact (hL216 G S hSn h hcent t ht hder ⟨ζ⟩).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (lieModel_commutator_commutator_of_L34 hSn hS hnab hcent h))))))
    · exact (hU34 G S hSn h hcent t ht hder ⟨ζ⟩).elim
    · exact Or.inr (Or.inl (lieModel_commutator_of_L225 hSn hS hnab hcent h))
    · exact Or.inr (Or.inr (Or.inl (lieModel_commutator_of_L35 hSn hS hnab hcent h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (lieModel_commutator_commutator_of_U35 hSn hS hnab hcent h))))
    · exact (hPSp G S hSn h hcent t ht hder ⟨ζ⟩).elim
    · exact (hJ1 G S hSn h hcent t ht hder ⟨ζ⟩).elim
    · exact (hJ2 G S hSn h hcent t ht hder ⟨ζ⟩).elim
    · obtain ⟨θ⟩ := h
      have htop : S = ⊤ := hM12 G S hSn ⟨θ⟩ hcent t ht ⟨ζ⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans
          θ⟩)))))

end CFSG.EvenSporadicStandard.HSStd.InvCent
