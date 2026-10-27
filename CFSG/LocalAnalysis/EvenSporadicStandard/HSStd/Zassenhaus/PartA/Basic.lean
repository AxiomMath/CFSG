module

public import CFSG.Open.FusionDefs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

section Vocabulary

variable {G : Type*} [Group G]

abbrev Cen (a : G) : Subgroup G := centralizer ({a} : Set G)

theorem mem_Cen {a g : G} : g ∈ Cen a ↔ g * a = a * g :=
  mem_centralizer_singleton_iff

abbrev OQuot (H : Subgroup G) : Type _ := ↥H ⧸ Open.fusionOddCore ↥H

@[expose] def oMk (H : Subgroup G) : ↥H →* OQuot H := QuotientGroup.mk' _

@[expose] def derivedIn (A : Subgroup G) : Subgroup G := (commutator ↥A).map A.subtype

theorem derivedIn_le (A : Subgroup G) : derivedIn A ≤ A := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

abbrev Vsub (t u : G) : Subgroup G := zpowers t ⊔ zpowers u

theorem oMk_surjective (H : Subgroup G) : Function.Surjective (oMk H) :=
  QuotientGroup.mk'_surjective _

end Vocabulary

section OddCore

variable {G : Type*} [Group G]

theorem fusionOddCore_eq_standardComponentOddCore (H : Type*) [Group H] :
    Open.fusionOddCore H = Open.standardComponentOddCore H := rfl

theorem fusionOddCoreOf_eq (H : Subgroup G) :
    Open.fusionOddCoreOf H = (Open.fusionOddCore ↥H).map H.subtype := rfl

theorem fusionOddCoreOf_le (H : Subgroup G) : Open.fusionOddCoreOf H ≤ H := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

end OddCore

section SgnProd

open Equiv

@[expose] noncomputable def sgnProd : Wr2 (Perm (Fin 5)) →* ℤˣ :=
  SemidirectProduct.lift
    ((Perm.sign : Perm (Fin 5) →* ℤˣ).comp (MonoidHom.fst _ _) *
      (Perm.sign : Perm (Fin 5) →* ℤˣ).comp (MonoidHom.snd _ _))
    1 (by
      intro g
      ext ⟨a, b⟩
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MulEquiv.coe_toMonoidHom,
        MonoidHom.one_apply]
      obtain h | h := zmod2_cases g
      · subst h
        simp [swapHom]
      · subst h
        rw [swapHom_one']
        simp [swapEquiv, mul_comm])

theorem sgnProd_base (a b : Perm (Fin 5)) : sgnProd (base a b) = Perm.sign a * Perm.sign b := by
  simp [sgnProd, base]

theorem sgnProd_tau : sgnProd (tau : Wr2 (Perm (Fin 5))) = 1 := by
  simp [sgnProd, tau]

@[expose] noncomputable def DE4 : Subgroup (Wr2 (Perm (Fin 5))) := sgnProd.ker

theorem mem_DE4 {w : Wr2 (Perm (Fin 5))} : w ∈ DE4 ↔ sgnProd w = 1 := MonoidHom.mem_ker

end SgnProd

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
