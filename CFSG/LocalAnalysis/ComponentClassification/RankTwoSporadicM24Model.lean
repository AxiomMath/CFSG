module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Monster.CodeAut.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M24

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.M22
open CFSG.ABGLocalTools CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.Code

@[expose] noncomputable def autPermEquiv : ↥AutPerm ≃* ↥Blueprint.NativeSporadic.M24 :=
  (MulEquiv.subgroupCongr (AutPerm_eq_closure.trans bridge_closure_eq_map)).trans
    (Blueprint.NativeSporadic.M24.equivMapOfInjective _ (MulAut.conj bridgeQ⁻¹).injective).symm

theorem m24AutModel_of (hc : center ↥Blueprint.NativeSporadic.M24 = ⊥)
    (hi : OuterAutomorphisms.inner ↥Blueprint.NativeSporadic.M24 = ⊤) :
    AutModel (Blueprint.NativeSporadic.Carrier .M24) ↥AutPerm ⊤ where
  normal := inferInstance
  centralizer_eq_bot := by
    rw [coe_top, centralizer_univ]
    apply (map_eq_bot_iff_of_injective (center ↥AutPerm)
      (f := ((autPermEquiv : ↥AutPerm ≃* ↥Blueprint.NativeSporadic.M24) :
        ↥AutPerm →* ↥Blueprint.NativeSporadic.M24)) autPermEquiv.injective).mp
    rw [map_center_eq autPermEquiv, hc]
  nonempty_mulEquiv := ⟨Subgroup.topEquiv.trans autPermEquiv⟩
  exists_conj α := by
    set f : ↥(⊤ : Subgroup ↥AutPerm) ≃* ↥Blueprint.NativeSporadic.M24 :=
      Subgroup.topEquiv.trans autPermEquiv
    have hβ : MulAut.congr f α ∈ OuterAutomorphisms.inner ↥Blueprint.NativeSporadic.M24 := by
      rw [hi]
      trivial
    obtain ⟨g, hg⟩ := hβ
    refine ⟨autPermEquiv.symm g, fun x => ?_⟩
    have h1 : f (α x) = g * f x * g⁻¹ := by
      have := congrArg (fun φ : MulAut ↥Blueprint.NativeSporadic.M24 => φ (f x)) hg
      simpa [MulAut.congr_apply] using this.symm
    have h2 : α x = f.symm g * x * (f.symm g)⁻¹ := by
      apply f.injective
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [h2]
    rfl

theorem m24_commutator_le :
    ⁅(⊤ : Subgroup ↥AutPerm), (⊤ : Subgroup ↥AutPerm)⁆ ≤ (⊤ : Subgroup ↥AutPerm) := le_top

theorem m24_yCensusII : YCensus (⊤ : Subgroup ↥AutPerm) (· ≤ (⊤ : Subgroup ↥AutPerm)) :=
  fun _ _ _ h => absurd le_top h

@[expose] def iota : ↥AutPerm →* Equiv.Perm (Fin 24) := AutPerm.subtype

theorem iota_injective : Function.Injective iota := Subtype.val_injective

theorem map_top_iota : (⊤ : Subgroup ↥AutPerm).map iota = AutPerm := by
  rw [← MonoidHom.range_eq_map]
  exact range_subtype AutPerm

end CFSG.ComponentClassification.RankTwoSporadic.M24
