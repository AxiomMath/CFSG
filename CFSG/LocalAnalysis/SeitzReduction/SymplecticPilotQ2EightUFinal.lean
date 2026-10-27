module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def SpTwoUnitaryEvenEightProductInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k .unitaryEven) →
      (∀ (k l : Fin 4), k ≠ l → ∀ z ∈ centralizerPerfectCore
          (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)),
        ((e.symm (permSp K (Equiv.swap k l)) : L) : G) * z =
          z * ((e.symm (permSp K (Equiv.swap k l)) : L) : G)) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2)
        (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
        (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k),
        NsUniParamAgree P → NsUniProductCommute hF P

section Reduction

theorem spTwoUnitaryEvenEightAgreeInput_of_product (h : SpTwoUnitaryEvenEightProductInput) :
    SpTwoUnitaryEvenEightAgreeInput := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  have hkey : ∀ (k l : Fin 4), k ≠ l → ∀ z ∈ centralizerPerfectCore
      (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)),
      ((e.symm (permSp K (Equiv.swap k l)) : L) : G) * z =
        z * ((e.symm (permSp K (Equiv.swap k l)) : L) : G) := fun k l hkl z hz =>
    commute_permSp_swap_of_mem_overlap hset hK e ht hKt hroot hkl hz
  obtain ⟨F, _, _, _, hF, ι, hι, hpar⟩ :=
    exists_nsUniParam_even_of_three_le hset 3 hK le_rfl e ht hKt hroot
  obtain ⟨Q, hQ⟩ := exists_nsUniParamAgree_even_four hK hF (fun k => (hpar k).some) hkey
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, ι, hι, Q, hQ,
    h G L hset K hK e t ht hKt hroot hkey F hF ι hι Q hQ⟩

end Reduction

end CFSG.SeitzReduction.SymplecticPilot
