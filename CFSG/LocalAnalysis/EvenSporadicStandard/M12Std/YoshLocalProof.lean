module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelCert

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.M12Std.Yosh

structure SolomonA12HypGL (K : Type) [Group K] : Prop where
  fusionSimple : FusionSimple K
  sylowType : ∃ (S : Sylow 2 K) (S' : Sylow 2 (alternatingGroup (Fin 12))),
    Nonempty (↥(S : Subgroup K) ≃* ↥(S' : Subgroup (alternatingGroup (Fin 12))))
  exists_E : ∃ E : Subgroup K, (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 2 ^ 6 ∧
    Nat.card (normalizer (E : Set K)) = 2 ^ 6 * 168 ∧ ¬ E.Normal ∧
    Nonempty (↥(normalizer (E : Set K)) ⧸ E.subgroupOf (normalizer (E : Set K)) ≃*
      GL (Fin 3) (ZMod 2))

section Certified

set_option linter.unusedSectionVars false

@[expose] def Yoshida74LocalOfSwapGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (t : G), orderOf t = 2 →
    ∀ (e₀ : centralizer ({t} : Set G) ≃* Multiplicative (ZMod 2) × G12) (α : ℕ) (d : G),
      (α = 0 ∨ α = 1) → CentralSwap e₀ α d →
        ∃ c : G, orderOf c = 2 ∧ commutator (centralizer ({c} : Set G)) = ⊤ ∧
          Nat.card (center (centralizer ({c} : Set G))) = 2 ∧
          SolomonA12HypGL (centralizer ({c} : Set G) ⧸ center (centralizer ({c} : Set G)))

end Certified

section Proof

set_option linter.unusedSectionVars false

theorem yoshida74LocalOfSwapGL_holds : Yoshida74LocalOfSwapGL := by
  intro G _ _ hG t ht e₀ α d hα hd
  have M : ModelChecks := modelChecks
  have hα1 : α = 1 := yosh6 hG M ht hα hd
  subst hα1
  obtain ⟨k, hk, Ψ, hinj, hrange, hgen, hrel⟩ := yosh5 e₀ ht (by norm_num) hd
  let E : NEmb e₀ d 1 k := ⟨Ψ, hinj, hrange, hgen, hrel⟩
  have R := yosh8_model hG (M.fusion 1 k (by norm_num) hk) E ht hd (M.ue 1 k (by norm_num) hk)
    (M.es 1 k (by norm_num) hk) (M.l7 k hk) (M.l8 k hk) (M.sylowHom k hk)
  exact ⟨cG e₀, orderOf_cG e₀, R.out.perfect, R.out.card_center,
    ⟨R.out.fusionSimple, R.sylowType, R.out.exists_E⟩⟩

end Proof

end CFSG.EvenSporadicStandard.M12Std
