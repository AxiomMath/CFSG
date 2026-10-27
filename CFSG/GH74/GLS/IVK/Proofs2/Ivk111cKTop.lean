module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKCliff
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKMain
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage4.Rest.T2
open scoped TensorProduct MonoidAlgebra

theorem mix11c_clifford {p : ℕ} (hp : p.Prime) {H : Type} [Group H] [Finite H] (K : Subgroup H)
    [K.Normal] {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρ : Representation (ZMod p) H V)
    (hρ : IsSimpleModule (MonoidAlgebra (ZMod p) H) ρ.asModule)
    (hK : Function.Injective (resRep ρ K)) (hKne : Nontrivial K) {m : ℕ}
    (hmin : ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
      (σ : Representation (ZMod p) ↥K W), IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) σ.asModule →
      (∃ k, σ k ≠ 1) → m ≤ Module.finrank (ZMod p) W)
    (hd : Module.finrank (ZMod p) V < 2 * m) :
    IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) (resRep ρ K).asModule := by
  have : Fact p.Prime := ⟨hp⟩
  exact Mix11cK.clifford_core ρ hρ K hK hKne hmin hd

theorem ivk_11_1c_fixed_of_kclass (hC : Mix11cKClass) : IVK.Proofs2.IVK_11_1c_fixed := by
  intro p n hp hp2 H _ _ K _ hKmodel V _ _ _ ρ hinj hsimple h1 h2
  have hn : 0 < n := by omega
  obtain ⟨hKne, ha, hb, hc⟩ := hC p n hp hp2 hn K hKmodel
  have hKinj : Function.Injective (resRep ρ K) := hinj.comp K.subtype_injective
  have hs : IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) (resRep ρ K).asModule :=
    mix11c_clifford hp K ρ hsimple hKinj hKne (m := 2 * n) (fun W _ _ _ σ hσ hk => ha W σ hσ hk)
      (by omega)
  rcases hb V (resRep ρ K) hKinj hs h1 h2 with ⟨hmod, hd⟩ | ⟨hmod, hd, hend⟩
  · left
    refine ⟨hmod, hd, hs, ?_⟩
    intro V' _ _ _ ρ' hρ' hdim' hs'
    exact hc V V' (resRep ρ K) (resRep ρ' K) hKinj hs (hρ'.comp K.subtype_injective) hs' h1 h2 hdim'
  · right
    refine ⟨hmod, hd, hs, hend, ?_⟩
    intro V' _ _ _ ρ' hρ' hdim' hs'
    exact hc V V' (resRep ρ K) (resRep ρ' K) hKinj hs (hρ'.comp K.subtype_injective) hs' h1 h2 hdim'

theorem ivk_11_1c_fixed_of_sl2class (h : Mix11cSL2Class) : IVK.Proofs2.IVK_11_1c_fixed :=
  ivk_11_1c_fixed_of_kclass (mix11c_kclass_of_sl2 h)

end CFSG.GH74.GLS.Stage4.Rest
