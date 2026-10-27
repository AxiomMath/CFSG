module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.XbarGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathCase
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std

@[expose] def Fin76aWreathNoFusionM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L .M22 →
    ∀ (z t : G) (F L1 N : Subgroup G), z ∈ centralizer (L : Set G) → orderOf z = 2 →
      centralizer ({z} : Set G) ≤ L ⊔ zpowers z →
      ∀ S : Setup L z t F L1 N, (∀ x ∈ L1, ¬ IsConj z x) →
        NormQuot (alternatingGroup (Fin 6)) (normalizer (F : Set G) ⊓ L) F →
        ∀ N1 N2 : Subgroup (Ybar L1),
          Nonempty (N1 ≃* alternatingGroup (Fin 6)) → Nonempty (N2 ≃* alternatingGroup (Fin 6)) →
          (∀ a ∈ N1, ∀ b ∈ N2, a * b = b * a) → Disjoint N1 N2 → (N1 ⊔ N2).Normal →
          (N1 ⊔ N2).index = 2 → piY L1 S.zX ∉ N1 ⊔ N2 →
          N1.map (MulAut.conj (piY L1 S.zX)).toMonoidHom = N2 →
          ∀ g : G, g⁻¹ * z * g ∉ preimageY L1 (N1 ⊔ N2)

end CFSG.EvenSporadicStandard.M22Std
