module

public import CFSG.GH74.GLS.C3.Layer1.Th2NV7Core
public import CFSG.GH74.GLS.C3.Layer1.Th2HYM
public import CFSG.GH74.GLS.C3.Layer1.Th2NV7Frat
public import CFSG.GH74.GLS.C3.Layer1.Th2P812A7

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.HY CFSG.GH74.GLS.Th2.NV7

@[expose] def B_thm2_p812_NV7' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) → K ≤ M → T ≤ M →
      IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
      ∀ L : Subgroup G, IsMinSubnormalIn K M L → IsPCompIn 2 M L → L = pPrimeCoreOf 2 L ⊔ K →
        ∀ V : Subgroup G, V ≤ T ⊓ CxK x K → CFSG.IsElementaryAbelian 2 ↥V → V ≠ ⊥ →
          IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
            (normalizer (V : Set G) ⊓ CMbar M K) →
          pPrimeCoreOf 2 (normalizer (V : Set G)) ≤ M →
          ∀ U : Subgroup G, IsDSub K (T ⊓ K) U →
            normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M →
            normalizer ((U ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G) : Set G) ≤ M →
              normalizer (V : Set G) ≤ M

theorem b_thm2_p812_NV7'_proved : B_thm2_p812_NV7' := by
  intro G _ _ hG x y K T S M hstd h7 hKM hTM hQ L hLmin hLcomp hLeq V hVQ hVel hVne hQ1 hO U hU
    hFUV hUQ₁
  obtain ⟨e7⟩ := h7
  have hsimple : IsSimpleGroup (kBar K) := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
    exact MulEquiv.isSimpleGroup e7
  have hS : HYSetup x y K T S V :=
    ⟨hstd, hsimple, centerlessBar_of_A7 ⟨e7⟩, hVQ, hVel, hVne⟩
  have hU4 : IsFourSub (T ⊓ K) U := Th2.P812A7.IsDSub.isFourSub hU
  have ha := Q₁_sylow_YV hG hS hKM hO hLcomp hLeq hLmin.1 hU4 hFUV hQ1
  have hSyl := hS.sylow_HY hG ha
  have hVnorm : ∀ n ∈ normalizer (V : Set G), ∀ v ∈ V, n * v * n⁻¹ ∈ V := fun n hn v hv =>
    (Subgroup.mem_normalizer_iff.1 hn v).1 hv
  have hFT : U ⊔ V ≤ T := sup_le (hU.1.trans inf_le_left) (hVQ.trans inf_le_left)
  have hPH : T ⊓ K ≤ HV K V := hS.P_le_lamV.trans le_sup_left
  exact frattini_core' (HYSetup.HV_le_N K V) (hS.hnormH hG)
    (sup_le ((twoGen_le _).trans (inf_le_left.trans hKM)) hO) hO (hU.1.trans hPH) hVnorm
    (hstd.T_pGroup.to_le hFT)
    (sup_le (hU.1.trans (hPH.trans (HYSetup.HV_le_N K V))) Subgroup.le_normalizer) hFUV hSyl
    (fun m hmN hmS => mem_M_of_normalizes_S₀ hG hS hU hUQ₁ hmN hmS)

end CFSG.GH74.GLS
