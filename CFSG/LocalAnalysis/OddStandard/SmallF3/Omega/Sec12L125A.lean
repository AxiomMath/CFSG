module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma125a_of (hp : Asc82Pre11) (h124 : Asc82Lemma124) : Asc82Lemma125a := by
  intro G _ _ t L S z K1 K2 E hctx
  have hcore := sec125_core_of hp hctx (h124 G t L S z K1 K2 E hctx)
  have hsyl : IsSylow2Of (secV t S L E) (centralizer (secV t S L E : Set G)) :=
    hcore.sylow hctx.sylowE.2.1
  generalize secV t S L E = V at hcore hsyl ⊢
  have hVD : V ≤ centralizer (V : Set G) := hcore.V_le_centralizer
  have hcomm : ∀ k ∈ centralizer (V : Set G), ∀ z ∈ V, z * k = k * z :=
    fun k hk z hz => Subgroup.mem_centralizer_iff.mp hk z hz
  have h1 : V ⊔ oddCoreIn (centralizer (V : Set G)) = centralizer (V : Set G) :=
    sup_oddCoreIn_of_central_sylow hsyl hcomm
  have hDN : centralizer (V : Set G) ≤ secN V := fun x hx => Subgroup.centralizer_le_normalizer _ hx
  have hDnorm : ((centralizer (V : Set G)).subgroupOf (secN V)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDN]
    intro d n hd hn
    exact Sec125Core.conj_mem_centralizer hn hd
  have h2 : oddCoreIn (centralizer (V : Set G)) ≤ oddCoreIn (secN V) :=
    oddCoreIn_le_of_normal hDN hDnorm
  have hVN : V ≤ secN V := Subgroup.le_normalizer
  have hVnorm : (V.subgroupOf (secN V)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVN]
    exact le_rfl
  have hV2 : IsPGroup 2 V := hctx.sylowE.2.1.to_le (hcore.V_le)
  have h3 : ∀ p ∈ V, ∀ o ∈ oddCoreIn (secN V), p * o = o * p :=
    commute_of_normal_two_odd hVN (oddCoreIn_normal (secN V)).1 hVnorm
      (oddCoreIn_normal (secN V)).2 hV2 (odd_card_oddCoreIn (secN V))
  have h4 : oddCoreIn (secN V) ≤ centralizer (V : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact h3 v hv o ho
  refine le_antisymm ?_ (sup_le hVD h4)
  calc centralizer (V : Set G) = V ⊔ oddCoreIn (centralizer (V : Set G)) := h1.symm
    _ ≤ V ⊔ oddCoreIn (secN V) := sup_le_sup_left h2 V

end CFSG.OddStandard.SmallF3.Omega
