module

public import CFSG.GH74.Generic.S1.TLeafBarHigh
public import CFSG.GH74.Generic.S1.KL5
public import CFSG.GH74.Generic.S1.TLeafBar
public import CFSG.GH74.KGroups.BalanceLift

public section

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.LocalCores CFSG.Assembly.LowTwoRank
  CFSG.GH74.Filter.ClassicalOdd
open scoped commutatorElement

namespace CFSG.GH74.Generic.S1

section Main

theorem s1LeafCompBarHigh_of_KL5
    (hExact : S1LiftExactProp) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hK : KL5Table) : S1LeafCompBarHigh := by
  intro G _ _ x K hset hfront hbigK u hu hf hsym c hcJ hc2 hcc
  obtain ⟨M, hM, hAM⟩ := sym_component_of_L hExact hset hfront hbigK hf hsym hcJ hc2 hcc
  obtain ⟨-, -, hlay3⟩ := sym_barSub_le_layer hExact hset hfront hbigK hf hsym hcJ hc2 hcc
  have hcomm := symJ_comm_high hExact hset hfront hbigK hf hsym
  have hLJ := sup_comm_three hcomm
  have hc2' : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hccC : c ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hcommBar : ∀ j ∈ S45.barSub c (symJ (symX x u) 3),
      ∀ a ∈ S45.barSub c (symJ (symX x u) 0 ⊔ symJ (symX x u) 1), a * j = j * a := by
    intro j hj a ha
    obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 hj
    obtain ⟨l, hl, hlL, rfl⟩ := S45.mem_barSub.1 ha
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hLJ l hlL g hgJ)
  obtain ⟨ε, p, f, hSL3, ⟨ψ, hψ, hψJ⟩, hB4⟩ :=
    sym_sl3Pair_bar hExact hset hfront hbigK hf hsym hcJ hcc
  have hodd : Odd (p ^ f) := (hSL3.prime.odd_of_ne_two hSL3.ne_two).pow
  have hH : Gen4 (CentralizerBar c) := gen4_centralizerBar hset.gen4 c
  have hJ4M : ∀ j ∈ S45.barSub c (symJ (symX x u) 3), ∀ w ∈ M, j * w = w * j := by
    obtain ⟨t, htB, ht2, hinvB, hcenB⟩ := sl2_involution_facts hodd hB4
    have hcbB : proj c ⟨c, hccC⟩ ∈ S45.barSub c (symJ (symX x u) 3) :=
      S45.proj_mem_barSub hccC hcJ
    have hcb2 : proj c ⟨c, hccC⟩ * proj c ⟨c, hccC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨c, hccC⟩ : ↥(centralizer ({c} : Set G))) * ⟨c, hccC⟩ = 1 := Subtype.ext hc2'
      rw [this, map_one]
    have hcb1 : proj c ⟨c, hccC⟩ ≠ 1 := by
      intro h
      have := S45.eq_one_of_proj_eq_one_of_sq hccC h hc2'
      rw [this, orderOf_one] at hc2
      exact absurd hc2 (by norm_num)
    have hcbt : proj c ⟨c, hccC⟩ = t := (hinvB _ hcbB hcb2).resolve_left hcb1
    have hcbcen : ∀ h : CentralizerBar c, h * proj c ⟨c, hccC⟩ = proj c ⟨c, hccC⟩ * h := by
      intro h
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective h
      show proj c k * proj c ⟨c, hccC⟩ = proj c ⟨c, hccC⟩ * proj c k
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 k.2)
    obtain ⟨ψB, hψBi, hψB⟩ := exists_q8_of_hasSL2Model hodd hB4
    have hψBc : ψB (QuaternionGroup.a 2) = proj c ⟨c, hccC⟩ := by
      have hsq : ψB (QuaternionGroup.a 2) * ψB (QuaternionGroup.a 2) = 1 := by
        rw [← map_mul]
        have : (QuaternionGroup.a 2 : Q8) * QuaternionGroup.a 2 = 1 := by decide
        rw [this, map_one]
      rcases hinvB _ (hψB _) hsq with h | h
      · exfalso
        have : (QuaternionGroup.a 2 : Q8) = 1 := hψBi (h.trans (map_one ψB).symm)
        exact absurd this (by decide)
      · rw [hcbt]; exact h
    obtain ⟨ψA, hψAi, hψAV⟩ := exists_q8_of_hasSL2Model hodd hSL3.sl2
    have hGHS : GHList (↥M ⧸ center ↥M) :=
      ghList_of_quasisimple hset.simple hset.nonab hset.kgh hc2 hM.1
    have hBq : IsQuasisimple ↥(S45.barSub c (symJ (symX x u) 3)) :=
      isQuasisimple_of_sl2 (by have := hSL3.five_le; omega) hB4
    have hdec : ∀ j ∈ S45.barSub c (symJ (symX x u) 3), ∃ m ∈ M,
        ∃ d ∈ layer (CentralizerBar c) ⊓ centralizer (M : Set (CentralizerBar c)), j = m * d := by
      intro j hj
      obtain ⟨y', hy', τ, hτ, hyτ⟩ := CFSG.GH74.KGroups.Bal.layer_decomposition hM j (hlay3 hj)
      exact ⟨y', hy', τ, hτ, hyτ.symm⟩
    have hDlay : ∀ z ∈ center ↥M, (z : CentralizerBar c) ∈
        layer (CentralizerBar c) ⊓ centralizer (M : Set (CentralizerBar c)) := fun z hz =>
      ⟨(layer_normal_contains _).2 M hM z.2, Subgroup.mem_centralizer_iff.2 fun m hm => by
        have := Subgroup.mem_center_iff.1 hz ⟨m, hm⟩
        exact congrArg Subtype.val this⟩
    have hcbD : proj c ⟨c, hccC⟩ ∈
        layer (CentralizerBar c) ⊓ centralizer (M : Set (CentralizerBar c)) :=
      ⟨hlay3 hcbB, Subgroup.mem_centralizer_iff.2 fun m _ => hcbcen m⟩
    exact jcentral_of_KL5 (M := M) (D := layer (CentralizerBar c) ⊓ centralizer (M : Set (CentralizerBar c)))
      (B := S45.barSub c (symJ (symX x u) 3))
      (A := S45.barSub c (symJ (symX x u) 0 ⊔ symJ (symX x u) 1)) hK hGA hH hM.1 hGHS
      (fun d hd m hm => (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hd).2 m hm).symm)
      hDlay hdec hBq hSL3.prime hSL3.ne_two hSL3.five_le hB4 hcbD hcb1
      (fun z hz hzc => (hcenB z hz hzc).imp id (fun h => hcbt.symm ▸ h)) ψB hψB hψBi hψBc
      hSL3.model hSL3.quasi hAM hSL3.center_odd ψA hψAi (fun g => hSL3.le (hψAV g))
      (fun a ha j hj => hcommBar j hj a ha)
  obtain ⟨y, hyV, hy2, hVn⟩ := sym_bar_normal hExact hset hfront hbigK hf hsym hcJ hc2 hcc
  have hAeq := component_eq_of_sl3_pair hGA hH hM.1 ψ hψ (fun a m hm => hJ4M (ψ a) (hψJ a) m hm)
    hSL3 hAM hyV hy2 hVn
  rw [hAeq]
  exact hM.2

end Main

end CFSG.GH74.Generic.S1
