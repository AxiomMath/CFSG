module

public import CFSG.Goldschmidt75.B1Steps
public import CFSG.Goldschmidt75.TheoremA

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_normalClosure_le_comap
    (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T)
    (hAn : (S ⊓ perfRes (centralizer (S : Set G))).Normal) :
    ⁅normalClosure (S : Set G), normalClosure (((T : Subgroup G) ⊓
        perfRes (centralizer (S : Set G)) : Subgroup G) : Set G)⁆ ≤
      (goldschmidtOddCore (G ⧸ (S ⊓ perfRes (centralizer (S : Set G))))).comap
        (QuotientGroup.mk' _) := by
  set L := perfRes (centralizer (S : Set G)) with hL
  set A := S ⊓ L with hA
  set R := (T : Subgroup G) ⊓ L with hR
  set q := QuotientGroup.mk' A with hq
  have hsurj := QuotientGroup.mk'_surjective A
  have hRT : R ≤ T := inf_le_left
  have hRcl := stronglyClosed_inf_perfRes T hST hS
  have hRC : R ≤ centralizer (S : Set G) := inf_le_right.trans (perfRes_le _)
  have hSR : ⁅S, R⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hRC
  have h₁ : S.map q ≤ (sylowMap A T : Subgroup (G ⧸ A)) := by
    rw [coe_sylowMap]; exact map_mono hST
  have h₂ : R.map q ≤ (sylowMap A T : Subgroup (G ⧸ A)) := by
    rw [coe_sylowMap]; exact map_mono hRT
  have hdisj : S.map q ⊓ R.map q = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨s, hs, rfl⟩, ⟨r, hr, hrs⟩⟩
    rw [mem_bot]
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrs
    have hrS : r ∈ S := by
      have := mul_mem hs (inv_mem (mem_inf.mp hrs).1)
      simpa using this
    have hrA : r ∈ A := mem_inf.mpr ⟨hrS, (mem_inf.mp hr).2⟩
    have e : q s = q r := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := inv_mem hrs
      simpa using this
    rw [e, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hrA
  have hThA := theoremA (sylowMap A T) (sylowMap A T) h₁ h₂ (stronglyClosed_map A T hST hS)
    (stronglyClosed_map A T hRT hRcl) (by rw [← map_commutator, hSR, Subgroup.map_bot]) hdisj
  rw [← map_le_iff_le_comap, map_commutator, Subgroup.map_normalClosure _ _ hsurj,
    Subgroup.map_normalClosure _ _ hsurj, ← coe_map, ← coe_map]
  exact hThA

theorem perfRes_le_normalClosure (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    perfRes (centralizer (S : Set G)) ≤ normalClosure (((T : Subgroup G) ⊓
      perfRes (centralizer (S : Set G)) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := perfRes (centralizer (S : Set G)) with hL
  set W := normalClosure (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) with hW
  obtain ⟨P, hP⟩ := G310.exists_sylow_of_fusionIsSylowIn (fusionIsSylowIn_inf_perfRes T hST hS)
  have : W.Normal := normalClosure_normal
  have hPW : (P : Subgroup L) ≤ W.subgroupOf L := by
    intro x hx
    rw [mem_subgroupOf]
    apply le_normalClosure
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  have hodd : Odd (W.subgroupOf L).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hPW))
  exact le_of_perfect_of_odd_index (commutator_perfRes _) normal_subgroupOf hodd

end CFSG.Goldschmidt75
