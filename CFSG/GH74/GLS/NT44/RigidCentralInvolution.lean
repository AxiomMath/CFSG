module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem exists_involution_inf_zStar_of_mem_rigidSet
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {K T : Subgroup G}
    (hK : K ∈ RigidSet fullQ x)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G)))
    (h16 : Nat.card (Subgroup.center fullQ) = 16) :
    ∃ s : G, s ∈ T ⊓ zStar K ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : IsRigidOfType fullQ x K := hK
  have hZK : zStar K ≤ K := fun _ h => (Subgroup.mem_inf.mp h).1
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    CFSG.GH74.GLS.Stage1.Thm4.P92.sylow_inf hK' hT
  have hKZ : K ≤ Subgroup.normalizer (zStar K : Set G) := fun k hk =>
    CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_normalizer_zStar
      (Subgroup.le_normalizer hk)
  have hA : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ zStar K) (zStar K) := by
    have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hTK hZK hKZ
    have hEq : (T ⊓ K) ⊓ zStar K = T ⊓ zStar K := by
      rw [inf_assoc, inf_eq_right.mpr hZK]
    rwa [hEq] at h
  have hcenter : Nat.card (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)) = 16 := by
    obtain ⟨e⟩ := hK'.2
    calc
      Nat.card (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)) = Nat.card (Subgroup.center fullQ) :=
        Nat.card_congr (Subgroup.centerCongr e).toEquiv
      _ = 16 := h16
  have : Finite (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K) := Finite.of_surjective (hatMk K) (hatMk_surjective K)
  have hZeq : (zStar K).subgroupOf K =
      (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)).comap (hatMk K) := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center k
  have hcardZ : Nat.card (zStar K) = Nat.card (hatMk K).ker * 16 := by
    calc
      Nat.card (zStar K) = Nat.card ((zStar K).subgroupOf K) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv).symm
      _ = Nat.card ((Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)).comap (hatMk K)) := by rw [hZeq]
      _ = Nat.card (hatMk K).ker * Nat.card (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)) :=
        CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (hatMk K)
          (hatMk_surjective K) (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K))
      _ = Nat.card (hatMk K).ker * 16 := by rw [hcenter]
  have h2Z : 2 ∣ Nat.card (zStar K) := by
    rw [hcardZ]
    exact dvd_mul_of_dvd_right (by norm_num : (2 : ℕ) ∣ 16) _
  have hnotdvd : ¬ 2 ∣ (T ⊓ zStar K).relIndex (zStar K) :=
    ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 hA).2.2
  have hAne : T ⊓ zStar K ≠ ⊥ := by
    intro hbot
    have hcardA : (T ⊓ zStar K).relIndex (zStar K) = Nat.card (zStar K) := by
      rw [hbot]
      exact Subgroup.relIndex_bot_left (G := G) (H := zStar K)
    have hdvd : 2 ∣ (T ⊓ zStar K).relIndex (zStar K) := by
      rw [hcardA]
      exact h2Z
    exact hnotdvd hdvd
  obtain ⟨s, hs, hs2⟩ :=
    CFSG.ABGLocalTools.exists_mem_orderOf_eq_two hA.isPGroup hAne
  exact ⟨s, hs, hs2⟩


theorem exists_involution_inf_zStar_of_mem_rigidSet_of_even
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {K T : Subgroup G}
    (hK : K ∈ RigidSet fullQ x)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G)))
    (hEven : Even (Nat.card (Subgroup.center fullQ))) :
    ∃ s : G, s ∈ T ⊓ zStar K ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : IsRigidOfType fullQ x K := hK
  have hZK : zStar K ≤ K := fun _ h => (Subgroup.mem_inf.mp h).1
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    CFSG.GH74.GLS.Stage1.Thm4.P92.sylow_inf hK' hT
  have hKZ : K ≤ Subgroup.normalizer (zStar K : Set G) := fun k hk =>
    CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_normalizer_zStar
      (Subgroup.le_normalizer hk)
  have hA : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ zStar K) (zStar K) := by
    have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hTK hZK hKZ
    have hEq : (T ⊓ K) ⊓ zStar K = T ⊓ zStar K := by
      rw [inf_assoc, inf_eq_right.mpr hZK]
    rwa [hEq] at h
  have hcenter : Nat.card (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)) =
      Nat.card (Subgroup.center fullQ) := by
    obtain ⟨e⟩ := hK'.2
    exact Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have : Finite (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K) := Finite.of_surjective (hatMk K) (hatMk_surjective K)
  have hZeq : (zStar K).subgroupOf K =
      (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)).comap (hatMk K) := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center k
  have hcardZ : Nat.card (zStar K) = Nat.card (hatMk K).ker *
      Nat.card (Subgroup.center fullQ) := by
    calc
      Nat.card (zStar K) = Nat.card ((zStar K).subgroupOf K) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv).symm
      _ = Nat.card ((Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)).comap (hatMk K)) := by rw [hZeq]
      _ = Nat.card (hatMk K).ker * Nat.card (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K)) :=
        CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (hatMk K)
          (hatMk_surjective K) (Subgroup.center (CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT K))
      _ = Nat.card (hatMk K).ker * Nat.card (Subgroup.center fullQ) := by rw [hcenter]
  have h2Z : 2 ∣ Nat.card (zStar K) := by
    rw [hcardZ]
    exact dvd_mul_of_dvd_right hEven.two_dvd _
  have hnotdvd : ¬ 2 ∣ (T ⊓ zStar K).relIndex (zStar K) :=
    ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 hA).2.2
  have hAne : T ⊓ zStar K ≠ ⊥ := by
    intro hbot
    have hcardA : (T ⊓ zStar K).relIndex (zStar K) = Nat.card (zStar K) := by
      rw [hbot]
      exact Subgroup.relIndex_bot_left (G := G) (H := zStar K)
    have hdvd : 2 ∣ (T ⊓ zStar K).relIndex (zStar K) := by
      rw [hcardA]
      exact h2Z
    exact hnotdvd hdvd
  obtain ⟨s, hs, hs2⟩ :=
    CFSG.ABGLocalTools.exists_mem_orderOf_eq_two hA.isPGroup hAne
  exact ⟨s, hs, hs2⟩

end CFSG.GH74.GLS.NT44

end
