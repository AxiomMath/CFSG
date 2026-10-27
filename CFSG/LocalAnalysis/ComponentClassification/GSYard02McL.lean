module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import CFSG.Sporadic.Recognition.McLASEnum
public import CFSG.Sporadic.SmallOddCore.McL
public import Certificates.Certificate5186
public import Certificates.Certificate11005

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

theorem factorization_mclP_two : (898128000 : ℕ).factorization 2 = 7 := by
  rw [show (898128000 : ℕ) = 2 ^ 7 * 7016625 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 7016625)]
  rfl

theorem sylowFourJoined_mclP :
    SylowFourJoined mclP := by
  have FS := subEnumOK_spec mcl_groupData Certificates.certificate5186.1
  have FA := subEnumOK_spec mcl_groupData Certificates.certificate11005.1
  have hAsq := Certificates.certificate11005.2.1
  have hAnorm := Certificates.certificate11005.2.2
  have hsq : ∀ x ∈ closure (tp 275 '' {x | x ∈ sylAGens}), x * x = 1 := by
    intro x hx
    obtain ⟨k, hk, hrep⟩ := FA.enum.cover x hx
    have hmem : (mulClosureH 275 sylAGens 200).1[k]! ∈ (mulClosureH 275 sylAGens 200).1 := by
      rw [getElem!_pos _ k hk]
      exact Array.getElem_mem hk
    have h1 := Rep.compT hrep hrep
    have h2 := rep_of_tblEq h1 (Array.all_eq_true'.1 hAsq _ hmem)
    exact rep_unique h2 (Rep.idT (by norm_num))
  have hnorm : closure (tp 275 '' {x | x ∈ sylTwoGens}) ≤
      normalizer ((closure (tp 275 '' {x | x ∈ sylAGens}) : Subgroup (Equiv.Perm (Fin 275))) :
        Set (Equiv.Perm (Fin 275))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s ∈ sylTwoGens := hs
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k, hk, hrep⟩ := FA.enum.cover x hx
    have hmem : (mulClosureH 275 sylAGens 200).1[k]! ∈ (mulClosureH 275 sylAGens 200).1 := by
      rw [getElem!_pos _ k hk]
      exact Array.getElem_mem hk
    have hconj := Rep.compT (Rep.compT (FS.rep s hs') hrep) (FS.repInv s hs')
    have hmemT := Array.all_eq_true'.1 (Array.all_eq_true'.1 hAnorm s hs') _ hmem
    exact FA.enum.mem_of_memT hconj hmemT
  have hSP : Nat.card (closure (tp 275 '' {x | x ∈ sylTwoGens}) : Subgroup (Equiv.Perm (Fin 275)))
      = 128 := FS.card
  have hS'card : Nat.card ((closure (tp 275 '' {x | x ∈ sylTwoGens}) :
      Subgroup (Equiv.Perm (Fin 275))).subgroupOf mclP) = 2 ^ (Nat.card mclP).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe FS.le).toEquiv, hSP, card_mclP,
      factorization_mclP_two]
    norm_num
  have hSSA : ((Sylow.ofCard _ hS'card : Sylow 2 mclP) : Subgroup mclP) ≤ normalizer
      ((closure (tp 275 '' {x | x ∈ sylAGens}) : Subgroup (Equiv.Perm (Fin 275))).subgroupOf mclP :
        Set mclP) := by
    rw [Sylow.coe_ofCard]
    intro x hx
    have hx' : (x : Equiv.Perm (Fin 275)) ∈ closure (tp 275 '' {x | x ∈ sylTwoGens}) :=
      Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : (n : Equiv.Perm (Fin 275)) ∈ closure (tp 275 '' {x | x ∈ sylAGens}) :=
      Subgroup.mem_subgroupOf.mp hn
    have hN := Subgroup.mem_normalizer_iff.mp (hnorm hx') (n : Equiv.Perm (Fin 275))
    exact Subgroup.mem_subgroupOf.mpr (hN.mp hn')
  have hA2 : ∀ a ∈ (closure (tp 275 '' {x | x ∈ sylAGens}) :
      Subgroup (Equiv.Perm (Fin 275))).subgroupOf mclP, a * a = 1 := fun a ha =>
    Subtype.ext (hsq (a : Equiv.Perm (Fin 275)) (Subgroup.mem_subgroupOf.mp ha))
  have hA8 : 8 ≤ Nat.card ((closure (tp 275 '' {x | x ∈ sylAGens}) :
      Subgroup (Equiv.Perm (Fin 275))).subgroupOf mclP) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe FA.le).toEquiv, FA.card]
  exact sylowFourJoined_of_normal_elemAbelian (Sylow.ofCard _ hS'card) hSSA hA2 hA8

theorem leafMcL_holds :
    LeafSporadic .McL := by
  intro X _ _ _ _ hX
  obtain ⟨e⟩ := hX
  have e' : ↥mclP ≃* X := (mclPermEquiv).symm.trans e.symm
  exact SylowFourJoined.of_mulEquiv e' sylowFourJoined_mclP

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
