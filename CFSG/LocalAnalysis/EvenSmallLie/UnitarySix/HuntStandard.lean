module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntMain
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsNonsplit

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit CFSG.EvenSmallLie CFSG.ComponentClassification.WittDesign

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem std_exists_hyp
    (hset : StandardSetting G L) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    ∃ (t : G) (p : L →* Equiv.Perm (Fin 693)), orderOf t = 2 ∧ t ∈ (center L).map L.subtype ∧
      Hyp t L (toddLift p) p := by
  have := hset.simple
  obtain ⟨t, ht, htZ⟩ := exists_center_involution h2
  obtain ⟨z, hz, hzt⟩ := htZ
  have htL : t ∈ L := hzt ▸ z.2
  have htZ' : (⟨t, htL⟩ : L) ∈ center L := by
    have e : (⟨t, htL⟩ : L) = z := Subtype.ext hzt.symm
    rw [e]
    exact hz
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  obtain ⟨p, hp, hsurj, hker⟩ := exists_hom_T46 htL htZ' ht1 h2 hQ
  have htZ : t ∈ (center L).map L.subtype := ⟨z, hz, hzt⟩
  obtain ⟨hE2, hodd, hfus, hmove, hns⟩ := std_toddOrbit_fields hset ht htZ h2 hQ hp hsurj hker
  obtain ⟨D, hCE, -⟩ := davisSolomonFacts_uA hset ht htZ h2 hQ hp hsurj hker
  have hCL := (std_centralizer_eq_zpowers hset ht htZ D hCE).1
  have hLt : L ≤ centralizer ({t} : Set G) := (std_center_facts hset ht htZ).2.2.2.2.2.1
  have H : ToddOrbit.Hyp t L (toddLift p) p :=
    ⟨hp, hsurj, hker, htL, hLt, ht, fun _ => mem_toddLift, hE2, hodd, hfus, hmove, hns⟩
  exact ⟨t, p, ht, htZ, Hyp.of_simple hset.nonab H D hCE hCL⟩

end CFSG.EvenSmallLie.UnitarySix.Hunt
