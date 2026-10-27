module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.NoLift
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup

theorem ker_comp_inclusion_eq {H : Type*} [Group H] {z : H} {R0 : Subgroup H} (hzR : z ∈ R0)
    (hR0 : IsPGroup 2 R0)
    {ψ : ↥(centralizer ({z} : Set H)) →* Equiv.Perm (Fin 5)}
    (hker : ψ.ker = R0.subgroupOf (centralizer ({z} : Set H)))
    {Y : Subgroup H} (hY : Y ≤ centralizer ({z} : Set H))
    {f : ↥Y →* alternatingGroup (Fin 5)} (hf : Function.Surjective f)
    (hfk : f.ker ≤ (zpowers z).subgroupOf Y) :
    (ψ.comp (Subgroup.inclusion hY)).ker = f.ker := by
  have hzR0 : zpowers z ≤ R0 := Subgroup.zpowers_le.mpr hzR
  have hmem : ∀ x : ↥Y, x ∈ (ψ.comp (Subgroup.inclusion hY)).ker ↔ (x : H) ∈ R0 := by
    intro x
    rw [← MonoidHom.comap_ker ψ (Subgroup.inclusion hY), Subgroup.mem_comap]
    simp only [hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hK : (ψ.comp (Subgroup.inclusion hY)).ker = R0.subgroupOf Y := by
    ext x
    exact hmem x
  have hKp : IsPGroup 2 (ψ.comp (Subgroup.inclusion hY)).ker := by
    rw [hK]
    exact hR0.comap_subtype (K := Y)
  haveI hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hmapnormal : ((ψ.comp (Subgroup.inclusion hY)).ker.map f).Normal :=
    (inferInstance : ((ψ.comp (Subgroup.inclusion hY)).ker).Normal).map f hf
  refine le_antisymm ?_ ?_
  ·
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((ψ.comp (Subgroup.inclusion hY)).ker.map f) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff ((ψ.comp (Subgroup.inclusion hY)).ker)).mp hbot
    · exfalso
      have htopP : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) :=
        htop ▸ hKp.map f
      have hp : IsPGroup 2 (alternatingGroup (Fin 5)) := htopP.of_equiv Subgroup.topEquiv
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
      have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      rw [hcard] at hn
      have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn]; norm_num
      have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      exact (by norm_num : ¬ (3 : ℕ) ∣ 2) h32
  ·
    intro x hx
    rw [hmem x]
    have hx' : x ∈ (zpowers z).subgroupOf Y := hfk hx
    rw [Subgroup.mem_subgroupOf] at hx'
    exact hzR0 hx'

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
