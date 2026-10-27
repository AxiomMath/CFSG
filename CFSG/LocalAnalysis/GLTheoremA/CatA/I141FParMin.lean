module

public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FPar

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

private lemma barMap_mem_barX {p : ℕ} {X J N : Subgroup G} (hNJ : N ≤ J) (hJX : J ≤ X)
    {n : ↥J} (hn : n ∈ N.subgroupOf J) :
    ((barMap p hJX n : ↥(barX p X J)) : ↥X ⧸ GLAPPrimeCore p ↥X) ∈ barX p X N := by
  refine Subgroup.mem_map.2 ⟨Subgroup.inclusion hJX n, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hn)

theorem eq_of_normal_of_coprime_relIndex {p : ℕ} (hp : p.Prime) {X J N : Subgroup G}
    (hJ : GLAPComponent p X J) (hNJ : N ≤ J) (hNn : (N.subgroupOf J).Normal)
    (hcop : Nat.Coprime p (N.relIndex J)) : N = J := by
  obtain ⟨hJX, hsnJ, hcompJ, hmin⟩ := hJ
  have hsnN : IsSubnormal N X := IsSubnormal.step hNJ hNn hsnJ
  let Kb : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := barX p X J
  let Nb : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := barX p X N
  have hNbK : Nb ≤ Kb := by
    change (N.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ≤
      (J.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hNJ)
  by_cases hEq : Nb = Kb
  ·
    exact (eq_or_lt_of_le hNJ).resolve_right fun hlt => hmin N hlt hsnN hEq
  ·
    let f : ↥J →* ↥Kb := barMap p hJX
    have hf : Function.Surjective f := barMap_surjective hJX
    let M : Subgroup ↥Kb := (N.subgroupOf J).map f
    have hMnorm : M.Normal := hNn.map f hf
    have hMle : M ≤ Nb.subgroupOf Kb := by
      rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.2 (barMap_mem_barX hNJ hJX hn)
    have hMge : Nb.subgroupOf Kb ≤ M := by
      intro x hx
      have hxNb : (x : ↥X ⧸ GLAPPrimeCore p ↥X) ∈ Nb := Subgroup.mem_subgroupOf.1 hx
      change (x : ↥X ⧸ GLAPPrimeCore p ↥X) ∈ (N.subgroupOf X).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) at hxNb
      obtain ⟨xX, hxN, hxq⟩ := Subgroup.mem_map.1 hxNb
      have hxNJ : (xX : G) ∈ N := Subgroup.mem_subgroupOf.1 hxN
      let nJ : ↥J := ⟨(xX : G), hNJ hxNJ⟩
      have hnJ : nJ ∈ N.subgroupOf J := Subgroup.mem_subgroupOf.2 hxNJ
      refine Subgroup.mem_map.2 ⟨nJ, hnJ, ?_⟩
      ext
      have hincl : Subgroup.inclusion hJX nJ = xX := Subtype.ext rfl
      calc
        ((f nJ : ↥Kb) : ↥X ⧸ GLAPPrimeCore p ↥X)
            = QuotientGroup.mk' (GLAPPrimeCore p ↥X) (Subgroup.inclusion hJX nJ) := rfl
        _ = QuotientGroup.mk' (GLAPPrimeCore p ↥X) xX := by rw [hincl]
        _ = (x : ↥X ⧸ GLAPPrimeCore p ↥X) := hxq
    have hMeq : M = Nb.subgroupOf Kb := le_antisymm hMle hMge
    have hMne : M ≠ ⊤ := by
      intro htop
      have hsub : Nb.subgroupOf Kb = ⊤ := by rw [← hMeq, htop]
      exact hEq (le_antisymm hNbK (Subgroup.subgroupOf_eq_top.mp hsub))
    have hQ : CFSG.Open.IsQuasisimple ↥Kb := hcompJ.2.2
    have hcore : CFSG.pPrimeCore p ↥Kb = ⊥ := by
      have hq : CFSG.pPrimeCore p (↥J ⧸ GLAPPrimeCore p ↥J) = ⊥ :=
        CFSG.pPrimeCore_quotient_eq_bot hp
      have e : (↥J ⧸ GLAPPrimeCore p ↥J) ≃* ↥Kb := quotEquivBarX hp hJX hsnJ
      have hmap := CFSG.pPrimeCore_map_iso p e
      rw [hq, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hMZ : M ≤ Subgroup.center ↥Kb :=
      le_center_of_normal_of_isQuasisimple hQ hMnorm hMne
    haveI : Fact p.Prime := ⟨hp⟩
    have hpdvd : p ∣ (Subgroup.center ↥Kb).index := by
      rw [Subgroup.index_eq_card]
      exact CFSG.LocalAnalysis.GLTheoremA.I142.dvd_card_center_quot_of_pPrimeCore_eq_bot
        hQ hcore
    have hdvd1 : (Subgroup.center ↥Kb).index ∣ M.index := Subgroup.index_dvd_of_le hMZ
    have hle : N.subgroupOf J ≤ M.comap f := fun x hx => Subgroup.mem_map_of_mem f hx
    have hdvd2 : M.index ∣ (N.subgroupOf J).index := by
      have h := Subgroup.index_dvd_of_le hle
      rwa [Subgroup.index_comap_of_surjective M hf] at h
    have hpdvdNJ : p ∣ N.relIndex J := by
      change p ∣ (N.subgroupOf J).index
      exact hpdvd.trans (hdvd1.trans hdvd2)
    exfalso
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpdvdNJ

end CFSG.LocalAnalysis.GLTheoremA.I141FPar

end
