module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Main
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddFull
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs61
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (LieQConstrained)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ (lieQConstrained_odd)

theorem i196_of_facts
    (G : Type) [Group G] [Finite G] (p : ℕ)
    (hF1 : I196OuterFix p) (hF2 : I196OuterCore p) (hC1 : I196ChevOfChar p)
    (hC2 : I196ChevCard p) :
    I196At G p := by
  intro hp hp2 X J B _hX hJ hchev hB
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hL : LieQConstrained p := lieQConstrained_odd hp hp2
  have hcases := isChevCases_innerAut hp hp2 hK hchev hC1.1
  have hLQ : ∀ {H : Subgroup (MulAut (PQuot p J))}, innerAut (PQuot p J) ≤ H →
      H196LQ p H (innerAut (PQuot p J)) :=
    fun hH => h196LQ_innerAut hL (hC1.2 hp hp2) hK hcases hH
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => isElemAbelian_commute hB hx hy
  have hkey : ∀ x ∈ autBar p B J, ∀ y ∈ autBar p B J, x * y = y * x := by
    intro x hx y hy
    obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 hx
    obtain ⟨γ', hγ', hγy⟩ := Subgroup.mem_map.1 hy
    have hγB : (γ : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
    have hγ'B : (γ' : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ')).1
    have hcomm : γ * γ' = γ' * γ := Subtype.ext (hBc _ hγB _ hγ'B)
    rw [← hγx, ← hγy, ← map_mul, hcomm, map_mul]
  have hA : IsElemAbelian p (autBar p B J) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hkey a a.2 b b.2)⟩⟩, ?_⟩
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 hx
    have hγB : (γ : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
    have hpow : γ ^ p = 1 := Subtype.ext (by simpa using hB.2 _ hγB)
    rw [← hγx, ← map_pow, hpow, map_one]
  by_cases hcore : IsCompCoreFreeLocalType p B J
  · exact Or.inl hcore
  · right
    unfold IsCompCoreFreeLocalType IsCoreFreeLocalType at hcore
    push Not at hcore
    obtain ⟨D, hDA, H, hH, hDN, hne⟩ := hcore
    have hDel : IsElemAbelian p D := isElemAbelian_mono hA hDA
    have hch : IsChevSimple p (PQuot p J ⧸ Subgroup.center (PQuot p J)) := hchev
    rcases h196_main hLQ hp2 hK hch hF1 hF2 hC2 hH hDel hDN with h | ⟨hD1, hDI, hp3, hcat⟩
    · exact absurd h hne
    · subst hp3
      refine ⟨rfl, hcat, ?_⟩
      obtain ⟨a, haD, haI⟩ : ∃ a ∈ D, a ∉ innerAut (PQuot 3 J) := by
        by_contra hcon
        push Not at hcon
        apply hD1
        rw [eq_bot_iff]
        intro d hd
        have hdI : d ∈ innerAut (PQuot 3 J) := hcon d hd
        have hmem : d ∈ D ⊓ innerAut (PQuot 3 J) := Subgroup.mem_inf.2 ⟨hd, hdI⟩
        rw [hDI] at hmem
        exact hmem
      obtain ⟨γ, hγ, hγa⟩ := Subgroup.mem_map.1 (hDA haD)
      refine ⟨(γ : G), Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ), ?_⟩
      intro hind
      apply haI
      rw [← hγa]
      exact (CFSG.LocalAnalysis.GLTheoremA.inducesInnerMod_iff_barAut_mem_inner γ.2).1 hind

end CFSG.LocalAnalysis.GLTheoremA
