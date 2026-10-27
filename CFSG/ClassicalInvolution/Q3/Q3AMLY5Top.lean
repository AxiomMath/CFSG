module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Stmt
public import CFSG.ClassicalInvolution.Q3.Q3AMTriLY

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section Assembly


theorem cfby_of_leaves (L : CFBYLeaves) : CFBY := by
  intro G _ _ _ Ω K J S R T W z t hbad hint hN hth hE
  have hset : E4SettingY Ω K J S R T W z t := ⟨hbad, hint, hN, hth, hE⟩
  obtain ⟨s, hs⟩ := L.axis G Ω K J S R T W z t hset
  have hsec := L.sect G Ω K J S R T W z t hset
  have vz := L.vertexZ G Ω K J S R T W z t hset s hs
  have vt := L.vertexT G Ω K J S R T W z t hset hsec s hs
  have va := L.vertexA G Ω K J S R T W z t hset hsec s hs
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hne : z ≠ t := fun e => by
    have : IsUniqueInvolution J z := e ▸ hstd.ht
    exact hstd.hJ.2.1 (hnt K hstd.stand.mem J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have helem := T8T.isElemAbelian_closure_three hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t
  have hcard := T8T.natCard_closure_three hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t
    hstd.hz.ne_one hstd.ht.ne_one hne hs.ne_one hs.indep
  have hvert : ∀ c ∈ Subgroup.closure ({z, t, s} : Set G), c ≠ 1 →
      Hyp51At (Subgroup.closure ({z, t, s} : Set G)) c := by
    intro c hc hc1
    rcases T8T.mem_closure_three_involutions hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t hc with
      h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · rw [h]; exact vz
    · rw [h]; exact vt.1
    · rw [h]; exact vt.2.1
    · rw [h]; exact va.1
    · rw [h]; exact va.2.1
    · rw [h]; exact vt.2.2
    · rw [h]; exact va.2.2
  have hB : Hyp51 (Subgroup.closure ({z, t, s} : Set G)) := ⟨helem, hcard, hvert⟩
  have hzt_le : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, s} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  exact hbad.false_of_linkAxis
    ⟨hzt_le, lemma52 G _ hB, L.link G Ω K J S R T W z t hset hsec s hs⟩

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3AM
