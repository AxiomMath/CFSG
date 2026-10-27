module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinHyps

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem hOdd : classicalInvolutionOddCore ↥(pSpan (fam K (conjSub g (piGen π)))) = ⊥ := by
  rw [S.fam_gen]; exact S.hO

theorem fam_mem {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) :
    L ∈ CoreAssembly.conjClass K₀ := fam_subset S.hos.graph S.hK hL

theorem commutes_of_le {J J' P : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K₀)
    (hJ' : J' ∈ CoreAssembly.conjClass K₀) (hne : J ≠ J') (hP : IsPGroup 2 P) (hJP : J ≤ P)
    (hJ'P : J' ≤ P) : ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  exact Q3CP.l67Gen G (CoreAssembly.conjClass K₀) S.hs.hyp T J
    (mem_RSet_of_isPGroup hJ (S.hs.two J hJ)) J' (mem_RSet_of_isPGroup hJ' (S.hs.two J' hJ'))
    (hJP.trans hPT) (hJ'P.trans hPT) hne

theorem eq_of_map_le {n : ℕ} (hn : 5 ≤ n) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ fam K (conjSub g (piGen π)))
    (h₂ : L₂ ∈ fam K (conjSub g (piGen π)))
    (hle : (L₁.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ≤
      (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ) : L₁ = L₂ := by
  by_contra hne
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  have hS2 : IsPGroup 2 ((L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ) :=
    ((S.hs.two L₂ (S.fam_mem h₂)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (le_pSpan h₂)).symm).map _
  have hQ2 : IsPGroup 2 (((((L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map
      J.φ)).comap J.φ).map (pSpan (fam K (conjSub g (piGen π)))).subtype) :=
    (hS2.comap_of_ker_isPGroup J.φ hk).map _
  have hLQ : ∀ {L : Subgroup G}, L ∈ fam K (conjSub g (piGen π)) →
      (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ≤
        (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ →
      L ≤ ((((L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ)).comap
        J.φ).map (pSpan (fam K (conjSub g (piGen π)))).subtype := by
    intro L hL hLS l hl
    exact ⟨⟨l, le_pSpan hL hl⟩, hLS (J.mem_map hL hl), rfl⟩
  have hc := S.commutes_of_le (S.fam_mem h₁) (S.fam_mem h₂) hne hQ2 (hLQ h₁ hle) (hLQ h₂ le_rfl)
  obtain ⟨α, h, b, hlab⟩ := J.label L₁ h₁
  obtain ⟨x, hx, x', hx', hxx'⟩ := AE.exists_not_comm_memBar hn α h b
  rw [← hlab] at hx hx'
  obtain ⟨l, hl, rfl⟩ := J.exists_of_mem_map h₁ hx
  obtain ⟨l', hl', hl'e⟩ := J.exists_of_mem_map h₂ (hle hx')
  apply hxx'
  rw [← hl'e, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl l' hl')

theorem map_twin_eq {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) n) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h (!b) := by
  obtain ⟨α', h', b', hlab'⟩ := J.label K' S.twin_mem_fam
  obtain ⟨-, z', hz'K, hz'K'⟩ := S.hK'
  have hzz : z' = z := (S.hz.eq hz'K).symm
  rw [hzz] at hz'K'
  have e1 := J.map_eq_zBar hn S.mem_fam_self (S.card8 K S.hK) hlab S.hz
  have e2 := J.map_eq_zBar hn S.twin_mem_fam (S.card8 K' S.hK'.1) hlab' hz'K'
  have hαα : α = α' := AE.eq_of_zBar_eq hn8 (e1.symm.trans e2)
  subst hαα
  have hb : b' = !b := by
    by_contra hb
    have hbb : b' = b := by cases b <;> cases b' <;> simp_all
    subst hbb
    exact S.hne (S.eq_of_map_le hn J S.twin_mem_fam S.mem_fam_self
      (le_of_eq (hlab'.trans hlab.symm)))
  rw [hlab', hb]

theorem exists_y {n : ℕ} (hn : 5 ≤ n) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    ∃ y : ↥(pSpan (fam K (conjSub g (piGen π)))), J.φ y = AE.yBar α h ∧ (∃ a : ℕ, y ^ 3 ^ a = 1) ∧
      (y : G) * z = z * (y : G) ∧ (y : G) ∈ Subgroup.normalizer (piGen π : Set G) := by
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  have hmem : AE.yBar α h ∈ J.φ.range := by
    rw [J.range_eq]; exact AE.yBar_mem α h
  obtain ⟨y, hyφ, a, hya⟩ := J.exists_lift_pow_three hmem (AE.yBar_pow_three α h)
  have hz := J.map_eq_zBar hn S.mem_fam_self (S.card8 K S.hK) hlab S.hz
  have hcomm : J.φ y * J.φ ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ =
      J.φ ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ * J.φ y := by
    rw [hyφ, hz]; exact AE.yBar_comm_zBar α h
  have hyz := J.comm_of_pow_three hk hya hcomm
  have hyz' : (y : G) * z = z * (y : G) := congrArg Subtype.val hyz
  refine ⟨y, hyφ, ⟨a, hya⟩, hyz', ?_⟩
  exact S.hos.centralizer_le_normalizer_piGen S.hK S.hπ S.hH1 S.hz
    (Subgroup.mem_centralizer_singleton_iff.mpr hyz')

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
