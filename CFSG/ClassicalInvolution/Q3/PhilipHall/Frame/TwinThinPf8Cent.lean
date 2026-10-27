module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Basic

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

theorem commutes_of_nbrAdj {J J' : Subgroup G} (h : nbrAdj (CoreAssembly.conjClass K₀) J J') :
    ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  have hJ := h.1
  have hJ' := h.2.1
  have hN := ((mem_omegaNbr_iff S.hs.hyp S.hs.two).mp h.2).2.2
  have hP : IsPGroup 2 ↥(J' ⊔ J : Subgroup G) :=
    (S.hs.two J' hJ').to_sup_of_normal_right' (S.hs.two J hJ) hN
  exact S.commutes_of_le hJ hJ' h.2.2.1.symm hP le_sup_right le_sup_left

theorem fam_of_conj_pi {L : Subgroup G} (hL : L ∈ conjSub g '' π) :
    L ∈ fam K (conjSub g (piGen π)) := by
  have hπg := isMaxOrb_conj S.hos.graph S.hπ g
  obtain ⟨a, ha, haL⟩ := transitive_of_maxOrb S.hos.graph hπg K
    (S.hos.mem_conj_image_of_mem S.hπ S.hg) L hL
  have ha' : a ∈ conjSub g (piGen π) := by
    rw [← piGen_conj]; exact ha
  exact ⟨⟨a, ha'⟩, haL⟩

theorem K_not_mem_pi : K ∉ π := fun h =>
  Set.disjoint_left.mp (S.hos.disjoint_twinSet S.hπ S.hH1)
    (mem_twinSet_self S.hK S.hz) h

theorem K'_not_mem_pi : K' ∉ π := fun h =>
  Set.disjoint_left.mp (S.hos.disjoint_twinSet S.hπ S.hH1) S.hK' h

theorem y_cent_pi {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {y : ↥(pSpan (fam K (conjSub g (piGen π))))} (hyφ : J.φ y = AE.yBar α h)
    (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1) {L : Subgroup G} (hL : L ∈ π)
    (hadj : nbrAdj (CoreAssembly.conjClass K₀) (conjSub g K) L) :
    ∀ l ∈ L, (y : G) * l = l * (y : G) := by
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  obtain ⟨a3, hya3⟩ := hy3
  by_cases hLg : L ∈ conjSub g '' π
  · have hLf := S.fam_of_conj_pi hLg
    obtain ⟨β, hβ, c, hlabL⟩ := J.label L hLf
    have hKL : nbrAdj (CoreAssembly.conjClass K₀) K L := adj_of_mem_isMaxOrb S.hos.graph S.hπ hL
    have hcomm := S.commutes_of_nbrAdj hKL
    have hβα : Disjoint α β := by
      by_cases heq : α = β
      · exfalso
        subst heq
        by_cases hcb : c = b
        · subst hcb
          have hLK : L = K := S.eq_of_map_le hn J hLf S.mem_fam_self
            (le_of_eq (hlabL.trans hlab.symm))
          exact S.K_not_mem_pi (hLK ▸ hL)
        · have hcb' : c = !b := by cases b <;> cases c <;> simp_all
          subst hcb'
          have hLK : L = K' := S.eq_of_map_le hn J hLf S.twin_mem_fam
            (le_of_eq (hlabL.trans (S.map_twin_eq hn hn8 J hlab).symm))
          exact S.K'_not_mem_pi (hLK ▸ hL)
      · refine AE.disjoint_of_zBar_comm (h := h) (h' := hβ) heq (c := c) fun y' hy' => ?_
        rw [← hlabL] at hy'
        obtain ⟨l, hl, rfl⟩ := J.exists_of_mem_map hLf hy'
        have hz := J.map_eq_zBar hn S.mem_fam_self (S.card8 K S.hK) hlab S.hz
        rw [← hz, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm z S.hz.mem l hl)
    intro l hl
    have hmem : J.φ ⟨l, le_pSpan hLf hl⟩ ∈ AE.memBar β hβ c := by
      rw [← hlabL]; exact J.mem_map hLf hl
    have h1 : J.φ y * J.φ ⟨l, le_pSpan hLf hl⟩ = J.φ ⟨l, le_pSpan hLf hl⟩ * J.φ y := by
      rw [hyφ]
      exact AE.yBar_comm_memBar_of_disjoint hβα c _ hmem
    exact congrArg Subtype.val (J.comm_of_pow_three hk hya3 h1)
  · have hβ := S.hos.nbr_diff_subset_beta (isMaxOrb_conj S.hos.graph S.hπ g) hadj hLg
    have hcen := S.hos.beta_le_centralizer hβ
    rw [piGen_conj] at hcen
    intro l hl
    have hyX : (y : G) ∈ conjSub g (piGen π) :=
      (SetLike.ext_iff.mp S.fam_gen (y : G)).mp y.2
    exact Subgroup.mem_centralizer_iff.mp (hcen hl) y hyX

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
