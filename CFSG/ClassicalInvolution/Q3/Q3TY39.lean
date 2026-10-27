module

public import CFSG.ClassicalInvolution.Q3.Q3TY38
public import CFSG.ClassicalInvolution.Q3.Q3TY33
public import CFSG.ClassicalInvolution.Q3.Q3TY21
public import CFSG.ClassicalInvolution.Q3.Q3TY30
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups commutatorElement

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem PartnerPatternMinus3.of_fixed_member_ge3 (hMFZ : Gaps.FundNoncentral 3) {u : ℕ}
    (c : Q3TC.TCtx3 .POmegaMinus (u + 3 + 5) Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G}
    (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfix : HasFixedMember Ω K β z) : PartnerPatternMinus3 (u + 3 + 5) Ω K β t := by
  classical
  have hΩ := c.hΩ
  have htz : t * z * t⁻¹ = z := by
    obtain ⟨W, hW⟩ := hKβ
    have hzt : Commute z t := standardPair_involutions_commute two_ne_zero_gf3 hW c.hz.mem ht.mem
      c.hz.orderOf_eq_two ht.orderOf_eq_two
    rw [mul_inv_eq_iff_eq_mul]
    exact hzt.symm.eq
  obtain ⟨M, hMΩ, hKM, hβM, hMnot⟩ := hfix
  have hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra hcon
    push Not at hcon
    exact hMnot hcon
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_minus3 (by omega) c hsingle hβ ht hKβ hMΩ hKM hβM
  obtain ⟨x, hx2, hxfix⟩ := minus_fixed_of_nodes_ge3_3 hMFZ c hsingle D ht htz hKβ hMΩ hMN nd h0
    h1
  obtain ⟨j, hjK, hjY, hjΩ, hjperf, hjc, hjp, hjtw, hjimg⟩ :=
    c.exists_nodes_typeTwistedD3_img (m := u + 3 + 5) (by omega)
      (spinMinus6Generated_galois (p := 3) (f := 1) (by norm_num))
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y₀ : G) ∈ locLayer Ω z := y₀.2
  have hyz : (y₀ : G) * z * (y₀ : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have himg : ∀ a : Fin (u + 3 + 5 - 1), locImg Ω z (conjSub (y₀ : G) (j a)) =
      ((rankOne (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)).rootGroup a).map
        (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    intro a
    rw [locImg_conjSub_layer, hjimg a, show locMk Ω z y₀ = c.d.ψ x from hy₀]
    exact map_conj_map_hom c.d.ψ x _
  refine PartnerPatternMinus3.of_locAut c hjK hjY (fun a ha => (hjΩ a ha).1) hjperf hjc hjp hjtw
    hy htz (fun a ha w hw => ?_) (fun a ha => ?_)
  · rw [himg a] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact hxfix a ha r hr
  ·
    obtain ⟨a', ha'⟩ := a
    have ha0 : a' = 0 := ha
    subst ha0
    have hmemy : conjSub (y₀ : G) (j ⟨0, by omega⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y₀ : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by omega⟩, mem_centralizingMembers_of_commutes (hjΩ _ (by simp)).1.1
        c.hz.mem (commutes_symm (hjK _)), rfl⟩
    have hK2 : Commutes K (nd.J ⟨2, by omega⟩) := by
      rw [← h0]
      exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp)) (by fr_idx)
    have hJ2 : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {z} :=
      mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm hK2)
    have heq : conjSub (y₀ : G) (j ⟨0, by omega⟩) = nd.J ⟨2, by omega⟩ :=
      c.eq_of_locImg_eq hmemy hJ2 (by rw [himg, hx2])
    rw [heq]
    obtain ⟨W, hW⟩ := nd.pair_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by fr_idx)
    rw [h1] at hW
    exact ⟨W, hW⟩

end Main

section Stmt

theorem partnerPatternStmt3_ge8 (h3 : OddThreeFreeInput) {m : ℕ} (hm : 8 ≤ m) :
    PartnerPatternStmt3 m := by
  obtain ⟨u, rfl⟩ : ∃ u, m = u + 3 + 5 := ⟨m - 8, by omega⟩
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  have hadm : StatedLieAdmissible .POmegaMinus (u + 3 + 5) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ u + 3 + 5; omega⟩
  obtain ⟨c⟩ := Q3TC.nonempty_tctx3 (yData3_minus (by omega) hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨ι, -, D, -, -⟩ := id hshape
  exact PartnerPatternMinus3.of_fixed_member_ge3 (Gaps.fundNoncentral 3) c hsingle D hβ ht hKβ
    hfix

end Stmt

end CFSG.ClassicalInvolution.Q3.Q3TY
