module

public import CFSG.ClassicalInvolution.Q3.Q3TZCount
public import CFSG.ClassicalInvolution.Q3.Q3TIYAtT

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TIV
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)

section Closure

variable {G : Type} [Group G]

theorem eq_top_of_closure3 {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hconn : RouteD.DeltaConnected Ω) {H : Subgroup G} {K J : Subgroup G} (hK : K ∈ Ω)
    (hKH : K ≤ H) (hJH : J ≤ H)
    (hneighK : ∀ L ∈ Ω, L ≠ K → Commutes K L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J)
    (hneighJ : ∀ L ∈ Ω, L ≠ J → Commutes J L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J) : H = ⊤ := by
  obtain ⟨𝔖, h𝔖⟩ : ∃ 𝔖 : Set (Subgroup G), 𝔖 =
      {L | L ∈ Ω ∧ ∃ h ∈ H, L = conjSub h K ∨ L = conjSub h J} := ⟨_, rfl⟩
  have hsub : 𝔖 ⊆ Ω := fun L hL => by
    rw [h𝔖] at hL
    exact hL.1
  have hne : 𝔖.Nonempty := ⟨K, by
    rw [h𝔖]
    exact ⟨hK, 1, H.one_mem, Or.inl (conjSub_one K).symm⟩⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    intro N hN L hL hLN hc
    rw [h𝔖] at hN
    obtain ⟨hNΩ, h, hhH, hNh⟩ := hN
    have hL' : conjSub h⁻¹ L ∈ Ω := hΩ.conjInvariant _ L hL
    have hLeq : L = conjSub h (conjSub h⁻¹ L) := (conjSub_conjSub_inv h L).symm
    rw [h𝔖]
    refine ⟨hL, ?_⟩
    have hcc : Commutes (conjSub h⁻¹ N) (conjSub h⁻¹ L) := (commutes_conjSub_iff h⁻¹).mpr hc
    rcases hNh with hN | hN
    · rw [hN, conjSub_inv_conjSub] at hcc
      have hne' : conjSub h⁻¹ L ≠ K := fun hEq => hLN (by rw [hLeq, hEq, hN])
      obtain ⟨y, hy, hyeq⟩ := hneighK _ hL' hne' hcc
      refine ⟨h * y, H.mul_mem hhH hy, ?_⟩
      rcases hyeq with hyeq | hyeq
      · left
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y K) := by rw [hyeq]
          _ = conjSub (h * y) K := (conjSub_mul h y K).symm
      · right
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y J) := by rw [hyeq]
          _ = conjSub (h * y) J := (conjSub_mul h y J).symm
    · rw [hN, conjSub_inv_conjSub] at hcc
      have hne' : conjSub h⁻¹ L ≠ J := fun hEq => hLN (by rw [hLeq, hEq, hN])
      obtain ⟨y, hy, hyeq⟩ := hneighJ _ hL' hne' hcc
      refine ⟨h * y, H.mul_mem hhH hy, ?_⟩
      rcases hyeq with hyeq | hyeq
      · left
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y K) := by rw [hyeq]
          _ = conjSub (h * y) K := (conjSub_mul h y K).symm
      · right
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y J) := by rw [hyeq]
          _ = conjSub (h * y) J := (conjSub_mul h y J).symm
  have hall := subset_of_adj_closed hconn hsub hne hcl
  have hle : ∀ L ∈ Ω, L ≤ H := by
    intro L hL
    have hLS := hall hL
    rw [h𝔖] at hLS
    obtain ⟨-, h, hhH, hLh⟩ := hLS
    have key : ∀ M : Subgroup G, M ≤ H → conjSub h M ≤ H := by
      intro M hM x hx
      rw [mem_conjSub_iff] at hx
      have h1 := H.mul_mem (H.mul_mem hhH (hM hx)) (H.inv_mem hhH)
      have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rwa [e] at h1
    rcases hLh with hLh | hLh
    · rw [hLh]; exact key K hKH
    · rw [hLh]; exact key J hJH
  refine eq_top_iff.mpr ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun L hL => hle L hL

end Closure

section Layers

variable {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G} {tY : StatedLieTag}
  {nY : ℕ}


theorem eq_top_of_layers3 (hconn : RouteD.DeltaConnected (conjClass3 K))
    (c : TwinLoc3 tY nY (conjClass3 K) z) (hKcls : IsClassicalMember3 K z)
    (hT : IsTwinAt (conjClass3 K) K T z) (hJ : J ∈ centralizingMembers (conjClass3 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T) (A : AtT3 K T J z t tY nY) {H : Subgroup G}
    (hYz : centralizingLayer (conjClass3 K) {z} ≤ H)
    (hYt : centralizingLayer (conjClass3 K) {t} ≤ H) : H = ⊤ := by
  classical
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hKΩ, isSubnormal_le hKcls.subnormal⟩
  have hKH : K ≤ H := (le_centralizingLayer hKz).trans hYz
  have hJH : J ≤ H := (le_centralizingLayer hJ).trans hYz
  have hneighK : ∀ L ∈ conjClass3 K, L ≠ K → Commutes K L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J := by
    intro L hL hLK hcm
    have hLz : L ∈ centralizingMembers (conjClass3 K) {z} :=
      ⟨hL, fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hcm z hKcls.mem l hl).symm⟩
    by_cases hLT : L = T
    · have hLt : L ∈ centralizingMembers (conjClass3 K) {t} := hLT ▸ A.hTt
      have hLJ : L ≠ J := by rw [hLT]; exact hJT.symm
      have hLJ₂ : L ≠ A.J₂ := by rw [hLT]; exact A.hJ₂T.symm
      obtain ⟨y, hy, hyeq⟩ := A.c.link_big A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso
        (L := K) (L' := L) A.hKt hJK.symm A.hJ₂K.symm hLt hLJ hLJ₂
      exact ⟨y, hYt hy, Or.inl hyeq.symm⟩
    · obtain ⟨y, hy, hyeq⟩ := c.link_big hKz hT.mem hT.ne.symm hKiso hTiso (L := J) (L' := L)
        hJ hJK hJT hLz hLK hLT
      exact ⟨y, hYz hy, Or.inr hyeq.symm⟩
  have hneighJ : ∀ L ∈ conjClass3 K, L ≠ J → Commutes J L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J := by
    intro L hL hLJ hcm
    have hLt : L ∈ centralizingMembers (conjClass3 K) {t} :=
      ⟨hL, fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hcm t A.clsJ.mem l hl).symm⟩
    by_cases hLJ₂ : L = A.J₂
    · obtain ⟨y, hy, hyeq⟩ := c.link_big hKz hT.mem hT.ne.symm hKiso hTiso (L := J) (L' := L)
        hJ hJK hJT (hLJ₂ ▸ A.hJ₂z) (by rw [hLJ₂]; exact A.hJ₂K) (by rw [hLJ₂]; exact A.hJ₂T)
      exact ⟨y, hYz hy, Or.inr hyeq.symm⟩
    · obtain ⟨y, hy, hyeq⟩ := A.c.link_big A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso
        (L := K) (L' := L) A.hKt hJK.symm A.hJ₂K.symm hLt hLJ hLJ₂
      exact ⟨y, hYt hy, Or.inl hyeq.symm⟩
  exact eq_top_of_closure3 c.hΩ hconn hKΩ hKH hJH hneighK hneighJ

theorem false_of_normalizes3 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hconn : RouteD.DeltaConnected (conjClass3 K)) (c : TwinLoc3 tY nY (conjClass3 K) z)
    (hKcls : IsClassicalMember3 K z) (hT : IsTwinAt (conjClass3 K) K T z)
    (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (A : AtT3 K T J z t tY nY)
    (h : ∀ N ∈ centralizingMembers (conjClass3 K) {t}, N ≠ J → N ≠ A.J₂ →
      N ≤ normX3 K T z) : False := by
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hJΦ : J ∈ phi3 K T z := ⟨hJ, hJK, hJT⟩
  have hJ₂Φ : A.J₂ ∈ phi3 K T z := ⟨A.hJ₂z, A.hJ₂K, A.hJ₂T⟩
  have hΦX : ∀ N ∈ phi3 K T z, N ≤ normX3 K T z := fun N hN =>
    ((le_iSup₂ (f := fun (N : Subgroup G) (_ : N ∈ phi3 K T z) => N) N hN).trans
      (Subgroup.le_normalizer : xGen3 K T z ≤ normX3 K T z))
  have hYz : centralizingLayer (conjClass3 K) {z} ≤ normX3 K T z := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNK : N = K
    · subst hNK
      exact h _ A.hKt hJK.symm A.hJ₂K.symm
    by_cases hNT : N = T
    · subst hNT
      exact h _ A.hTt hJT.symm A.hJ₂T.symm
    exact hΦX N ⟨hN, hNK, hNT⟩
  have hYt : centralizingLayer (conjClass3 K) {t} ≤ normX3 K T z := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNJ : N = J
    · subst hNJ
      exact hΦX _ hJΦ
    by_cases hNJ₂ : N = A.J₂
    · subst hNJ₂
      exact hΦX _ hJ₂Φ
    exact h N hN hNJ hNJ₂
  have htop := eq_top_of_layers3 hconn c hKcls hT hJ hJK hJT A hYz hYt
  have htop' : Subgroup.normalizer (xGen3 K T z : Set G) = ⊤ := htop
  have hnorm : (xGen3 K T z).Normal := Subgroup.normalizer_eq_top_iff.mp htop'
  have hKX : ∀ N ∈ phi3 K T z, Commutes K N := fun N hN => hT.comm_K N hN.1 hN.2.1
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (xGen3 K T z) with hbot | hX
  · have hJle : J ≤ xGen3 K T z :=
      le_iSup₂ (f := fun (N : Subgroup G) (_ : N ∈ phi3 K T z) => N) J hJΦ
    rw [hbot] at hJle
    have := Subgroup.mem_bot.mp (hJle A.clsJ.mem)
    exact A.clsJ.ne_one this
  · have hKc : K ≤ Subgroup.center G := by
      intro k hk
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ xGen3 K T z := by rw [hX]; trivial
      have hXle : xGen3 K T z ≤ Subgroup.centralizer (K : Set G) := by
        refine iSup₂_le fun N hN => ?_
        intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro k' hk'
        exact hKX N hN k' hk' n hn
      have := Subgroup.mem_centralizer_iff.mp (hXle hg) k hk
      exact this.symm
    rw [hcen] at hKc
    have := Subgroup.mem_bot.mp (hKc hKcls.mem)
    exact hKcls.ne_one this

end Layers

end CFSG.ClassicalInvolution.Q3.Q3TZ
