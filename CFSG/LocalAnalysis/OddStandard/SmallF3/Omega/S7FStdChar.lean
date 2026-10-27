module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Defs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.GS82PumpInputs (OddLieCharUnique)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Open (StatedLieTag)

variable {G : Type} [Group G]

theorem s7f_lieModel_center_of_simple [Finite G] {L : Subgroup G} (hY : IsQuasisimple ↥L)
    {τ : StatedLieTag} {n : ℕ} (h : LieModel (↥L ⧸ oddCore ↥L) τ n 3 1) (hn : n ≠ 0) :
    LieModel (↥L ⧸ center ↥L) τ n 3 1 := by
  have hs : IsSimpleGroup (↥L ⧸ oddCore ↥L) :=
    (CFSG.LieType.Simplicity.fam_classical_converse (↥L ⧸ oddCore ↥L)
      ⟨τ, n, 3, 1, h.statedClassicalModel_of_ne_zero hn⟩).2.2
  exact LieModel.of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (center_eq_oddCore_of_simple hY hs)).symm h

theorem s7f_lieModel_center_of_twoU43 [Finite G] {L : Subgroup G} (hY : IsQuasisimple ↥L)
    (h : IsTwoU43 (↥L ⧸ oddCore ↥L)) : LieModel (↥L ⧸ center ↥L) .PSU 4 3 1 := by
  have hne : oddCore ↥L ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥L ⧸ oddCore ↥L) := (QuotientGroup.subsingleton_iff).mpr htop
    haveI : Finite (↥L ⧸ oddCore ↥L) := inferInstance
    have h1 : Nat.card (center (↥L ⧸ oddCore ↥L)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    have h2 : Nat.card (center (↥L ⧸ oddCore ↥L)) = 2 := h.1
    omega
  let N : Subgroup ↥L := oddCore ↥L
  haveI : N.Normal := oddCore_normal ↥L
  let q : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N
  have hle : N ≤ center ↥L := oddCore_le_center_of_isQuasisimple hY hne
  haveI : Group.IsPerfect ↥L := hY.1
  have hcenter : (center ↥L).map q = center (↥L ⧸ N) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel q
      (QuotientGroup.mk'_surjective N)
      (by rw [show q.ker = N from QuotientGroup.ker_mk' N]; exact hle)
  have e1 : (↥L ⧸ N) ⧸ (center ↥L).map q ≃* ↥L ⧸ center ↥L :=
    QuotientGroup.quotientQuotientEquivQuotient N (center ↥L) hle
  have e2 : (↥L ⧸ N) ⧸ (center ↥L).map q ≃* (↥L ⧸ N) ⧸ center (↥L ⧸ N) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  exact LieModel.of_mulEquiv (e2.symm.trans e1) h.2

theorem s7f_lieModel_center_of_inF [Finite G] {L : Subgroup G} (hL : InF L) :
    ∃ (τ : StatedLieTag) (n f : ℕ), LieModel (↥L ⧸ center ↥L) τ n 3 f := by
  obtain ⟨hY, hQ | hQ⟩ := hL
  · rcases hQ with h | h | h | h | h | h <;>
      exact ⟨_, _, _, s7f_lieModel_center_of_simple hY h (by norm_num)⟩
  · exact ⟨_, _, _, s7f_lieModel_center_of_twoU43 hY hQ⟩

theorem s7f_center_eq_bot [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (mem_center_iff.mp (h ▸ mem_top a : a ∈ center G) b).symm hab

theorem s7f_orderOf_conj (hc : center G = ⊥) {s : G} (hs : orderOf s = 2) :
    orderOf (MulAut.conj s) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  refine orderOf_eq_prime (by rw [← map_pow, hs2, map_one]) ?_
  intro h1
  have hmem : s ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : s * g * s⁻¹ = g := by
      have := congrArg (fun φ : MulAut G => φ g) h1
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc g * s = s * g * s⁻¹ * s := by rw [hg]
      _ = s * g := by group
  rw [hc, mem_bot] at hmem
  rw [hmem, orderOf_one] at hs
  exact absurd hs (by norm_num)

theorem s7f_chev3_of_oddLieType (hGLS : GLS3OddLieAutComponentsInput) (hC : OddLieCharUnique)
    [Finite G] [IsSimpleGroup G] (hLC : ∃ L : Subgroup G, InF L ∧ InC L) (ho : OddLieType G) :
    Chev3 G := by
  obtain ⟨L, hLF, s, hs, hLs⟩ := hLC
  obtain ⟨τ0, n0, f0, hY0⟩ := s7f_lieModel_center_of_inF hLF
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := ho
  have hc : center G = ⊥ := s7f_center_eq_bot (s7f_nonab_of_quasisimple hLF.1)
  have hfix : fixedSubgroup (MulAut.conj s) = centralizer ({s} : Set G) :=
    CFSG.Sporadic.HeldB.fixedSubgroup_conj s
  have hcomp : IsComponent (L.subgroupOf (fixedSubgroup (MulAut.conj s))) := by
    rw [hfix]
    exact hLs.2
  have hLle : L ≤ fixedSubgroup (MulAut.conj s) := by
    rw [hfix]
    exact hLs.1
  have e : ↥(L.subgroupOf (fixedSubgroup (MulAut.conj s))) ⧸
      center ↥(L.subgroupOf (fixedSubgroup (MulAut.conj s))) ≃* ↥L ⧸ center ↥L :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLle) (map_center_eq _)
  have hp3 : p = 3 := by
    rcases hGLS G t n p f hp hp2 hadm hm (MulAut.conj s) (s7f_orderOf_conj hc hs) _ hcomp with
      ⟨τ', n', f', -, hm'⟩ | ⟨h3, -⟩
    · exact hC _ τ' n' p f' τ0 n0 3 f0 hp2 (by norm_num) (LieModel.of_mulEquiv e hm') hY0
    · exact h3
  subst hp3
  exact ⟨t, n, f, hadm, hm⟩

end CFSG.OddStandard.SmallF3.Omega
