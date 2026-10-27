module

public import CFSG.GroupTheory.PLayer.Permuted
public import CFSG.LocalAnalysis.GLTheoremA.S12.Diag
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts3
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common

public section

namespace CFSG

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.GLTheoremA.S12 CFSG.Yardstones.Md0ec50421ce4

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem fixedBar_zpowers_eq_fixedSub {X : Subgroup G} {x : G} (hp : p.Prime)
    (hxp : orderOf x = p) (hxN : x ∈ Subgroup.normalizer (X : Set G)) :
    fixedBar p X (Subgroup.zpowers x) =
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub
        (barAut p X ⟨x, hxN⟩) := by
  have hxp' : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  ext z
  constructor
  · intro hz
    exact hz ⟨x, hxN⟩ (Subgroup.mem_zpowers x)
  · intro hz f hf
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hf
    obtain ⟨n, hn⟩ := idiag_zpow_nat hp.pos hxp' k
    have hf' : f = (⟨x, hxN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ n := by
      apply Subtype.ext
      show (f : G) = x ^ n
      rw [← hk, hn]
    have hpow : ∀ n : ℕ, ((barAut p X ⟨x, hxN⟩ : MulAut (PQuot p X)) ^ n) z = z := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply,
          show ((barAut p X) ⟨x, hxN⟩) z = z from hz, ih]
    rw [hf', map_pow]
    exact hpow n

theorem hasPermutedFixedComponent_of_conj_ne {X J : Subgroup G} {x : G}
    (hp : p.Prime) (hJ : GLAPComponent p X J) (hxp : orderOf x = p)
    (hxN : x ∈ Subgroup.normalizer (X : Set G))
    (hJx : J.map (MulAut.conj x).toMonoidHom ≠ J) :
    HasPermutedFixedComponent p X x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp' : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  let Y : Subgroup G := X ⊔ Subgroup.zpowers x
  have hXY : X ≤ Y := le_sup_left
  have hxY : x ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hYnorm : Y ≤ Subgroup.normalizer (X : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact Subgroup.zpowers_le.2 hxN
  have hXnormal : (X.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).2 hYnorm
  have hJY : GLAPComponent p Y J :=
    CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp hXY hXnormal hJ
  have hxM : x ∉ Subgroup.normalizer (J : Set G) := fun h =>
    hJx (Subgroup.mem_normalizer_iff_map_conj_eq.mp h)
  obtain ⟨P, hP⟩ := diag_pcomp_exists hp hJY hxY hxp' hxM
  let CX : Subgroup G := X ⊓ Subgroup.centralizer ({x} : Set G)
  have hJstar_sn : IsSubnormal (closureIn J (Subgroup.zpowers x)) X := by
    let 𝓛 : Set (Subgroup G) := {L : Subgroup G | ∃ g ∈ Subgroup.zpowers x, L = GLBConj g J}
    have hcomp : ∀ L ∈ 𝓛, GLAPComponent p X L := by
      rintro L ⟨g, hg, rfl⟩
      have hgN : g ∈ Subgroup.normalizer (X : Set G) := (Subgroup.zpowers_le.2 hxN) hg
      have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ g
      rwa [gLBConj_eq_of_mem_normalizer hgN] at h
    have hJstar_eq : closureIn J (Subgroup.zpowers x) = sSup 𝓛 := by
      rw [closureIn_eq_iSup_gLBConj, sSup_eq_iSup]
      refine le_antisymm ?_ ?_
      · refine iSup₂_le fun g hg => ?_
        exact le_iSup₂_of_le (GLBConj g J) ⟨g, hg, rfl⟩ le_rfl
      · refine iSup₂_le fun L hL => ?_
        obtain ⟨g, hg, rfl⟩ := hL
        exact le_iSup₂_of_le g hg le_rfl
    have := CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp 𝓛 hcomp
    rwa [← hJstar_eq] at this
  have hA_sn : IsSubnormal (closureIn J (Subgroup.zpowers x) ⊓
      Subgroup.centralizer ({x} : Set G)) CX := hJstar_sn.inf _
  have hP_CX : GLAPComponent p CX P :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest.glaPComponent_of_isSubnormal hp hA_sn hP
  have hP_sub : GLAPComponent p (CX.subgroupOf X) (P.subgroupOf X) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp inf_le_left hP_CX
  let ψ : ↥X →* PQuot p X := QuotientGroup.mk' (GLAPPrimeCore p ↥X)
  have hker : Nat.Coprime p (Nat.card ↥((CX.subgroupOf X) ⊓ ψ.ker)) := by
    have hle : (CX.subgroupOf X) ⊓ ψ.ker ≤ ψ.ker := inf_le_right
    have hcop : Nat.Coprime p (Nat.card ↥ψ.ker) := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.pPrimeCore_coprime_card
    exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
  have hQ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp ψ hker hP_sub
  have himg : (CX.subgroupOf X).map ψ = fixedBar p X (Subgroup.zpowers x) := by
    rw [fixedBar_zpowers_eq_fixedSub hp hxp hxN,
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts3.fixedSub_barAut_eq_p hp hxp' hxN]
    rfl
  exact ⟨(P.subgroupOf X).map ψ, by rwa [himg] at hQ⟩

theorem glaPLayer_inf_centralizer_ne_bot_of_conj_ne {X J : Subgroup G} {x : G}
    (hp : p.Prime) (hJ : GLAPComponent p X J) (hxp : orderOf x = p)
    (hxN : x ∈ Subgroup.normalizer (X : Set G))
    (hJx : J.map (MulAut.conj x).toMonoidHom ≠ J) :
    GLAPLayer p (X ⊓ Subgroup.centralizer ({x} : Set G)) ≠ ⊥ := by
  have hxp' : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  exact glaPLayer_inf_centralizer_ne_bot_of_permuted hp hxp' hxN
    (hasPermutedFixedComponent_of_conj_ne hp hJ hxp hxN hJx)

end CFSG

end
