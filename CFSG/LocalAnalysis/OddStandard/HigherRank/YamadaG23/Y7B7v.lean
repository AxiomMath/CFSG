module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7r

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_quotModIso (c : Ctx7 G L) (hb : B5Std c) :
    QuotModIso (normIn c.s.H c.s.fr.B) (M7 c.s) (c.s.fr.B ⊔ M3 c.s) c.s.fr.B c.s.fr.F := by
  have hM7X7 : M7 c.s ≤ X7 c.s := (y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb)
  haveI hNM : ((M3 c.s).subgroupOf (y7bBM c.s)).Normal := y7b_M3_normal_BM c hb
  haveI hFN : (c.s.fr.F.subgroupOf c.s.fr.B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (y54_F_le_B hb.hH)]
    intro h k hh hk
    rw [← y7b_B_inf_M3 c hb, Subgroup.mem_inf] at hh ⊢
    exact ⟨c.s.fr.B.mul_mem (c.s.fr.B.mul_mem hk hh.1) (c.s.fr.B.inv_mem hk),
      (Subgroup.mem_normalizer_iff.mp (y7b_B_le_NM3 c hb hk) h).mp hh.2⟩
  obtain ⟨θ, hθ1, hθ2⟩ := y7b_exists_theta c hb
  obtain ⟨ι, hι⟩ := y7b_quotEquiv_sup (B := c.s.fr.B) (M := M3 c.s) (F := c.s.fr.F)
    (y7b_B_le_NM3 c hb) (y7b_B_inf_M3 c hb)
  let f : ↥(M7 c.s) →* ↥c.s.fr.B ⧸ c.s.fr.F.subgroupOf c.s.fr.B :=
    ι.symm.toMonoidHom.comp (θ.comp (Subgroup.inclusion hM7X7))
  have hfw : ∀ w : ↥(M7 c.s), f w = ι.symm (θ (Subgroup.inclusion hM7X7 w)) := fun _ => rfl
  refine y7a_quotModIso_of f ?_ ?_ ?_
  · intro z
    refine QuotientGroup.induction_on z ?_
    intro b
    have hbBM : (b : G) ∈ y7bBM c.s := Subgroup.mem_sup_left b.2
    obtain ⟨y, hyM7, hymem⟩ := y7b_theta_onto_M7 c hb (b : G) hbBM
    refine ⟨⟨y, hyM7⟩, ?_⟩
    have hθ : θ (Subgroup.inclusion hM7X7 ⟨y, hyM7⟩) =
        QuotientGroup.mk (⟨(b : G), hbBM⟩ : ↥(y7bBM c.s)) :=
      (hθ1 (Subgroup.inclusion hM7X7 ⟨y, hyM7⟩) ⟨(b : G), hbBM⟩).mpr hymem
    rw [hfw, hθ, ← hι b, MulEquiv.symm_apply_apply]
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hfw, MulEquiv.map_eq_one_iff]
    have hθy : θ (Subgroup.inclusion hM7X7 w) = 1 ↔ ⁅(w : G), c.s.t⁆ ∈ M3 c.s := by
      rw [← QuotientGroup.mk_one (G := ↥(y7bBM c.s))
        (N := (M3 c.s).subgroupOf (y7bBM c.s)), hθ1]
      simp
    rw [hθy, ← y7b_X0_iff c hb (hM7X7 w.2)]
    constructor
    · intro hwX0
      have hwW : (w : G) ∈ y7bW c.s := by
        rw [← y7b_C7_inf_X0 c hb]
        exact Subgroup.mem_inf.mpr ⟨y7b_M7_le_C7 c hb w.2, hwX0⟩
      have hw' : (w : G) ∈ M7 c.s ⊓ y7bW c.s := Subgroup.mem_inf.mpr ⟨w.2, hwW⟩
      rwa [y7b_M7_inf_W c hb] at hw'
    · intro hwBM
      exact y7b_W_le_X0 c hb (y7b_BM_le_W c hb hwBM)
  · intro n hn w w' hw q q' hq h
    have hwG : (Subgroup.inclusion hM7X7 w' : G) =
        n * (Subgroup.inclusion hM7X7 w : G) * n⁻¹ := by
      simpa only [Subgroup.coe_inclusion] using hw
    have hqG : ((⟨(q' : G), Subgroup.mem_sup_left q'.2⟩ : ↥(y7bBM c.s)) : G) =
        n * ((⟨(q : G), Subgroup.mem_sup_left q.2⟩ : ↥(y7bBM c.s)) : G) * n⁻¹ := by
      simpa only [Subtype.coe_mk] using hq
    have hθw : θ (Subgroup.inclusion hM7X7 w) =
        QuotientGroup.mk (⟨(q : G), Subgroup.mem_sup_left q.2⟩ : ↥(y7bBM c.s)) := by
      have h1 : ι (f w) = ι (QuotientGroup.mk q) := congrArg ι h
      rw [hfw, MulEquiv.apply_symm_apply, hι q] at h1
      exact h1
    have hθw' := hθ2 n hn (Subgroup.inclusion hM7X7 w) (Subgroup.inclusion hM7X7 w') hwG
      (⟨(q : G), Subgroup.mem_sup_left q.2⟩ : ↥(y7bBM c.s))
      (⟨(q' : G), Subgroup.mem_sup_left q'.2⟩ : ↥(y7bBM c.s)) hqG hθw
    rw [hfw, hθw', ← hι q', MulEquiv.symm_apply_apply]

end CFSG.OddStandard.HigherRank.YamadaG23
