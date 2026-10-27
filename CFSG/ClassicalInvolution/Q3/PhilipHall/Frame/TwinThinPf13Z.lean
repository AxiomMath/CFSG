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

@[expose] def Zset (P : Set (Subgroup G)) : Set G := {u | ∃ L ∈ P, IsUniqueInvolution L u}

@[expose] def Zgrp (P : Set (Subgroup G)) : Subgroup G := Subgroup.closure (Zset P)

@[expose] def Dz (K : Subgroup G) (π : Set (Subgroup G)) (g : G) : Subgroup G :=
  Subgroup.closure ((Zgrp π : Set G) ∪ (Zgrp (fam K (conjSub g (piGen π))) : Set G))

theorem closure_comm_of_comm (S0 : Set G) (h : ∀ s ∈ S0, ∀ t ∈ S0, s * t = t * s) :
    ∀ a ∈ Subgroup.closure S0, ∀ b ∈ Subgroup.closure S0, a * b = b * a := by
  have step1 : ∀ s ∈ S0, ∀ b ∈ Subgroup.closure S0, b * s = s * b := by
    intro s hs b hb
    have hle : Subgroup.closure S0 ≤ Subgroup.centralizer {s} := by
      refine (Subgroup.closure_le _).mpr ?_
      intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h t ht s hs)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  intro a ha b hb
  have hle : Subgroup.closure S0 ≤ Subgroup.centralizer {b} := by
    refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mpr (step1 t ht b hb).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

theorem Zgrp_conj_mem {P : Set (Subgroup G)} {x : G} (hx : ∀ L ∈ P, conjSub x L ∈ P) {d : G}
    (hd : d ∈ Zgrp P) : x * d * x⁻¹ ∈ Zgrp P := by
  induction hd using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨L, hL, hu⟩ := ht
    exact Subgroup.subset_closure ⟨conjSub x L, hx L hL, hu.conj x⟩
  | one => simpa using (Zgrp P).one_mem
  | mul a b ha hb iha ihb =>
    have := (Zgrp P).mul_mem iha ihb
    simpa [mul_assoc] using this
  | inv a ha iha =>
    have := (Zgrp P).inv_mem iha
    simpa [mul_assoc] using this

@[expose] def ThinCross (K : Subgroup G) (π : Set (Subgroup G)) (g : G) : Prop :=
  (∀ e ∈ Zgrp π, ∀ e' ∈ Zgrp (fam K (conjSub g (piGen π))), e * e' = e' * e) ∧
  (∀ x ∈ piGen π, ∀ e' ∈ Zgrp (fam K (conjSub g (piGen π))), x * e' * x⁻¹ ∈ Dz K π g) ∧
  (∀ x ∈ conjSub g (piGen π), ∀ e ∈ Zgrp π, x * e * x⁻¹ ∈ Dz K π g)

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem z_mem_Zset : z ∈ Zset (fam K (conjSub g (piGen π))) := ⟨K, S.mem_fam_self, S.hz⟩

theorem Dz_normal (hc : ThinCross K π g) :
    ∀ h : G, ∀ d ∈ Dz K π g, h * d * h⁻¹ ∈ Dz K π g := by
  have hgen := (graph_17_10 S.hos.graph S.hK S.hπ).generate (iSup_conjClass_eq_top S.hs.gen) g S.hg
  have hXn : ∀ x ∈ piGen π, ∀ d ∈ Dz K π g, x * d * x⁻¹ ∈ Dz K π g := by
    intro x hx d hd
    induction hd using Subgroup.closure_induction with
    | mem t ht =>
      rcases ht with ht | ht
      · refine Subgroup.subset_closure (Or.inl ?_)
        exact Zgrp_conj_mem (fun L hL => stable_of_maxOrb S.hos.graph S.hπ x hx L hL) ht
      · exact hc.2.1 x hx t ht
    | one => simpa using (Dz K π g).one_mem
    | mul a b ha hb iha ihb =>
      have := (Dz K π g).mul_mem iha ihb
      simpa [mul_assoc] using this
    | inv a ha iha =>
      have := (Dz K π g).inv_mem iha
      simpa [mul_assoc] using this
  have hXgn : ∀ x ∈ conjSub g (piGen π), ∀ d ∈ Dz K π g, x * d * x⁻¹ ∈ Dz K π g := by
    intro x hx d hd
    induction hd using Subgroup.closure_induction with
    | mem t ht =>
      rcases ht with ht | ht
      · exact hc.2.2 x hx t ht
      · refine Subgroup.subset_closure (Or.inr ?_)
        exact Zgrp_conj_mem (fun L hL => fam_inv L hL x hx) ht
    | one => simpa using (Dz K π g).one_mem
    | mul a b ha hb iha ihb =>
      have := (Dz K π g).mul_mem iha ihb
      simpa [mul_assoc] using this
    | inv a ha iha =>
      have := (Dz K π g).inv_mem iha
      simpa [mul_assoc] using this
  have hnorm : ∀ M : Subgroup G, (∀ x ∈ M, ∀ d ∈ Dz K π g, x * d * x⁻¹ ∈ Dz K π g) →
      M ≤ Subgroup.normalizer (Dz K π g : Set G) := by
    intro M hM x hx
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · exact fun hd => hM x hx d hd
    · intro hd
      have := hM x⁻¹ (M.inv_mem hx) _ hd
      simpa [mul_assoc] using this
  have hle : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤ Subgroup.normalizer (Dz K π g : Set G) := by
    refine iSup₂_le fun M hM => ?_
    rcases hM with hM | ⟨M0, hM0, rfl⟩
    · exact (le_piGen hM).trans (hnorm _ hXn)
    · have : conjSub g M0 ≤ conjSub g (piGen π) := conjSub_mono (le_piGen hM0)
      exact this.trans (hnorm _ hXgn)
  rw [hgen] at hle
  intro h d hd
  exact (Subgroup.mem_normalizer_iff.mp (hle (Subgroup.mem_top h)) d).mp hd

theorem thinTail_of_cross (hc : ThinCross K π g)
    (hab : ∀ a ∈ Zgrp (fam K (conjSub g (piGen π))), ∀ b ∈ Zgrp (fam K (conjSub g (piGen π))),
      a * b = b * a)
    (hab0 : ∀ a ∈ Zgrp π, ∀ b ∈ Zgrp π, a * b = b * a) (h : G) :
    z * (h * z * h⁻¹) = (h * z * h⁻¹) * z := by
  have hz : z ∈ Dz K π g :=
    Subgroup.subset_closure (Or.inr (Subgroup.subset_closure (S.z_mem_Zset)))
  have hcomm : ∀ a ∈ Dz K π g, ∀ b ∈ Dz K π g, a * b = b * a := by
    refine closure_comm_of_comm _ ?_
    rintro s (hs | hs) t (ht | ht)
    · exact hab0 s hs t ht
    · exact hc.1 s hs t ht
    · exact (hc.1 t ht s hs).symm
    · exact hab s hs t ht
  exact hcomm z hz _ (S.Dz_normal hc h z hz)

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
