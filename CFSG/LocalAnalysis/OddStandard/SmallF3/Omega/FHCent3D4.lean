module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHCent3D4Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddAsm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp
import CFSG.GH74.Generic.Front.Sch
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Main


theorem asc82FactCent3D4_holds : Asc82FactCent3D4 := by
  intro A _ _ H hH hC hL a ha g hg3 hga hgH hall
  haveI : H.Normal := hH
  have hsimple : IsSimpleGroup ↥H :=
    (l34g_simple_of_simpleFStar (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))))).1
  have ha2 : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha, pow_two] at h
  have hg3' : g ^ 3 = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hg3] at h
  have hf2 : (MulAut.conjNormal a : MulAut ↥H) * MulAut.conjNormal a = 1 := by
    rw [← map_mul, ha2, map_one]
  have hβodd : Odd (orderOf (MulAut.conjNormal g : MulAut ↥H)) := by
    have h3 : (MulAut.conjNormal g : MulAut ↥H) ^ 3 = 1 := by
      rw [← map_pow, hg3', map_one]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
  have hfix : ∀ x : ↥H, (MulAut.conjNormal a : MulAut ↥H) x = x → Odd (orderOf x) →
      (MulAut.conjNormal g : MulAut ↥H) x = x := by
    intro x hfx hxodd
    have hxa : a * (x : A) * a⁻¹ = x := by
      simpa [MulAut.conjNormal_apply] using congrArg Subtype.val hfx
    have hxc : (x : A) ∈ H ⊓ centralizer ({a} : Set A) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 (by
        calc (x : A) * a = a * x * a⁻¹ * a := by rw [hxa]
          _ = a * x := by group)⟩
    have hcomm : g * (x : A) = x * g := hall (x : A) hxc (by rwa [Subgroup.orderOf_coe])
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc g * (x : A) * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
      _ = x := by group
  obtain ⟨s, hs⟩ := fh_d4OddCent_of fh_simFamO_one_one fh_simFamO_one_neg_one
    fh_simFamO_neg_one_one fh_simFamO_neg_one_neg_one ↥H hsimple hL _ hf2 _ hβodd hfix
  exact hgH (CFSG.GH74.Generic.mem_of_conjNormal_inner (by rw [hC]; exact bot_le) hs.symm)

end Main

end CFSG.OddStandard.SmallF3.Omega
