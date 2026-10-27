module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

open Polynomial Module CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.OrthogonalInvolutions

theorem spSupported_q2_le_om8 {t : StatedSp 4 (ZMod 2)} (ht3 : t ^ 3 = 1)
    (htΩ : t ∈ OmInSp CFSG.AGLEmbedding.Om8) :
    spSupported t {q2} ≤ OmInSp CFSG.AGLEmbedding.Om8 := by
  intro g hg
  rw [mem_OmInSp]
  refine (mem_Om8_iff_omegaGroup (g : SpGL)).mpr ?_
  obtain ⟨hcomm, hfix⟩ := (mem_spSupported_q2_iff ht3).1 hg
  have htO : toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (t : SpGL) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q8 :=
    elementaryGroup_le_orthogonalGroup Q8
      ((CFSG.AGLEmbedding.mem_Om8_iff (t : SpGL)).1 (mem_OmInSp.mp htΩ))
  have htQ : ∀ w, Q8 (spEnd t w) = Q8 w := by
    intro w
    have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp htO w
    rwa [toLinEquiv_apply] at h
  have huni : ∀ u v, spForm 4 (ZMod 2) (spEnd g u) (spEnd g v) = spForm 4 (ZMod 2) u v :=
    fun u v => mem_sesqUnitaryGroup.mp (spLin_mem g) u v
  have hcommE : Commute (spEnd g) (spEnd t) := by
    have h := congrArg (spLin 4 (ZMod 2)) hcomm
    rw [map_mul, map_mul] at h
    exact congrArg Units.val h
  have hgT : ∀ v, spEnd g (spEnd t v) = spEnd t (spEnd g v) := by
    intro v
    have h := congrArg
      (fun e : Module.End (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) => e v) hcommE.eq
    simpa [Module.End.mul_apply] using h
  let f : (Fin 4 ⊕ Fin 4 → ZMod 2) →+ ZMod 2 :=
    { toFun := fun v => Q8 (spEnd g v) + Q8 v
      map_zero' := by simp
      map_add' := fun u v => by
        have hP : spForm 4 (ZMod 2) u v + spForm 4 (ZMod 2) u v = 0 :=
          CharTwo.add_self_eq_zero _
        have h1 : Q8 (spEnd g u + spEnd g v) =
            Q8 (spEnd g u) + Q8 (spEnd g v) + spForm 4 (ZMod 2) u v := by
          rw [QuadraticMap.map_add Q8 (spEnd g u) (spEnd g v), polar_Q8, huni u v]
        have h2 : Q8 (u + v) = Q8 u + Q8 v + spForm 4 (ZMod 2) u v := by
          rw [QuadraticMap.map_add Q8 u v, polar_Q8]
        rw [map_add, h1, h2]
        linear_combination hP }
  have hf_t : ∀ v, f (spEnd t v) = f v := by
    intro v
    show Q8 (spEnd g (spEnd t v)) + Q8 (spEnd t v) = Q8 (spEnd g v) + Q8 v
    rw [hgT v, htQ (spEnd g v), htQ v]
  have hf_range : ∀ v ∈ LinearMap.range (spEnd t - 1), f v = 0 := by
    rintro v ⟨w, rfl⟩
    have h1 : (spEnd t - 1) w = spEnd t w - w := rfl
    rw [h1, map_sub, hf_t w]
    exact sub_self _
  have hf_fix : ∀ v ∈ fixV t, f v = 0 := by
    intro v hv
    show Q8 (spEnd g v) + Q8 v = 0
    rw [hfix v hv]
    exact CharTwo.add_self_eq_zero (Q8 v)
  have hf_eq : ∀ v, f v = 0 := by
    intro v
    have htop : fixV t ⊔ LinearMap.range (spEnd t - 1) = ⊤ := by
      rw [eq_top_iff, ← fixV_sup_movV ht3]
      exact sup_le_sup_left (movV_le_range ht3) _
    have hv : v ∈ fixV t ⊔ LinearMap.range (spEnd t - 1) := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    rw [← hab, map_add, hf_fix a ha, hf_range b hb, add_zero]
  have hO : toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q8 := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have h := hf_eq v
    have h2 : Q8 (spEnd g v) = - Q8 v := eq_neg_of_add_eq_zero_left h
    rw [neg_eq_self_of_two_eq_zero (K := ZMod 2) (by decide)] at h2
    rw [toLinEquiv_apply]
    exact h2
  have hWle : LinearMap.range (spEnd g - 1) ≤ movV t := by
    rintro w ⟨v, rfl⟩
    have htop : fixV t ⊔ movV t = ⊤ := fixV_sup_movV ht3
    have hv : v ∈ fixV t ⊔ movV t := by rw [htop]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    rw [← hab]
    have hga : spEnd g a = a := hfix a ha
    have hgb : spEnd g b ∈ movV t := apply_mem_movV_of_commute hcomm hb
    have hcalc : (spEnd g - 1) (a + b) = spEnd g b - b := by
      rw [LinearMap.sub_apply, Module.End.one_apply, map_add, hga]
      abel
    rw [hcalc]
    exact Submodule.sub_mem (movV t) hgb hb
  have hinv : ∀ w ∈ LinearMap.range (spEnd g - 1), spEnd t w ∈ LinearMap.range (spEnd g - 1) := by
    rintro w ⟨v, rfl⟩
    refine ⟨spEnd t v, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, hgT v]
  have heven : Even (Module.finrank (ZMod 2) (LinearMap.range (spEnd g - 1))) :=
    even_finrank_of_le_movV hWle hinv
  have hcomm_eq : commSpace (toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL)) =
      LinearMap.range (spEnd g - 1) := rfl
  exact ⟨hO, by rw [hcomm_eq]; exact heven⟩

end CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

end
