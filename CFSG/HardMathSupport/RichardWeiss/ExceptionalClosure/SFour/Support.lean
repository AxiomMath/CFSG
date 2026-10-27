module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderAlt

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem ewp_sub_eq_zero_of_free_point {d : ℕ} (f c : Perm (Fin d))
    (T Γ : Finset (Fin d)) (hfree : ∃ i, i ∉ T ∧ i ∉ Γ) (hdis : Disjoint T Γ)
    (hc : ∀ x ∉ T, c x = x) (hf : ∀ x ∉ Γ, f x = x) (x y : evenWeight d)
    (h : (evenWeightPerm f y - y) - (evenWeightPerm c x - x) ∈ evenWeightOnes d) :
    evenWeightPerm f y - y = 0 := by
  classical
  obtain ⟨c0, hc0⟩ := (mem_evenWeightOnes_iff d _).1 h
  have hcoord : ∀ (σ : Perm (Fin d)) (z : evenWeight d) (i : Fin d),
      ((evenWeightPerm σ z - z : evenWeight d) : Fin d → ZMod 2) i =
        (z : Fin d → ZMod 2) (σ⁻¹ i) - (z : Fin d → ZMod 2) i := fun σ z i => rfl
  have hinv : ∀ (σ : Perm (Fin d)) (i : Fin d), σ i = i → σ⁻¹ i = i := fun σ i hi =>
    (Equiv.symm_apply_eq σ).2 hi.symm
  obtain ⟨i0, hi0T, hi0Γ⟩ := hfree
  have hi0 : i0 ∉ T ∧ i0 ∉ Γ := ⟨hi0T, hi0Γ⟩
  have hcz : c0 = 0 := by
    have h1 := hc0 i0
    have h2 : ((evenWeightPerm f y - y) - (evenWeightPerm c x - x) : evenWeight d) =
      (evenWeightPerm f y - y) - (evenWeightPerm c x - x) := rfl
    have h3 : (((evenWeightPerm f y - y) - (evenWeightPerm c x - x) : evenWeight d) :
        Fin d → ZMod 2) i0 =
      ((evenWeightPerm f y - y : evenWeight d) : Fin d → ZMod 2) i0 -
        ((evenWeightPerm c x - x : evenWeight d) : Fin d → ZMod 2) i0 := rfl
    rw [h3, hcoord, hcoord, hinv f i0 (hf i0 hi0.2), hinv c i0 (hc i0 hi0.1)] at h1
    simpa using h1.symm
  subst hcz
  apply Subtype.ext
  funext i
  have h1 := hc0 i
  have h3 : (((evenWeightPerm f y - y) - (evenWeightPerm c x - x) : evenWeight d) :
        Fin d → ZMod 2) i =
      ((evenWeightPerm f y - y : evenWeight d) : Fin d → ZMod 2) i -
        ((evenWeightPerm c x - x : evenWeight d) : Fin d → ZMod 2) i := rfl
  rw [h3] at h1
  by_cases hiΓ : i ∈ Γ
  · have hiT : i ∉ T := fun hT' => Finset.disjoint_left.1 hdis hT' hiΓ
    have : ((evenWeightPerm c x - x : evenWeight d) : Fin d → ZMod 2) i = 0 := by
      rw [hcoord, hinv c i (hc i hiT)]; simp
    have h4 : ∀ a b : ZMod 2, a - b = 0 → b = 0 → a = 0 := fun a b h hb =>
      (sub_eq_zero.1 h).trans hb
    exact h4 _ _ h1 this
  · rw [hcoord, hinv f i (hf i hiΓ)]
    simp

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
